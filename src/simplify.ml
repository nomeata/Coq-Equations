open Pp

(* ========== Coq references ========= *)
(* This section should change a lot when we approach an actual solution. *)


type constr_gen = Evd.evar_map ref -> Term.constr

module type SIGMAREFS =
  sig
    val sigma : constr_gen
    val sigmaI : constr_gen
  end

module type COQREFS =
  sig
    (* Equality type. *)
    val eq : constr_gen
    val eq_refl : constr_gen
    (* Decidable equality typeclass. *)
    val eq_dec : constr_gen
    (* Simplification of dependent pairs. *)
    val simpl_sigma : constr_gen
    val simpl_sigma_dep : constr_gen
    val simpl_sigma_dep_dep : constr_gen
    (* Deletion using K. *)
    val simpl_K : constr_gen
    val simpl_K_dec : constr_gen
    (* Solution lemmas. *)
    val solution_left : constr_gen
    val solution_left_dep : constr_gen
    val solution_right : constr_gen
    val solution_right_dep : constr_gen
  end

module RefsHelper = struct
  open Coqlib

  let gen_from_ref ref = fun evd ->
    let glob = Lazy.force ref in
      Evarutil.e_new_global evd glob

  let init_reference = Coqlib.find_reference "Equations.Simplify"
  let load_ref dir s = gen_from_ref (lazy (init_reference dir s))
end

(* This should be parametrizable by the user. *)
module CoqRefs : COQREFS = struct
  include RefsHelper

  let load_depelim s = load_ref ["Equations"; "DepElim"] s

  let eq = gen_from_ref (Lazy.from_fun Coqlib.build_coq_eq)
  let eq_refl = gen_from_ref (Lazy.from_fun Coqlib.build_coq_eq_refl)
  let eq_dec = load_ref ["Equations"; "EqDec"] "EqDec"
  let simpl_sigma = load_depelim "eq_simplification_sigma1"
  let simpl_sigma_dep = load_depelim "eq_simplification_sigma1_dep"
  let simpl_sigma_dep_dep = load_depelim "eq_simplification_sigma1_dep_dep"
  let simpl_K = load_depelim "simplification_K"
  let simpl_K_dec = load_depelim "simplification_K_dec"
  let solution_left = load_depelim "solution_left"
  let solution_left_dep = load_depelim "solution_left_dep"
  let solution_right = load_depelim "solution_right"
  let solution_right_dep = load_depelim "solution_right_dep"
end

(* This should not. *)
module SigmaRefs : SIGMAREFS = struct
  include RefsHelper

  let sigma = load_ref ["Equations"; "Init"] "sigma"
  let sigmaI = load_ref ["Equations"; "Init"] "sigmaI"
end


(* ========== Simplification ========== *)

(* Some types to define what is a simplification. *)
type direction = Left | Right

type simplification_step =
    Deletion of bool (* Force the use of K? *)
  | Solution of direction option (* None = infer it *)
  | NoConfusion
  | NoCycle

(* None = infer it. *)
type simplification_rules = (Loc.t * simplification_step option) list

type goal = Context.rel_context * Term.types

type open_term = Term.constr -> Term.constr
type open_term_with_context = goal * open_term

exception CannotSimplify of Pp.std_ppcmds

type pre_simplification_fun =
  Environ.env -> Evd.evar_map ref -> goal -> open_term

type simplification_fun =
  Environ.env -> Evd.evar_map ref -> goal -> open_term_with_context

(* Auxiliary functions. *)

(* Return a substitution (and its inverse) which is just a permutation
 * of the variables in the context which is well-typed, and such that
 * all variables in [t] (and their own dependencies) are now declared
 * before [x] in the context. *)
let strengthen (env : Environ.env) (evd : Evd.evar_map) (ctx : Context.rel_context)
  (x : int) ?(rels : Int.Set.t = Covering.rels_above ctx x) (t : Term.constr) :
    Covering.context_map * Covering.context_map =
  let rels = Int.Set.union rels (Covering.dependencies_of_term env evd ctx t x) in
  let maybe_reduce k t =
    if Int.Set.mem k (Termops.free_rels t) then
      Reductionops.nf_betadeltaiota env evd t
    else t
  in
  (* We may have to normalize some declarations in the context if they
   * mention [x] syntactically when they shouldn't. *)
  let ctx = CList.map_i (fun k decl ->
    if Int.Set.mem k rels && k < x then
      Context.map_rel_declaration (maybe_reduce (x - k)) decl
    else decl) 1 ctx in
  (* Now we want to put everything in [rels] as the oldest part of the context,
   * and everything else after. The invariant is that the context
   * [subst (rev (before @ after)) @ ctx] is well-typed. *)
  (* We also create along what we need to build the actual substitution. *)
  let len_ctx = Context.rel_context_length ctx in
  let lifting = len_ctx - Int.Set.cardinal rels in
  let rev_subst = Array.make len_ctx (Covering.PRel 0) in
  let rec aux k before after n subst = function
  | decl :: ctx ->
      if Int.Set.mem k rels then
        let subst = Covering.PRel (k + lifting - n + 1) :: subst in
        rev_subst.(k + lifting - n) <- Covering.PRel k;
        (* We lift the declaration not to be well-typed in the new context,
         * but so that it reflects in a raw way its movement in the context.
         * This allows to apply a simple substitution afterwards, instead
         * of going through the whole context at each step. *)
        let decl = Context.map_rel_declaration (Vars.lift (n - lifting - 1)) decl in
        aux (succ k) (decl :: before) after n subst ctx
      else
        let subst = Covering.PRel n :: subst in
        rev_subst.(n - 1) <- Covering.PRel k;
        let decl = Context.map_rel_declaration (Vars.lift (k - n)) decl in
        aux (succ k) before (decl :: after) (succ n) subst ctx
  | [] -> CList.rev (before @ after), CList.rev subst
  in
  (* Now [subst] is a list of indices which represents the substitution
   * that we must apply. *)
  (* Right now, [ctx'] is an ill-typed rel_context, we need to apply [subst]. *)
  let (ctx', subst) = aux 1 [] [] 1 [] ctx in
  let rev_subst = Array.to_list rev_subst in
  (* Fix the context [ctx'] by using [subst]. *)
  (* We lift each declaration to make it appear as if it was under the
   * whole context, which allows then to apply the substitution, and lift
   * it back to its place. *)
  let do_subst k c = Vars.lift (-k)
    (Covering.specialize_constr subst (Vars.lift k c)) in
  let ctx' = CList.map_i (fun k decl ->
    Context.map_rel_declaration (do_subst k) decl) 1 ctx' in
  (* Now we have everything need to build the two substitutions. *)
  let s = Covering.mk_ctx_map evd ctx' subst ctx in
  let rev_s = Covering.mk_ctx_map evd ctx rev_subst ctx' in
    s, rev_s

(* Infer the context and the type of the hole in the term returned by a
 * simplification function. It is assumed there is exactly one hole. *)
let infer_hole_type (env : Environ.env) (evd : Evd.evar_map ref)
  ((ctx, ty) : goal) (ctx' : Context.rel_context)
  (term : open_term) : Term.types =
  (* We just want to create temporary evars. *)
  let evd = ref !evd in
  let ev_ty, tev =
    let env = Environ.push_rel_context ctx' env in
    let ev_ty, _ = Evarutil.e_new_type_evar env evd Evd.univ_flexible_alg in
    let tev = Evarutil.e_new_evar env evd ev_ty in
      ev_ty, tev
  in
  let () = let env = Environ.push_rel_context ctx env in
    Typing.check env evd (term tev) ty in
  let ty = Evd.existential_value !evd (Term.destEvar ev_ty) in
    ty

let infer_hole_context (env : Environ.env) (evd : Evd.evar_map ref)
  ((ctx, ty) : goal) (term : open_term) : Context.rel_context =
  (* Determine the context of the hole. *)
  let ctx' = ref ctx in
  let hole = Term.mkRel 0 in
  let c = term hole in
  (* Collect the context above the hole. *)
  let rec aux (ctx : Context.rel_context) (c : Term.constr) =
    if Constr.equal c hole then ctx' := ctx
    else Termops.iter_constr_with_full_binders Context.add_rel_decl aux ctx c
  in aux ctx c; !ctx'

let infer_hole (f : pre_simplification_fun) (env : Environ.env) (evd : Evd.evar_map ref)
  (gl : goal) : open_term_with_context =
  let term = f env evd gl in
  let ctx' = infer_hole_context env evd gl term in
  let ty = infer_hole_type env evd gl ctx' term in
    (ctx', ty), term

(* Add a typing check. *)
let safe_term (env : Environ.env) (evd : Evd.evar_map ref)
  (((ctx, ty), f) : open_term_with_context) : open_term_with_context =
  (ctx, ty), fun c ->
    let () =
      let env = Environ.push_rel_context ctx env in
        Typing.check env evd c ty
    in f c

(* Build an open term by substituting the second term for the hole in the
 * first term. *)
let compose_term
  ((_, f1) : open_term_with_context)
  ((gl2, f2) : open_term_with_context) : open_term_with_context =
  gl2, fun c -> f1 (f2 c)

let safe_fun (f : simplification_fun)
  (env : Environ.env) (evd : Evd.evar_map ref) (gl : goal) : open_term_with_context =
    safe_term env evd (f env evd gl)

(* Applies [g] to the goal, then [f]. *)
let compose_fun (f : simplification_fun) (g : simplification_fun)
  (env : Environ.env) (evd : Evd.evar_map ref) (gl : goal) : open_term_with_context =
  let (gl, _) as term1 = g env evd gl in
  let term2 = f env evd gl in
    compose_term term1 term2

(* Check that the first hypothesis in the goal is an equality, and some
 * additional constraints if specified. Raise CannotSimplify if it's
 * not the case. Otherwise, return the goal decomposed in two types,
 * the Name of the equality, its arguments. *)
let check_equality ?(equal_terms : bool = false)
  ?(var_left : bool = false) ?(var_right : bool = false)
  (env : Environ.env) (evd : Evd.evar_map ref) (ty : Term.types) :
    ((Names.name * Term.types * Term.types) *
     (Term.types * Term.constr * Term.constr)) =
  try
    let name, ty1, ty2 = Term.destProd ty in
    let ind, args = Term.decompose_appvect ty1 in
    if not (Constr.equal ind (CoqRefs.eq evd)) then
      raise (CannotSimplify (str
        "The first hypothesis in the goal is not an equality."));
    let tA = args.(0) in
    let tx, ty = args.(1), args.(2) in
    if equal_terms && not (Constr.equal tx ty) then
      raise (CannotSimplify (str
        "The first hypothesis in the goal is not an equality
         between identical terms."));
    if var_left && not (Term.isRel tx) then
      raise (CannotSimplify (str
        "The left-hand side of the first hypothesis in the goal is
         not a variable."));
    if var_right && not (Term.isRel ty) then
      raise (CannotSimplify (str
        "The right-hand side of the first hypothesis in the goal is
         not a variable."));
    (name, ty1, ty2), (tA, tx, ty)
  with
  | Term.DestKO -> raise (CannotSimplify (str "The goal is not a product."))

let decompose_sigma (env : Environ.env) (evd : Evd.evar_map ref)
  (t : Term.constr) : (Term.types * Term.constr * Term.constr * Term.constr) option =
  try
    let f, args = Term.destApp t in
    (* FIXME: with a better definition of SigmaRefs.sigmaI, we shouldn't have
     * to instantiate anything... *)
    if not (Term.eq_constr_nounivs f (SigmaRefs.sigmaI evd)) then None
    else Some (args.(0), args.(1), args.(2), args.(3))
  with
  | Term.DestKO -> None

(* Simplification functions to handle each step. *)
(* Any of these can throw a CannotSimplify exception which explains why the
 * rule cannot apply. *)

(* This function is not accessible by the user for now. It is used to project
 * (if needed) the first component of an equality between sigmas. It will not
 * do anything if it fails, unless the first hypothesis in the goal is not
 * even an equality. *)
let remove_sigma (env : Environ.env) (evd : Evd.evar_map ref)
  ((ctx, ty) : goal) : open_term =
  let (name, ty1, ty2), (_, t1, t2) = check_equality env evd ty in
  match decompose_sigma env evd t1, decompose_sigma env evd t2 with
  | Some (tA, tB, tt, tp), Some (_, _, tu, tq) ->
      (* Determine the degree of dependency. *)
      if Vars.noccurn 1 ty2 then begin
        (* No dependency in the goal, but maybe there is a dependency in
           the pair itself. *)
        try
          let name', _, tBbody = Term.destLambda tB in
          if Vars.noccurn 1 tBbody then
            (* No dependency whatsoever. *)
            let tsimpl_sigma = CoqRefs.simpl_sigma evd in
            let tP = Termops.pop tBbody in
            let tB = Termops.pop ty2 in
            fun c -> Constr.mkApp
              (tsimpl_sigma, [| tA; tP; tB; tt; tu; tp; tq; c |])
          else raise Term.DestKO
        with
        | Term.DestKO ->
            (* Dependency in the pair, but not in the goal. *)
            let tsimpl_sigma = CoqRefs.simpl_sigma_dep evd in
            let tP = tB in
            let tB = Termops.pop ty2 in
            fun c -> Constr.mkApp
              (tsimpl_sigma, [| tA; tP; tB; tt; tu; tp; tq; c |])
      end else
        (* We assume full dependency. We could add one more special case,
         * but we don't for now. *)
        let tsimpl_sigma = CoqRefs.simpl_sigma_dep_dep evd in
        let tP = tB in
        let tB = Constr.mkLambda (name, ty1, ty2) in
        fun c -> Constr.mkApp
          (tsimpl_sigma, [| tA; tP; tt; tu; tp; tq; tB; c |])
  | _, _ -> fun c -> c
let remove_sigma = infer_hole remove_sigma

let deletion ~(force:bool) (env : Environ.env) (evd : Evd.evar_map ref)
  ((ctx, ty) : goal) : open_term =
  let (name, ty1, ty2), (tA, tx, _) =
    check_equality ~equal_terms:true env evd ty in
  if Vars.noccurn 1 ty2 then
    (* The goal does not depend on the equality, we can just eliminate it. *)
    fun c -> Constr.mkLambda (name, ty1, Vars.lift 1 c)
  else
    let tB = Constr.mkLambda (name, ty1, ty2) in
    if force then
      (* The user wants to use K directly. *)
      let tsimpl_K = CoqRefs.simpl_K evd in
      fun c ->
        Constr.mkApp (tsimpl_K, [| tA; tx; tB; c |])
    else
      (* We will try to find an instance of K for the type [A]. *)
      let tsimpl_K_dec = CoqRefs.simpl_K_dec evd in
      let eqdec_ty = Constr.mkApp (CoqRefs.eq_dec evd, [| tA |]) in
      let tdec =
        let env = Environ.push_rel_context ctx env in
        try
          Evarutil.evd_comb1
            (Typeclasses.resolve_one_typeclass env) evd eqdec_ty
        with Not_found ->
          raise (CannotSimplify (str
            "[deletion] Cannot simplify without K on type " ++
            Printer.pr_constr_env env !evd tA))
      in fun c ->
          Constr.mkApp (tsimpl_K_dec, [| tA; tdec; tx; tB; c |])
let deletion ~force = infer_hole (deletion ~force)

let solution ~(dir:direction) (env : Environ.env) (evd : Evd.evar_map ref)
  ((ctx, ty) as gl : goal) : open_term_with_context =
  let var_left = match dir with Left -> true | Right -> false in
  let var_right = not var_left in
  let (name, ty1, ty2), (tA, tx, tz) =
    check_equality ~var_left ~var_right env evd ty in
  let trel, term =
    if var_left then tx, tz
    else tz, tx
  in
  let rel = Term.destRel trel in
  if Int.Set.mem rel (Covering.dependencies_of_term env !evd ctx term rel) then
   raise (CannotSimplify (str
    "[solution] The variable appears on both sides of the equality.")); 
  let (ctx', _, _) as subst, rev_subst = strengthen env !evd ctx rel term in
  let trel' = Covering.mapping_constr subst trel in
  let rel' = Term.destRel trel' in
  let term' = Covering.mapping_constr subst term in
  let tA' = Covering.mapping_constr subst tA in
  let ty1' = Covering.mapping_constr subst ty1 in
  (* We will have to generalize everything after [x'] in the new
   * context. *)
  let after', (name', _, _), before' = Covering.split_context (pred rel') ctx' in
  (* let after, _, before = Covering.split_context rel ctx in*)
  
  (* Select the correct solution lemma. *)
  let nondep = Vars.noccurn 1 ty2 in
  let tsolution = begin match var_left, nondep with
  | false, false -> CoqRefs.solution_right_dep
  | false, true -> CoqRefs.solution_right
  | true, false -> CoqRefs.solution_left_dep
  | true, true -> CoqRefs.solution_left end evd
  in
  let tB' =
    let body = Covering.mapping_constr subst ty in
    (* Right now, [body] has an equality at the head that we want
     * to move, in some sense. *)
    let _, _, body = Term.destProd body in
    if nondep then
      let body = Termops.pop body in
      let body = Term.it_mkProd_or_LetIn body after' in
        (* [body] is a term in the context [decl' :: before'],
         * whereas [tA'] lives in [ctx']. *)
        Constr.mkLambda (name', Vars.lift (-rel') tA', body)
    else
      (* We make some room for the equality. *)
      let body = Vars.liftn 1 (succ rel') body in
      let body = Vars.subst1 (Constr.mkRel rel') body in
      let after' = Termops.lift_rel_context 1 after' in
      let body = Term.it_mkProd_or_LetIn body after' in
      let body = Constr.mkLambda (name, Vars.lift (1-rel') ty1', body) in
        Constr.mkLambda (name', Vars.lift (-rel') tA', body)
  in
  (* [tB'] is a term in the context [before']. We want it in [ctx']. *)
  let tB' = Vars.lift rel' tB' in
  let targs' = Termops.extended_rel_vect 1 after' in
  (* [ctx''] is just [ctx'] where we replaced the substituted variable. *)
  let ctx'' = Covering.subst_in_ctx rel' term' ctx' in
  let after'', _ = CList.chop (pred rel') ctx'' in
  let res = fun c ->
      (* [c] is a term in the context [ctx'']. *)
      let c = Term.it_mkLambda_or_LetIn c after'' in
      (* [c] is a term in the context [before']. *)
      let c = Vars.lift rel' c in
      (* [c] is a term in the context [ctx']. *)
      let c =
        if nondep then
          Constr.mkApp (tsolution, [| tA'; tB'; term'; c; trel' |])
        else
          Constr.mkApp (tsolution, [| tA'; term'; tB'; c; trel' |])
      in
      (* We make some room for the application of the equality... *)
      let c = Vars.lift 1 c in
      let c = Constr.mkApp (c, [| Constr.mkRel 1 |]) in
      (* [targs'] are arguments in the context [eq_decl :: ctx']. *)
      let c = Constr.mkApp (c, targs') in
      (* [ty1'] is the type of the equality in [ctx']. *)
      let c = Constr.mkLambda (name, ty1', c) in
      (* And now we recover a term in the context [ctx]. *)
        Covering.mapping_constr rev_subst c
  in
  let ty'' = infer_hole_type env evd gl ctx'' res in
    (ctx'', ty''), res

let noConfusion (env : Environ.env) (evd : Evd.evar_map ref)
  ((ctx, ty) : goal) : open_term_with_context =
  failwith "[noConfusion] is not implemented!"

let noCycle (env : Environ.env) (evd : Evd.evar_map ref)
  ((ctx, ty) : goal) : open_term_with_context =
  failwith "[noCycle] is not implemented!"

let identity (env : Environ.env) (evd : Evd.evar_map ref)
  (gl : goal) : open_term_with_context =
  gl, fun c -> c


let deletion ~force = compose_fun (deletion ~force) remove_sigma
let solution ~dir = compose_fun (solution ~dir) remove_sigma

let deletion ~force = safe_fun (deletion ~force)
let solution ~dir = safe_fun (solution ~dir)
let noConfusion = safe_fun noConfusion
let noCycle = safe_fun noCycle
let identity = safe_fun identity


let execute_step : simplification_step -> simplification_fun = function
  | Deletion force -> deletion ~force
  | Solution (Some dir) -> solution ~dir:dir
  | NoConfusion -> noConfusion
  | NoCycle -> noCycle
  (* We assume the direction has been inferred at this point. *)
  | Solution None -> assert false

let infer_step ~isDir:bool (env : Environ.env) (evd : Evd.evar_map ref)
  ((ctx, ty) : goal) : simplification_step =
  failwith "[infer_step] is not implemented!"

let simplify_one_aux : simplification_step option -> simplification_fun = function
  | None -> fun env evd gl ->
      let step = infer_step ~isDir:false env evd gl in
        execute_step step env evd gl
  | Some (Solution None) -> fun env evd gl ->
      let step = infer_step ~isDir:true env evd gl in
        execute_step step env evd gl
  | Some step -> execute_step step

let simplify_one ((loc, rule) : Loc.t * simplification_step option) :
  simplification_fun = fun env evd gl ->
    try simplify_one_aux rule env evd gl
    with CannotSimplify err ->
      Errors.user_err_loc (loc, "Equations.Simplify", err)

let simplify (rules : simplification_rules) : simplification_fun =
  let funs = List.rev_map simplify_one rules in
    List.fold_left compose_fun identity funs

let simplify_tac (rules : simplification_rules) : unit Proofview.tactic =
  Proofview.Goal.enter begin fun gl ->
    let gl = Proofview.Goal.assume gl in
    let env = Environ.reset_context (Proofview.Goal.env gl) in
    let hyps = Proofview.Goal.hyps gl in
    (* We want to work in a [rel_context], not a [named_context]. *)
    let ctx, subst = Covering.rel_of_named_context hyps in
    let rev_subst, _ = Covering.named_of_rel_context ctx in
    let concl = Proofview.Goal.concl gl in
    (* We also need to convert the goal for it to be well-typed in
     * the [rel_context]. *)
    let ty = Vars.subst_vars subst concl in
    (* [ty'] is the expected type of the hole in the term, under the
     * context [ctx']. *)
    Proofview.Refine.refine ~unsafe:false (fun evd ->
      let evd = ref evd in
      let (ctx', ty'), term = simplify rules env evd (ctx, ty) in
      let c = let env = Environ.push_rel_context ctx' env in
          Evarutil.e_new_evar ~principal:true env evd ty'
      in
      let c = term c in
      let c = Vars.substl rev_subst c in
        !evd, c)
  end


(* Printing functions. *)

let pr_simplification_step : simplification_step -> Pp.std_ppcmds = function
  | Deletion false -> str "-"
  | Deletion true -> str "-!"
  | Solution (Some Left) -> str "->"
  | Solution (Some Right) -> str "<-"
  | Solution None -> str "<->"
  | NoConfusion -> str "NoConfusion"
  | NoCycle -> str "NoCycle"

let pr_simplification_rule ((_, rule) : Loc.t * simplification_step option) :
  Pp.std_ppcmds = match rule with
  | None -> str "?"
  | Some step -> pr_simplification_step step

let pr_simplification_rules : simplification_rules -> Pp.std_ppcmds =
  prlist_with_sep spc pr_simplification_rule
