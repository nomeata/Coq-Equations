open Pp

(* ========== Coq references ========= *)
(* This section should change a lot when we approach an actual solution. *)


type constr_gen = Evd.evar_map ref -> Term.constr

module type COQREFS =
  sig
    val eq : constr_gen
    val eq_refl : constr_gen
    val eq_dec : constr_gen
    val simpl_sigma1 : constr_gen
    val simpl_sigma1_dep : constr_gen
    val simpl_sigma1_dep_dep : constr_gen
    val simpl_K : constr_gen
    val simpl_K_dec : constr_gen
  end

module CoqRefs : COQREFS = struct
  open Coqlib

  let gen_from_ref ref = fun evd ->
    let glob = Lazy.force ref in
      Evarutil.e_new_global evd glob

  let init_reference = Coqlib.find_reference "Equations.Simplify"
  let load_ref dir s = gen_from_ref (lazy (init_reference dir s))

  let eq = gen_from_ref (Lazy.from_fun Coqlib.build_coq_eq)
  let eq_refl = gen_from_ref (Lazy.from_fun Coqlib.build_coq_eq_refl)
  let eq_dec = load_ref ["Equations"; "EqDec"] "EqDec"
  let simpl_sigma1 = load_ref ["Equations"; "DepElim"]
    "eq_simplification_sigma1"
  let simpl_sigma1_dep = load_ref ["Equations"; "DepElim"]
    "eq_simplification_sigma1_dep"
  let simpl_sigma1_dep_dep = load_ref ["Equations"; "DepElim"]
    "eq_simplification_sigma1_dep_dep"
  let simpl_K = load_ref ["Equations"; "DepElim"]
    "simplification_K"
  let simpl_K_dec = load_ref ["Equations"; "DepElim"]
    "simplification_K_dec"
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

let strengthen (env : Environ.env) (evd : Evd.evar_map) (ctx : Context.rel_context)
  (x : int) (t : Term.constr) : Covering.context_map * Covering.context_map =
  failwith "[strengthen] is not implemented!"


(* Infer the context and the type of the hole in the term returned by a
 * simplification function. It is assumed there is exactly one hole. *)
let infer_hole (f : pre_simplification_fun) (env : Environ.env) (evd : Evd.evar_map ref)
  ((ctx, ty) as gl : goal) : open_term_with_context =
  let term = f env evd gl in
  (* Now to determine the context of the hole. *)
  let ctx' = ref ctx in
  let hole = Term.mkRel 0 in
  let c = term hole in
  (* Collect the context above the hole. *)
  let rec aux (ctx : Context.rel_context) (c : Term.constr) =
    if Constr.equal c hole then ctx' := ctx
    else Termops.iter_constr_with_full_binders Context.add_rel_decl aux ctx c
  in aux ctx c;
  let ctx' = !ctx' in
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
 * the Name of the equality, and its arguments. *)
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
        "The first hypothesis in the goal is not an equality."))
    else
      let tA = args.(0) in
      let tx, ty = args.(1), args.(2) in
    if equal_terms && not (Constr.equal tx ty) then
      raise (CannotSimplify (str
        "The first hypothesis in the goal is not an equality
         between identical terms."))
    else if var_left && not (Term.isRel tx) then
      raise (CannotSimplify (str
        "The left-hand side of the first hypothesis in the goal is
         not a variable."))
    else if var_right && not (Term.isRel ty) then
      raise (CannotSimplify (str
        "The right-hand side of the first hypothesis in the goal is
         not a variable."))
    else
      (name, ty1, ty2), (tA, tx, ty)
  with
  | Term.DestKO -> raise (CannotSimplify (str "The goal is not a product."))

(* Simplification functions to handle each step. *)
(* Any of these can throw a CannotSimplify exception which explains why the
 * rule cannot apply. *)

let deletion ~(force:bool) (env : Environ.env) (evd : Evd.evar_map ref)
  ((ctx, ty) : goal) : open_term =
  let (name, ty1, ty2), (tA, tx, _) =
    check_equality ~equal_terms:true env evd ty in
  if Vars.noccurn 1 ty2 then
    (* The goal does not depend on the equality, we can just eliminate it. *)
    fun c ->
      Constr.mkLambda (Names.Anonymous, ty1, Vars.lift 1 c)
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

let solution ~dir:direction (env : Environ.env) (evd : Evd.evar_map ref)
  ((ctx, ty) : goal) : open_term_with_context =
  failwith "[solution] is not implemented!"

let noConfusion (env : Environ.env) (evd : Evd.evar_map ref)
  ((ctx, ty) : goal) : open_term_with_context =
  failwith "[noConfusion] is not implemented!"

let noCycle (env : Environ.env) (evd : Evd.evar_map ref)
  ((ctx, ty) : goal) : open_term_with_context =
  failwith "[noCycle] is not implemented!"

let identity (env : Environ.env) (evd : Evd.evar_map ref)
  (gl : goal) : open_term_with_context =
  gl, fun c -> c



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
    let concl = Proofview.Goal.concl gl in
    (* We also need to convert the goal for it to be well-typed in
     * the [rel_context]. *)
    let ty = Vars.subst_vars subst concl in
    (* [ty'] is the expected type of the hole in the term, under the
     * context [ctx']. *)
    Proofview.Refine.refine (fun evd ->
      let evd = ref evd in
      let (ctx', ty'), term = simplify rules env evd (ctx, ty) in
      let c = let env = Environ.push_rel_context ctx' env in
          Evarutil.e_new_evar ~principal:true env evd ty'
      in !evd, term c)
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
