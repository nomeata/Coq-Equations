open Pp

(* ========== Coq references ========= *)
(* This section should change a lot when we approach an actual solution. *)

module type SIGMAREFS = sig
  val sigma : Names.inductive Lazy.t
  val sigmaI : Names.constructor Lazy.t
end

module type EQREFS = sig
  (* Equality type. *)
  val eq : Names.inductive Lazy.t
  val eq_refl : Names.constructor Lazy.t
  val eq_rect : Names.constant Lazy.t
  val eq_rect_r : Names.constant Lazy.t
  (* Decidable equality typeclass. *)
  val eq_dec : Names.constant Lazy.t
  (* Logic types. *)
  val zero : Names.inductive Lazy.t
  val one : Names.inductive Lazy.t
  val one_val : Names.constructor Lazy.t
  val one_ind_dep : Names.constant Lazy.t
  val zero_ind : Names.constant Lazy.t
  val zero_ind_dep : Names.constant Lazy.t
  (* NoConfusion. *)
  val noConfusion : Names.inductive Lazy.t
  val apply_noConfusion : Names.constant Lazy.t
  val simplify_ind_pack : Names.constant Lazy.t
  val simplify_ind_pack_inv : Names.constant Lazy.t
  val opaque_ind_pack_eq_inv : Names.constant Lazy.t
  (* Simplification of dependent pairs. *)
  val simpl_sigma : Names.constant Lazy.t
  val simpl_sigma_dep : Names.constant Lazy.t
  val simpl_sigma_dep_dep : Names.constant Lazy.t
  val pack_sigma_eq : Names.constant Lazy.t
  (* Deletion using K. *)
  val simpl_K : Names.constant Lazy.t
  val simpl_K_dec : Names.constant Lazy.t
  (* Solution lemmas. *)
  val solution_left : Names.constant Lazy.t
  val solution_left_dep : Names.constant Lazy.t
  val solution_right : Names.constant Lazy.t
  val solution_right_dep : Names.constant Lazy.t
end

module RefsHelper = struct
  let init_reference = Coqlib.find_reference "Equations.Simplify"
  let init_inductive dir s = lazy (Globnames.destIndRef (init_reference dir s))
  let init_constructor dir s = lazy (Globnames.destConstructRef (init_reference dir s))
  let init_constant dir s = lazy (Globnames.destConstRef (init_reference dir s))
end

(* This should be parametrizable by the user. *)
module EqRefs : EQREFS = struct
  include RefsHelper

  let init_depelim s = init_constant ["Equations"; "DepElim"] s

  let eq = lazy (Globnames.destIndRef (Coqlib.build_coq_eq ()))
  let eq_refl = lazy (Globnames.destConstructRef (Coqlib.build_coq_eq_refl ()))
  let eq_rect = init_constant ["Coq"; "Init"; "Logic"] "eq_rect"
  let eq_rect_r = init_constant ["Coq"; "Init"; "Logic"] "eq_rect_r"
  let eq_dec = init_constant ["Equations"; "EqDec"] "EqDec"
  let zero = init_inductive ["Coq"; "Init"; "Logic"] "False"
  let one = init_inductive ["Coq"; "Init"; "Logic"] "True"
  let one_val = init_constructor ["Coq"; "Init"; "Logic"] "I"
  let one_ind_dep = init_depelim "True_rect_dep"
  let zero_ind = init_constant ["Coq"; "Init"; "Logic"] "False_rect"
  let zero_ind_dep = init_depelim "False_rect_dep"
  let noConfusion = init_inductive ["Equations"; "DepElim"] "NoConfusionPackage"
  let apply_noConfusion = init_depelim "apply_noConfusion"
  let simplify_ind_pack = init_depelim "simplify_ind_pack"
  let simplify_ind_pack_inv = init_depelim "simplify_ind_pack_inv"
  let opaque_ind_pack_eq_inv = init_depelim "opaque_ind_pack_eq_inv"
  let simpl_sigma = init_depelim "eq_simplification_sigma1"
  let simpl_sigma_dep = init_depelim "eq_simplification_sigma1_dep"
  let simpl_sigma_dep_dep = init_depelim "eq_simplification_sigma1_dep_dep"
  let pack_sigma_eq = init_depelim "pack_sigma_eq"
  let simpl_K = init_depelim "simplification_K"
  let simpl_K_dec = init_depelim "simplification_K_dec"
  let solution_left = init_depelim "solution_left"
  let solution_left_dep = init_depelim "solution_left_dep"
  let solution_right = init_depelim "solution_right"
  let solution_right_dep = init_depelim "solution_right_dep"
end

(* This should not. *)
module SigmaRefs : SIGMAREFS = struct
  include RefsHelper

  let sigma = init_inductive ["Equations"; "Init"] "sigma"
  let sigmaI = init_constructor ["Equations"; "Init"] "sigmaI"
end

(* From the references, we can build terms. *)

type constr_gen = Evd.evar_map ref -> Term.constr

module type BUILDER = sig
  val sigma : constr_gen
  val sigmaI : constr_gen
  val eq : constr_gen
  val eq_refl : constr_gen
  val eq_dec : constr_gen
  val zero : constr_gen
  val one : constr_gen
  val one_val : constr_gen
  val one_ind_dep : constr_gen
  val zero_ind : constr_gen
  val zero_ind_dep : constr_gen
  val noConfusion : constr_gen
  val apply_noConfusion : constr_gen
  val simplify_ind_pack : constr_gen
  val simplify_ind_pack_inv : constr_gen
  val simpl_sigma : constr_gen
  val simpl_sigma_dep : constr_gen
  val simpl_sigma_dep_dep : constr_gen
  val simpl_K : constr_gen
  val simpl_K_dec : constr_gen
  val solution_left : constr_gen
  val solution_left_dep : constr_gen
  val solution_right : constr_gen
  val solution_right_dep : constr_gen
end

module BuilderHelper = struct
  let gen_from_inductive ind = fun evd ->
    let glob = Globnames.IndRef (Lazy.force ind) in
      Evarutil.e_new_global evd glob
  let gen_from_constant cst = fun evd ->
    let glob = Globnames.ConstRef (Lazy.force cst) in
      Evarutil.e_new_global evd glob
  let gen_from_constructor constr = fun evd ->
    let glob = Globnames.ConstructRef (Lazy.force constr) in
      Evarutil.e_new_global evd glob
end

module BuilderGen (SigmaRefs : SIGMAREFS) (EqRefs : EQREFS) : BUILDER = struct
  include BuilderHelper

  let sigma = gen_from_inductive SigmaRefs.sigma
  let sigmaI = gen_from_constructor SigmaRefs.sigmaI
  let eq = gen_from_inductive EqRefs.eq
  let eq_refl = gen_from_constructor EqRefs.eq_refl
  let eq_dec = gen_from_constant EqRefs.eq_dec
  let zero = gen_from_inductive EqRefs.zero
  let one = gen_from_inductive EqRefs.one
  let one_val = gen_from_constructor EqRefs.one_val
  let one_ind_dep = gen_from_constant EqRefs.one_ind_dep
  let zero_ind = gen_from_constant EqRefs.zero_ind
  let zero_ind_dep = gen_from_constant EqRefs.zero_ind_dep
  let noConfusion = gen_from_inductive EqRefs.noConfusion
  let apply_noConfusion = gen_from_constant EqRefs.apply_noConfusion
  let simplify_ind_pack = gen_from_constant EqRefs.simplify_ind_pack
  let simplify_ind_pack_inv = gen_from_constant EqRefs.simplify_ind_pack_inv
  let simpl_sigma = gen_from_constant EqRefs.simpl_sigma
  let simpl_sigma_dep = gen_from_constant EqRefs.simpl_sigma_dep
  let simpl_sigma_dep_dep = gen_from_constant EqRefs.simpl_sigma_dep_dep
  let simpl_K = gen_from_constant EqRefs.simpl_K
  let simpl_K_dec = gen_from_constant EqRefs.simpl_K_dec
  let solution_left = gen_from_constant EqRefs.solution_left
  let solution_left_dep = gen_from_constant EqRefs.solution_left_dep
  let solution_right = gen_from_constant EqRefs.solution_right
  let solution_right_dep = gen_from_constant EqRefs.solution_right_dep
end

module Builder : BUILDER = BuilderGen(SigmaRefs)(EqRefs)

(* ========== Simplification ========== *)

(* Some types to define what is a simplification. *)
type direction = Left | Right

type simplification_step =
    Deletion of bool (* Force the use of K? *)
  | Solution of direction
  | NoConfusion of simplification_rules
  | NoConfusionOut (* Step for the inversion of [simplify_ind_pack]. *)
  | NoCycle (* TODO: NoCycle should probably take a direction too. *)
  | ElimTrue | ElimFalse
and simplification_rule =
    Step of simplification_step
  | Infer_one
  | Infer_direction
  | Infer_many
and simplification_rules = (Loc.t * simplification_rule) list

type goal = Context.rel_context * Term.types
type open_term = (goal * Evd.evar) option * Term.constr

exception CannotSimplify of Pp.std_ppcmds

type simplification_fun = Environ.env -> Evd.evar_map ref -> goal -> open_term

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

(* Build an open term from a [Term.constr -> Term.constr] function, a goal
   and an expected [Context.rel_context] for the hole, using typing to infer
   the type of the hole. *)
let build_term (env : Environ.env) (evd : Evd.evar_map ref) ((ctx, ty) : goal)
  (ctx' : Context.rel_context) (f : Term.constr -> Term.constr) : open_term =
  let ev_ty, tev =
    let env = Environ.push_rel_context ctx' env in
    let ev_ty, _ = Evarutil.e_new_type_evar env evd Evd.univ_flexible_alg in
    let tev = Evarutil.e_new_evar env evd ev_ty in
      ev_ty, tev
  in
  let c = f tev in
  let env = Environ.push_rel_context ctx env in
  Typing.check env evd c ty;
  let ty' = Evd.existential_value !evd (Term.destEvar ev_ty) in
  let ev, _ = Term.destEvar tev in
  (*
  msg_info (str "Term is: " ++ Printer.pr_constr_env env !evd c);
  msg_info (str "Type of hole is: " ++ Printer.pr_constr_env env !evd ty');
  *)
    Some ((ctx', ty'), ev), c

(* Build an open term by substituting the second term for the hole in the
 * first term. *)
let compose_term (evd : Evd.evar_map ref)
  ((h1, c1) : open_term) ((h2, c2) : open_term) : open_term =
  match h1 with
  | Some ((ctx1, _), ev1) ->
      (* Currently, [c2] is typed under the rel_context [ctx1]. We want
         to assigne it to the evar [ev1], which means that we need to transpose
         it to the named_context of this evar. *)
      let subst, _ = Covering.named_of_rel_context ctx1 in
      let c2 = Vars.substl subst c2 in
        evd := Evd.define ev1 c2 !evd; h2, c1
  | None -> assert false

let safe_fun (f : simplification_fun)
  (env : Environ.env) (evd : Evd.evar_map ref) ((ctx, ty) : goal) : open_term =
  let (_, c) as res = f env evd (ctx, ty) in
  let env = Environ.push_rel_context ctx env in
  Typing.check env evd c ty;
  res

(* Applies [g] to the goal, then [f]. *)
let compose_fun (f : simplification_fun) (g : simplification_fun)
  (env : Environ.env) (evd : Evd.evar_map ref) (gl : goal) : open_term =
  let (h1, _) as t1 = g env evd gl in
  match h1 with
  | Some (gl', _) ->
      let t2 = f env evd gl' in
        compose_term evd t1 t2
  | None -> t1

(* Check if a type is a given inductive. *)
let check_inductive (ind : Names.inductive) : Term.types -> bool =
  Globnames.is_global (Globnames.IndRef ind)
(* Check if a term is a given constructor. *)
let check_construct (constr : Names.constructor) : Term.constr -> bool =
  Globnames.is_global (Globnames.ConstructRef constr)
(* Check if a term is a given constant. *)
let check_constant (cst : Names.constant) : Term.constr -> bool =
  Globnames.is_global (Globnames.ConstRef cst)

(* Deconstruct the goal if it's a product. Otherwise, raise CannotSimplify. *)
let check_prod (ty : Term.types) : Names.name * Term.types * Term.types =
  let name, ty1, ty2 = try Term.destProd ty
    with Term.DestKO -> raise (CannotSimplify (str "The goal is not a product."))
  in name, ty1, ty2

(* Check that the given type is an equality, and some
 * additional constraints if specified. Raise CannotSimplify if it's not
 * the case. Otherwise, return its arguments *)
let check_equality ?(equal_terms : bool = false)
  ?(var_left : bool = false) ?(var_right : bool = false) (ty : Term.types) :
    Term.types * Term.constr * Term.constr =
  let f, args = Term.decompose_appvect ty in
  if not (check_inductive (Lazy.force EqRefs.eq) f) then
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
  tA, tx, ty

let decompose_sigma (t : Term.constr) :
  (Term.types * Term.constr * Term.constr * Term.constr) option =
  let f, args = Term.decompose_appvect t in
  if check_construct (Lazy.force SigmaRefs.sigmaI) f then
    Some (args.(0), args.(1), args.(2), args.(3))
  else None

let with_retry (f : simplification_fun) (env : Environ.env)
  (evd : Evd.evar_map ref) ((ctx, ty) : goal) : open_term =
  try
    (* Be careful with the [evar_map] management. *)
    let evd' = ref !evd in
    let res = f env evd' (ctx, ty) in
    evd := !evd'; res
  with CannotSimplify _ ->
    msg_info (str "Reduce!");
    let reduce c =
      let env = Environ.push_rel_context ctx env in
        Tacred.hnf_constr env !evd c
    in
  (* Try to head-reduce the goal and reapply f. *) 
    let name, ty1, ty2 = try Term.destProd ty
      with Term.DestKO -> raise (CannotSimplify (str "The goal is not a product.")) in
    let ty1 = reduce ty1 in
    let ty = Constr.mkProd (name, ty1, ty2) in
    (* If the head is an equality, reduce it. *)
    let ty = try
      let name, ty1, ty2 = check_prod ty in
      let tA, t1, t2 = check_equality ty1 in
      let t1 = reduce t1 in
      let t2 = reduce t2 in
      let ty1 = Constr.mkApp (Builder.eq evd, [| tA; t1; t2 |]) in
        Constr.mkProd (name, ty1, ty2)
      with CannotSimplify _ -> ty
    in
      f env evd (ctx, ty)

(* Simplification functions to handle each step. *)
(* Any of these can throw a CannotSimplify exception which explains why the
 * rule cannot apply. *)

(* This function is not accessible by the user for now. It is used to project
 * (if needed) the first component of an equality between sigmas. It will not
 * do anything if it fails. *)
let remove_sigma (env : Environ.env) (evd : Evd.evar_map ref)
  ((ctx, ty) : goal) : open_term =
  let f =
  try
    let name, ty1, ty2 = check_prod ty in
    let _, t1, t2 = check_equality ty1 in
      match decompose_sigma t1, decompose_sigma t2 with
      | Some (tA, tB, tt, tp), Some (_, _, tu, tq) ->
          (* Determine the degree of dependency. *)
          if Vars.noccurn 1 ty2 then begin
            (* No dependency in the goal, but maybe there is a dependency in
               the pair itself. *)
            try
              let name', _, tBbody = Term.destLambda tB in
              if Vars.noccurn 1 tBbody then
                (* No dependency whatsoever. *)
                let tsimpl_sigma = Builder.simpl_sigma evd in
                let tP = Termops.pop tBbody in
                let tB = Termops.pop ty2 in
                fun c -> Constr.mkApp
                  (tsimpl_sigma, [| tA; tP; tB; tt; tu; tp; tq; c |])
              else raise Term.DestKO
            with
            | Term.DestKO ->
                (* Dependency in the pair, but not in the goal. *)
                let tsimpl_sigma = Builder.simpl_sigma_dep evd in
                let tP = tB in
                let tB = Termops.pop ty2 in
                fun c -> Constr.mkApp
                  (tsimpl_sigma, [| tA; tP; tB; tt; tu; tp; tq; c |])
          end else
            (* We assume full dependency. We could add one more special case,
             * but we don't for now. *)
            let tsimpl_sigma = Builder.simpl_sigma_dep_dep evd in
            let tP = tB in
            let tB = Constr.mkLambda (name, ty1, ty2) in
            fun c -> Constr.mkApp
              (tsimpl_sigma, [| tA; tP; tt; tu; tp; tq; tB; c |])
      | _, _ -> fun c -> c
  with CannotSimplify _ -> fun c -> c
  in build_term env evd (ctx, ty) ctx f

let deletion ~(force:bool) (env : Environ.env) (evd : Evd.evar_map ref)
  ((ctx, ty) : goal) : open_term =
  let name, ty1, ty2 = check_prod ty in
  let tA, tx, _ = check_equality ~equal_terms:true ty1 in
  let f =
    if Vars.noccurn 1 ty2 then
      (* The goal does not depend on the equality, we can just eliminate it. *)
      fun c -> Constr.mkLambda (name, ty1, Vars.lift 1 c)
    else
      let tB = Constr.mkLambda (name, ty1, ty2) in
      if force then
        (* The user wants to use K directly. *)
        let tsimpl_K = Builder.simpl_K evd in
        fun c ->
          Constr.mkApp (tsimpl_K, [| tA; tx; tB; c |])
      else
        (* We will try to find an instance of K for the type [A]. *)
        let tsimpl_K_dec = Builder.simpl_K_dec evd in
        let eqdec_ty = Constr.mkApp (Builder.eq_dec evd, [| tA |]) in
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
  in build_term env evd (ctx, ty) ctx f

let solution ~(dir:direction) (env : Environ.env) (evd : Evd.evar_map ref)
  ((ctx, ty) : goal) : open_term =
  let var_left = match dir with Left -> true | Right -> false in
  let var_right = not var_left in
  let name, ty1, ty2 = check_prod ty in
  let tA, tx, tz = check_equality ~var_left ~var_right ty1 in
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
  | false, false -> Builder.solution_right_dep
  | false, true -> Builder.solution_right
  | true, false -> Builder.solution_left_dep
  | true, true -> Builder.solution_left end evd
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
  let f = fun c ->
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
  in build_term env evd (ctx, ty) ctx'' f

(* Auxiliary steps for noConfusion. *)
let maybe_pack (env : Environ.env) (evd : Evd.evar_map ref)
  ((ctx, ty) : goal) : open_term =
  let name, ty1, ty2 = check_prod ty in
  let tA, t1, t2 = check_equality ty1 in
  let fA, _ = Term.decompose_app tA in
  let f1, _ = Term.decompose_app t1 in
  let f2, _ = Term.decompose_app t2 in
  if not (Term.isInd fA && Term.isConstruct f1 && Term.isConstruct f2) then
    raise (CannotSimplify (str "This is not an equality between constructors."));
  let indty = Inductiveops.find_rectype env !evd tA in
  let indfam, args = Inductiveops.dest_ind_type indty in
  if CList.is_empty args then
    build_term env evd (ctx, ty) ctx (fun c -> c)
  else begin
    (* We need to apply [simplify_ind_pack]. *)
    let ind, params = Inductiveops.dest_ind_family indfam in
    let evd', tB, _, _, valsig, _, _, tA = Sigma.build_sig_of_ind env !evd ind in
    evd := evd';
    (* We will try to find an instance of K for the type [A]. *)
    let eqdec_ty = Constr.mkApp (Builder.eq_dec evd, [| tA |]) in
    let tdec =
      let env = Environ.push_rel_context ctx env in
      try
        Evarutil.evd_comb1
          (Typeclasses.resolve_one_typeclass env) evd eqdec_ty
      with Not_found ->
        raise (CannotSimplify (str
          "[noConfusion] Cannot simplify without K on type " ++
          Printer.pr_constr_env env !evd tA))
    in
    let tx =
      let _, _, tx, _ = Option.get (decompose_sigma valsig) in
        Vars.substl args (Termops.pop tx)
    in
    let tsimplify_ind_pack = Builder.simplify_ind_pack evd in
    let tG = Constr.mkLambda (name, ty1, ty2) in
    let f = fun c ->
      Constr.mkApp (tsimplify_ind_pack, [| tA; tdec; tB; tx; t1; t2; tG; c |])
    in
      build_term env evd (ctx, ty) ctx f
  end

let apply_noconf (env : Environ.env) (evd : Evd.evar_map ref)
  ((ctx, ty) : goal) : open_term =
  let name, ty1, ty2 = check_prod ty in
  let tA, t1, t2 = check_equality ty1 in
  let noconf_ty = Constr.mkApp (Builder.noConfusion evd, [| tA |]) in
  let tnoconf =
    let env = Environ.push_rel_context ctx env in
    try
      Evarutil.evd_comb1
        (Typeclasses.resolve_one_typeclass env) evd noconf_ty
    with Not_found ->
      raise (CannotSimplify (str
        "[noConfusion] Cannot find an instance of NoConfusion for type " ++
        Printer.pr_constr_env env !evd tA))
  in
  let tapply_noconf = Builder.apply_noConfusion evd in
  let tB = Constr.mkLambda (name, ty1, ty2) in
  build_term env evd (ctx, ty) ctx
  begin fun c ->
    Constr.mkApp (tapply_noconf, [| tA; tnoconf; t1; t2; tB; c |]) end

let simplify_ind_pack_inv (env : Environ.env) (evd : Evd.evar_map ref)
  ((ctx, ty) : goal) : open_term =
  (* FIXME Can't ignore _all_ errors? *)
  try
    let f, args = Term.decompose_appvect ty in 
    if not (check_constant (Lazy.force EqRefs.opaque_ind_pack_eq_inv) f) ||
       not (Int.equal 8 (Array.length args)) then
      raise (CannotSimplify (str
        "Expected a full application of [opaque_ind_pack_eq_inv]. Maybe
         you did not solve completely a NoConfusion step?"));
    let tA = args.(0) in
    let teqdec = args.(1) in
    let tB = args.(2) in
    let tx = args.(3) in
    let tp = args.(4) in
    let tG = args.(6) in
    let teq = args.(7) in
    (* Check that [teq] is [eq_refl]. *)
    let tsigma = Constr.mkApp (Builder.sigma evd, [| tA; tB |]) in
    let tsigmaI = Constr.mkApp (Builder.sigmaI evd, [| tA; tB; tx; tp |]) in
    let teq_refl = Constr.mkApp (Builder.eq_refl evd, [| tsigma; tsigmaI |]) in
    if not (Evarconv.e_cumul env evd teq teq_refl) then
      (* FIXME Horrible error message... *)
      raise (CannotSimplify (str
        "[opaque_ind_pack_eq_inv] should be applied to [eq_refl]."));
    let tsimplify_ind_pack_inv = Builder.simplify_ind_pack_inv evd in
      build_term env evd (ctx, ty) ctx begin fun c ->
        Constr.mkApp (tsimplify_ind_pack_inv, [| tA; teqdec; tB; tx; tp; tG; c |])
      end
  with CannotSimplify _ ->
    build_term env evd (ctx, ty) ctx (fun c -> c)

let noConfusion = compose_fun apply_noconf maybe_pack

let noCycle (env : Environ.env) (evd : Evd.evar_map ref)
  ((ctx, ty) : goal) : open_term =
  failwith "[noCycle] is not implemented!"

let elim_true (env : Environ.env) (evd : Evd.evar_map ref)
  ((ctx, ty) : goal) : open_term =
  let name, ty1, ty2 = check_prod ty in
  if not (check_inductive (Lazy.force EqRefs.one) ty1) then
    raise (CannotSimplify (str
      "[elim_true] The first hypothesis is not the unit type."));
  let f =
    (* Check if the goal is dependent or not. *)
    if Vars.noccurn 1 ty2 then
      (* Not dependent, we can just eliminate True. *)
      fun c -> Constr.mkLambda (name, ty1, Vars.lift 1 c)
    else
      (* Apply the dependent induction principle for True. *)
      let tB = Constr.mkLambda (name, ty1, ty2) in
      let tone_ind = Builder.one_ind_dep evd in
      fun c ->
        Constr.mkApp (tone_ind, [| tB; c |])
  in build_term env evd (ctx, ty) ctx f

let elim_false (env : Environ.env) (evd : Evd.evar_map ref)
  ((ctx, ty) : goal) : open_term =
  let name, ty1, ty2 = check_prod ty in
  if not (check_inductive (Lazy.force EqRefs.zero) ty1) then
    raise (CannotSimplify (str
      "[elim_true] The first hypothesis is not the empty type."));
  let tB, tzero_ind =
  (* Check if the goal is dependent or not. *)
    if Vars.noccurn 1 ty2 then
      let tB = Termops.pop ty2 in
      let tzero_ind = Builder.zero_ind evd in
        tB, tzero_ind
    else
      let tB = Constr.mkLambda (name, ty1, ty2) in
      let tzero_ind = Builder.zero_ind_dep evd in
        tB, tzero_ind
  in
  let c = Constr.mkApp (tzero_ind, [| tB |]) in
  (* We need to type the term in order to solve eventual universes
   * constraints. *)
  let _ = let env = Environ.push_rel_context ctx env in
    Typing.e_type_of env evd c in
    None, c

let identity (env : Environ.env) (evd : Evd.evar_map ref) (gl : goal) : open_term =
  build_term env evd gl (fst gl) (fun c -> c)


(* Inference mechanism. *)

let infer_step ~(loc:Loc.t) ~(isSol:bool)
  (env : Environ.env) (evd : Evd.evar_map ref)
  ((ctx, ty) : goal) : simplification_step =
  (* The goal does not have to be a product, but if it's not, it has to be
   * an application of [opaque_ind_pack_eq_inv]. *)
  let f, _ = Term.decompose_appvect ty in
  if check_constant (Lazy.force EqRefs.opaque_ind_pack_eq_inv) f then
    NoConfusionOut
  else begin
    let name, ty1, ty2 = check_prod ty in
    (* First things first, maybe the head of the goal is False or True. *)
    if check_inductive (Lazy.force EqRefs.zero) ty1 then ElimFalse
    else if check_inductive (Lazy.force EqRefs.one) ty1 then ElimTrue
    else
    (* We need to destruct the equality at the head
       to analyze it. *)
    let tA, tu, tv = check_equality ty1 in
    (* If the user wants a solution, we need to respect his wishes. *)
    if isSol then
      if Term.isRel tu then Solution Left
      else if Term.isRel tv then Solution Right
      else raise (CannotSimplify (str "Neither side of the equality is a variable."))
    else begin
      let check_occur trel term =
        let rel = Term.destRel trel in
          not (Int.Set.mem rel (Covering.dependencies_of_term env !evd ctx term rel))
      in
      if Term.isRel tu && check_occur tu tv then Solution Left
      else if Term.isRel tv && check_occur tv tu then Solution Right
      else
      let check_ind t =
        let f, _ = Term.decompose_app t in
          Term.isInd f
      in
      let check_construct t =
          let f, _ = Term.decompose_app t in
            Term.isConstruct f
      in
      if check_ind tA && check_construct tu && check_construct tv then
        NoConfusion [loc, Infer_many]
      else if Constr.equal tu tv then Deletion false (* Never force K. *)
      else
      (* Check if [u] occurs in [t] under only constructors. *)
      (* For now we don't care about the type of these constructors. *)
      (* Note that we also don't need to care about binders, since we can
         only go through constructors and nothing else. *)
      let check_occur t u =
        let eq t = fst (Universes.eq_constr_universes t u) in
        let rec aux t =
          if eq t then raise Termops.Occur;
          let f, args = Term.decompose_app t in
          if Term.isConstruct f then
            CList.iter aux args
        in try aux t; false
        with Termops.Occur -> true
      in
      if check_occur tu tv || check_occur tv tu then NoCycle
      else
        raise (CannotSimplify (str "Could not infer a simplification step."))
    end
  end

let expand_many rule env evd ((_, ty) : goal) : simplification_rules =
  (* FIXME: maybe it's too brutal/expensive? *)
  let ty = Tacred.compute env !evd ty in
  let _, ty, _ = check_prod ty in
  try
    let ty, _, _ = check_equality ty in
    let rec aux ty acc =
      let f, args = Term.decompose_appvect ty in
      if check_inductive (Lazy.force SigmaRefs.sigma) f then aux args.(0) (rule :: acc)
      else acc
    in aux ty [rule]
  with CannotSimplify _ -> [rule]


(* Execution machinery. *)

let rec execute_step : simplification_step -> simplification_fun = function
  | Deletion force -> deletion ~force
  | Solution dir -> solution ~dir:dir
  | NoConfusion rules -> compose_fun simplify_ind_pack_inv
      (compose_fun (simplify rules) noConfusion)
  | NoConfusionOut -> simplify_ind_pack_inv
  | NoCycle -> noCycle
  | ElimTrue -> elim_true
  | ElimFalse -> elim_false

and simplify_one ((loc, rule) : Loc.t * simplification_rule) :
  simplification_fun =
  let handle_error f =
    fun env evd gl ->
      try f env evd gl
      with CannotSimplify err ->
        Errors.user_err_loc (loc, "Equations.Simplify", err)
  in
  let wrap get_step =
    let f = fun env evd gl ->
      let step = get_step env evd gl in
        execute_step step env evd gl
    in
(*    let f = safe_fun f in*)
    let f = compose_fun f remove_sigma in
    let f = with_retry f in
      handle_error f
  in
  match rule with
  | Infer_many -> fun env evd gl ->
      let rules = handle_error (expand_many (loc, Infer_one)) env evd gl in
        simplify rules env evd gl
  | Step step -> wrap (fun _ _ _ -> step)
  | Infer_one -> wrap (infer_step ~loc ~isSol:false)
  | Infer_direction -> wrap (infer_step ~loc ~isSol:true)

and simplify (rules : simplification_rules) : simplification_fun =
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
      (*
      msg_info (str "Goal is: " ++ Printer.pr_constr_env
        (Proofview.Goal.env gl) evd concl);
      *)
      let evd = ref evd in
      let _, c = simplify rules env evd (ctx, ty) in
      let c = Vars.substl rev_subst c in
        !evd, c)
  end


(* Printing functions. *)

let pr_simplification_step : simplification_step -> Pp.std_ppcmds = function
  | Deletion false -> str "-"
  | Deletion true -> str "-!"
  | Solution (Left) -> str "->"
  | Solution (Right) -> str "<-"
  | NoConfusion rules -> str "$"
  | NoConfusionOut -> str "NoConfusionOut"
  | NoCycle -> str "NoCycle"
  | ElimTrue -> str "ElimTrue"
  | ElimFalse -> str "ElimFalse"

let pr_simplification_rule ((_, rule) : Loc.t * simplification_rule) :
  Pp.std_ppcmds = match rule with
  | Infer_one -> str "?"
  | Infer_direction -> str "<->"
  | Infer_many -> str "*"
  | Step step -> pr_simplification_step step

let pr_simplification_rules : simplification_rules -> Pp.std_ppcmds =
  prlist_with_sep spc pr_simplification_rule
