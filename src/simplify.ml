(* Some types to define what is a simplification. *)
type direction = Left | Right

type simplification_step =
    Deletion
  | Solution of direction option (* None = infer it *)
  | NoConfusion
  | NoCycle

(* None = infer it. *)
type simplification_rules = (Loc.t * simplification_step option) list

type goal = Context.rel_context * Term.types

type open_term =
  Environ.env -> Evd.evar_map -> Term.constr -> Evd.evar_map * Term.constr
type open_term_with_context = goal * open_term

exception CannotSimplify of Pp.std_ppcmds

type simplification_fun =
  Environ.env -> Evd.evar_map -> goal -> open_term_with_context

(* Auxiliary functions. *)

let strengthen (env : Environ.env) (evd : Evd.evar_map) (ctx : Context.rel_context)
  (x : int) (t : Term.constr) : Covering.context_map * Covering.context_map =
  failwith "[strengthen] is not implemented!"

(* Add a typing check. *)
let safe_term ((ctx, ty), f) : open_term_with_context =
  (ctx, ty), fun env evd c ->
    let () =
      let env = Environ.push_rel_context ctx env in
      let evd = ref evd in
        Typing.check env evd c ty
    in f env evd c

(* Build an open term by substituting the second term for the hole in the
 * first term. *)
let compose_term
  (((ctx1, ty1), f1) : open_term_with_context)
  (((ctx2, ty2), f2) : open_term_with_context) : open_term_with_context =
  (ctx2, ty2), fun env evd c ->
    let evd, c = f2 env evd c in
      f1 env evd c

let safe_fun (f : simplification_fun)
  (env : Environ.env) (evd : Evd.evar_map) (gl : goal) : open_term_with_context =
    safe_term (f env evd gl)

(* Applies [g] to the goal, then [f]. *)
let compose_fun (f : simplification_fun) (g : simplification_fun)
  (env : Environ.env) (evd : Evd.evar_map) (gl : goal) : open_term_with_context =
  let (gl, _) as term1 = g env evd gl in
  let term2 = f env evd gl in
    compose_term term1 term2

(* Simplification functions to handle each step. *)
(* Any of these can throw a CannotSimplify exception which explains why the
 * rule cannot apply. *)

let deletion (env : Environ.env) (evd : Evd.evar_map)
  ((ctx, ty) : goal) : open_term_with_context =
  try
    let name, ty1, ty2 = Term.destProd ty in
      let ind, args = Term.decompose_appvect ty1 in
      if false then
        raise (CannotSimplify (Pp.str
          "[deletion] First hypothesis in the goal is not an equality."))
      else
        if Vars.noccurn 1 ty2 then
          (* The goal does not depend on the equality, we can just eliminate it. *)
          (ctx, Vars.lift (-1) ty2), fun env evd c ->
            evd, Constr.mkLambda (Names.Anonymous, ty1, Vars.lift 1 c)
        else
          failwith "[deletion] is not implemented!"
  with
  | Term.DestKO -> raise (CannotSimplify (Pp.str
    "[deletion] The goal is not a product."))

let solution ~dir:direction (env : Environ.env) (evd : Evd.evar_map)
  ((ctx, ty) : goal) : open_term_with_context =
  failwith "[solution] is not implemented!"

let noConfusion (env : Environ.env) (evd : Evd.evar_map)
  ((ctx, ty) : goal) : open_term_with_context =
  failwith "[noConfusion] is not implemented!"

let noCycle (env : Environ.env) (evd : Evd.evar_map)
  ((ctx, ty) : goal) : open_term_with_context =
  failwith "[noCycle] is not implemented!"

let identity (env : Environ.env) (evd : Evd.evar_map)
  (gl : goal) : open_term_with_context =
  gl, fun env evd c -> evd, c



let deletion = safe_fun deletion
let solution ~dir = safe_fun (solution ~dir)
let noConfusion = safe_fun noConfusion
let noCycle = safe_fun noCycle
let identity = safe_fun identity


let execute_step : simplification_step -> simplification_fun = function
  | Deletion -> deletion
  | Solution (Some dir) -> solution ~dir:dir
  | NoConfusion -> noConfusion
  | NoCycle -> noCycle
  (* We assume the direction has been inferred at this point. *)
  | Solution None -> assert false

let infer_step ~isDir:bool (env : Environ.env) (evd : Evd.evar_map)
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
    let evd = Proofview.Goal.sigma gl in
    let hyps = Proofview.Goal.hyps gl in
    (* We want to work in a [rel_context], not a [named_context]. *)
    let ctx, subst = Covering.rel_of_named_context hyps in
    let concl = Proofview.Goal.concl gl in
    (* We also need to convert the goal for it to be well-typed in
     * the [rel_context]. *)
    let ty = Vars.subst_vars subst concl in
    (* [ty'] is the expected type of the hole in the term, under the
     * context [ctx']. *)
    let (ctx', ty'), term = simplify rules env evd (ctx, ty) in
      Proofview.Refine.refine (fun evd ->
        let evd, c = let env = Environ.push_rel_context ctx' env in
          Evarutil.new_evar ~principal:true env evd ty'
        in term env evd c)
  end


(* Printing functions. *)

let pr_simplification_step : simplification_step -> Pp.std_ppcmds = function
  | Deletion -> Pp.str "-"
  | Solution (Some Left) -> Pp.str "->"
  | Solution (Some Right) -> Pp.str "<-"
  | Solution None -> Pp.str "<->"
  | NoConfusion -> Pp.str "NoConfusion"
  | NoCycle -> Pp.str "NoCycle"

let pr_simplification_rule ((_, rule) : Loc.t * simplification_step option) :
  Pp.std_ppcmds = match rule with
  | None -> Pp.str "?"
  | Some step -> pr_simplification_step step

let pr_simplification_rules : simplification_rules -> Pp.std_ppcmds =
  Pp.prlist_with_sep Pp.spc pr_simplification_rule
