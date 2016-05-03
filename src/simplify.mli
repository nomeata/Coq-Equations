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

type simplification_fun =
  Environ.env -> Evd.evar_map ref -> goal -> open_term_with_context

(* Auxiliary functions. *)

(* Return a substitution and its inverse. *)
(* For more flexibility, [rels] is a set of indices which are to be
 * moved before the variable. By default, this is everything already before
 * the variable. *)
val strengthen :
  Environ.env -> Evd.evar_map ->
  Context.rel_context -> int -> ?rels:Int.Set.t -> Term.constr ->
  Covering.context_map * Covering.context_map

val safe_term : Environ.env -> Evd.evar_map ref ->
  open_term_with_context -> open_term_with_context
val compose_term : open_term_with_context -> open_term_with_context ->
  open_term_with_context
val safe_fun : simplification_fun -> simplification_fun
val compose_fun : simplification_fun -> simplification_fun -> simplification_fun

(* Simplification functions to handle each step. *)
(* Any of these can throw a CannotSimplify exception which explains why the
 * rule cannot apply. *)
(* It is assumed that the head of the goal should be a simple equality that
 * the function has to simplify. *)
(* For instance, a goal such as [(p; x) = (q; y) -> P] has to be changed
 * to [forall (e : p = q), eq_rect ... x e = y -> P] beforehand. *)

val deletion : force:bool -> simplification_fun
val solution : dir:direction -> simplification_fun
val noConfusion : simplification_fun
val noCycle : simplification_fun
val identity : simplification_fun

val execute_step : simplification_step -> simplification_fun

val infer_step :
  isDir:bool -> Environ.env -> Evd.evar_map ref -> goal -> simplification_step

val simplify : simplification_rules -> simplification_fun

val simplify_tac : simplification_rules -> unit Proofview.tactic

val pr_simplification_rules : simplification_rules -> Pp.std_ppcmds
