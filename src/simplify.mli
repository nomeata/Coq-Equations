(* Some types to define what is a simplification. *)
type direction = Left | Right

type simplification_step =
    Deletion
  | Solution of direction option (* None = infer it *)
  | NoConfusion
  | NoCycle

(* None = infer it. *)
type simplification_rules = simplification_step option list

type goal = Context.rel_context * Term.types

type open_term =
  Environ.env -> Evd.evar_map -> Term.constr -> Evd.evar_map * Term.constr
type open_term_with_context = goal * open_term

exception CannotSimplify of Pp.std_ppcmds

type simplification_fun =
  Environ.env -> Evd.evar_map -> goal -> open_term_with_context

(* Auxiliary functions. *)

(* Return a substitution and its inverse. *)
val strengthen :
  Environ.env -> Evd.evar_map ->
  Context.rel_context -> int -> Term.constr ->
  Covering.context_map * Covering.context_map

val safe_term : open_term_with_context -> open_term_with_context
val compose_term : open_term_with_context -> open_term_with_context ->
  open_term_with_context
val safe_fun : simplification_fun -> simplification_fun
val compose_fun : simplification_fun -> simplification_fun -> simplification_fun

(* Simplification functions to handle each step. *)
(* Any of these can throw a CannotSimplify exception which explains why the
 * rule cannot apply. *)

val deletion : simplification_fun
val solution : dir:direction -> simplification_fun
val noConfusion : simplification_fun
val noCycle : simplification_fun
val identity : simplification_fun

val execute_step : simplification_step -> simplification_fun

val infer_step :
  isDir:bool -> Environ.env -> Evd.evar_map -> goal -> simplification_step

val simplify : simplification_rules -> simplification_fun

val simplify_tac : simplification_rules -> unit Proofview.tactic

