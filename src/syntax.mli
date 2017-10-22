(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2016 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

open Term
open Context
open Environ
open Names
open Equations_common

(** User-level patterns *)
type generated = bool
type nested = bool

type user_pat =
    PUVar of identifier * generated
  | PUCstr of constructor * int * user_pats
  | PUInac of Constrexpr.constr_expr
and user_pats = user_pat Loc.located list


(** Globalized syntax *)

type lhs = user_pats (* p1 ... pn *)
and 'a rhs =
    Program of Constrexpr.constr_expr * 'a where_clause list
  | Empty of identifier Loc.located
  | Rec of Constrexpr.constr_expr * Constrexpr.constr_expr option *
             identifier Loc.located option * 'a list
  | Refine of Constrexpr.constr_expr * 'a list
  | By of (Tacexpr.raw_tactic_expr, Tacexpr.glob_tactic_expr) Util.union *
      'a list
and prototype =
  identifier located * nested * Constrexpr.local_binder list * Constrexpr.constr_expr
and 'a where_clause = prototype * 'a list
and program = (signature * clause list) list
and signature = identifier * rel_context * constr (* f : Π Δ. τ *)
and clause = Loc.t * lhs * clause rhs (* lhs rhs *)

val pr_user_pat : env -> user_pat Loc.located -> Pp.std_ppcmds
val pr_user_pats : env -> user_pats -> Pp.std_ppcmds

val pr_lhs : env -> user_pats -> Pp.std_ppcmds
val pplhs : user_pats -> unit
val pr_rhs : env -> clause rhs -> Pp.std_ppcmds
val pr_clause :
  env -> clause -> Pp.std_ppcmds
val pr_clauses :
  env -> clause list -> Pp.std_ppcmds
val ppclause : clause -> unit


(** Raw syntax *)
type pat_expr =
    PEApp of Libnames.reference Misctypes.or_by_notation located *
      pat_expr located list
  | PEWildcard
  | PEInac of Constrexpr.constr_expr
  | PEPat of Constrexpr.cases_pattern_expr
type user_pat_expr = pat_expr located
type input_pats =
    SignPats of (Id.t located option * user_pat_expr) list
  | RefinePats of user_pat_expr list
type pre_equation =
    identifier located option * input_pats * pre_equation rhs
type pre_equations = pre_equation where_clause list

type rec_type = 
  | Structural of (Id.t * nested * Id.t located option) list (* for mutual rec *)
  | Logical of logical_rec
and logical_rec =
  | LogicalDirect of Id.t located
  | LogicalProj of rec_info
and rec_info = {
  comp : constant option;
  comp_app : constr;
  comp_proj : constant;
  comp_recarg : int;
}
val is_structural : rec_type option -> bool
val is_rec_call : logical_rec -> constr -> bool
val next_ident_away : Id.t -> Id.t list ref -> Id.t

type equation_option = 
  | OInd of bool | ORec of Id.t located option 
  | OComp of bool 
  | OEquations of bool

type equation_user_option = equation_option

val pr_r_equation_user_option : 'a -> 'b -> 'c -> 'd -> Pp.std_ppcmds

type equation_options = equation_option list

val pr_equation_options : 'a -> 'b -> 'c -> 'd -> Pp.std_ppcmds

val translate_cases_pattern :
  'a -> Id.t list ref -> Glob_term.cases_pattern -> user_pat Loc.located

val ids_of_pats : pat_expr located list -> identifier list

val interp_pat : Environ.env -> ?avoid:Names.Id.t list ref ->
  user_pat_expr -> Loc.t * user_pat

val interp_eqn :
  identifier ->
  rec_type option ->
  env ->
  Impargs.implicit_status list ->
  pre_equation ->
  clause
