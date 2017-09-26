(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2016 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

open Cases
open Util
open Names
open Nameops
open Term
open Termops
open Declarations
open Inductiveops
open Environ
open Vars
open Reductionops
open Typeops
open Type_errors
open Pp
open Proof_type

open Locus
open Context

open Glob_term
open Retyping
open Pretype_errors
open Evarutil
open Evarconv
open List
open Libnames
open Topconstr
open Entries
open Tacmach
open Tacexpr
open Tactics
open Tacticals
open Decl_kinds

open Coqlib

let ($) f g = fun x -> f (g x)
let (&&&) f g (x, y) = (f x, g y)
let id x = x

(* Options. *)
let ocaml_splitting = ref true
let simplify_withK = ref true

let _ = Goptions.declare_bool_option {
  Goptions.optsync  = true;
  Goptions.optdepr  = false;
  Goptions.optname  = "splitting variables in OCaml";
  Goptions.optkey   = ["Equations"; "OCaml"; "Splitting"];
  Goptions.optread  = (fun () -> !ocaml_splitting);
  Goptions.optwrite = (fun b -> ocaml_splitting := b)
}

let _ = Goptions.declare_bool_option {
  Goptions.optsync  = true;
  Goptions.optdepr  = false;
  Goptions.optname  = "using K during simplification";
  Goptions.optkey   = ["Equations"; "WithK"];
  Goptions.optread  = (fun () -> !simplify_withK);
  Goptions.optwrite = (fun b -> simplify_withK := b)
}

(* Debugging infrastructure. *)

let debug = ref false

let _ = Goptions.declare_bool_option {
  Goptions.optsync  = true;
  Goptions.optdepr  = false;
  Goptions.optname  = "Equations debug output";
  Goptions.optkey   = ["Equations"; "Debug"];
  Goptions.optread  = (fun () -> !debug);
  Goptions.optwrite = (fun b -> debug := b)
}

let check_term env evd c t =
  Typing.e_check env (ref evd) c t

let check_type env evd t =
  ignore(Typing.e_sort_of env (ref evd) t)
      
let typecheck_rel_context env evd ctx =
  let open Context.Rel.Declaration in
  try
  let _ =
    List.fold_right
      (fun rel env ->
	 check_type env evd (get_type rel);
	 Option.iter (fun c -> check_term env evd c (get_type rel)) (get_value rel);
	 push_rel rel env)
      ctx env
  in ()
  with e ->
    Printf.eprintf "Exception while typechecking context %s : %s\n"
                   (Pp.string_of_ppcmds (print_rel_context (push_rel_context ctx env)))
                   (Printexc.to_string e);
    raise e

let new_untyped_evar () =
  let open Sigma in
  let Sigma (ev, _, _) = new_pure_evar empty_named_context_val (Sigma.Unsafe.of_evar_map Evd.empty) mkProp in
    ev

let to82 t = Proofview.V82.of_tactic t
let of82 t = Proofview.V82.tactic t

let proper_tails l = snd (List.fold_right (fun _ (t,ts) -> List.tl t, ts @ [t]) l (l, []))

let list_find_map_i f =
  let rec try_find_f n = function
    | [] -> None
    | h::t -> 
      match f n h with
      | Some _ as res -> res 
      | None -> try_find_f (n+1) t
  in
  try_find_f

let array_remove_last a =
  Array.sub a 0 (Array.length a - 1)

let array_chop_last a =
  Array.chop (Array.length a - 1) a

let rev_assoc eq k =
  let rec loop = function
    | [] -> raise Not_found | (v,k')::_ when eq k k' -> v | _ :: l -> loop l 
  in
  loop

let array_filter_map f a =
  let l' =
    Array.fold_right (fun c acc -> 
		      Option.cata (fun r -> r :: acc) acc (f c))
    a []
  in Array.of_list l'

let new_global evd gr =
  let sigma = Sigma.Unsafe.of_evar_map evd in
  let Sigma.Sigma (gr, sigma, _) = Evarutil.new_global sigma gr in
  Sigma.to_evar_map sigma, gr

let e_new_global evdref gr =
  let sigma, gr = new_global !evdref gr in
  evdref := sigma; gr

let find_constant contrib dir s evd =
  e_new_global evd (Coqlib.find_reference contrib dir s)

let contrib_name = "Equations"
let init_constant dir s evd = find_constant contrib_name dir s evd
let init_reference dir s = Coqlib.find_reference contrib_name dir s
let gen_constant dir s = Coqlib.gen_constant "equations" dir s

let global_reference id =
  Smartlocate.global_of_extended_global (Nametab.locate_extended (qualid_of_ident id))

let constr_of_ident id =
  Universes.constr_of_global (Nametab.locate (qualid_of_ident id))

let e_type_of = Typing.e_type_of ~refresh:false				 

let make_definition ?opaque ?(poly=false) evd ?types b =
  let env = Global.env () in
  let _t = Typing.e_type_of env evd b in
  let evm = match types with
    | None -> !evd
    | Some t -> let _s = Typing.e_type_of env evd t in !evd
  in
  let evm, nf = Evarutil.nf_evars_and_universes evm in
  let body = nf b and typ = Option.map nf types in
  let used = Universes.universes_of_constr body in
  let used' = Option.cata Universes.universes_of_constr Univ.LSet.empty typ in
  let used = Univ.LSet.union used used' in
  let evm = Evd.restrict_universe_context evm used in
  evd := evm;
  Declare.definition_entry ~poly ~univs:(snd (Evd.universe_context evm))
      ?types:typ body

let declare_constant id body ty poly evd kind =
  let ce = make_definition ~opaque:false ~poly (ref evd) ?types:ty body in
  let cst = Declare.declare_constant id (DefinitionEntry ce, kind) in
    Flags.if_verbose Feedback.msg_info (str((string_of_id id) ^ " is defined"));
    cst
    
let declare_instance id poly evd ctx cl args =
  let open Typeclasses in
  let c, t = instance_constructor cl args in
  let term = it_mkLambda_or_LetIn (Option.get c) ctx in
  let typ = it_mkProd_or_LetIn t ctx in
  let cst = declare_constant id term (Some typ) poly evd (IsDefinition Instance) in
  let inst = new_instance (fst cl) Hints.empty_hint_info true poly (Globnames.ConstRef cst) in
    add_instance inst; mkConst cst

let coq_unit = lazy (init_reference ["Coq";"Init";"Datatypes"] "unit")
let coq_tt = lazy (init_reference ["Coq";"Init";"Datatypes"] "tt")
let coq_Empty = lazy (init_reference ["Coq";"Init";"Datatypes"] "Empty_set")

let coq_True = lazy (init_reference ["Coq";"Init";"Logic"] "True")
let coq_I = lazy (init_reference ["Coq";"Init";"Logic"] "I")
let coq_False = lazy (init_reference ["Coq";"Init";"Logic"] "False")

let coq_prod = init_constant ["Coq";"Init";"Datatypes"] "prod"
let coq_pair = init_constant ["Coq";"Init";"Datatypes"] "pair"

let coq_zero = lazy (gen_constant ["Init"; "Datatypes"] "O")
let coq_succ = lazy (gen_constant ["Init"; "Datatypes"] "S")
let coq_nat = lazy (gen_constant ["Init"; "Datatypes"] "nat")

let rec coq_nat_of_int = function
  | 0 -> Lazy.force coq_zero
  | n -> mkApp (Lazy.force coq_succ, [| coq_nat_of_int (pred n) |])

let rec int_of_coq_nat c = 
  match kind_of_term c with
  | App (f, [| arg |]) -> succ (int_of_coq_nat arg)
  | _ -> 0

let fresh_id_in_env avoid id env =
  Namegen.next_ident_away_in_goal id (avoid@ids_of_named_context (named_context env))

let fresh_id avoid id gl =
  fresh_id_in_env avoid id (pf_env gl)

let coq_eq = Lazy.from_fun Coqlib.build_coq_eq
let coq_eq_refl = lazy ((Coqlib.build_coq_eq_data ()).Coqlib.refl)

let coq_heq = lazy (Coqlib.coq_reference "mkHEq" ["Logic";"JMeq"] "JMeq")
let coq_heq_refl = lazy (Coqlib.coq_reference "mkHEq" ["Logic";"JMeq"] "JMeq_refl")

let coq_fix_proto = lazy (init_reference ["Equations";"Init"] "fixproto")

let coq_Id = lazy (init_reference ["Equations";"Init"] "Id")
let coq_Id_refl = lazy (init_reference ["Equations";"Init"] "id_refl")
			 

type logic_ref = Globnames.global_reference lazy_t
							       
type logic = {
  logic_eqty : logic_ref;
  logic_eqrefl: logic_ref;
  logic_sort : sorts_family;
  logic_zero : logic_ref;
  logic_one : logic_ref;
  logic_one_val : logic_ref;
  (* logic_prod : logic_ref; *)
  (* logic_pair : logic_ref; *)
  (* logic_fst : logic_ref; *)
  (* logic_snd : logic_ref; *)
}

let prop_logic =
  { logic_eqty = coq_eq; logic_eqrefl = coq_eq_refl; logic_sort = InProp;
    logic_zero = coq_False;
    logic_one = coq_True; logic_one_val = coq_I;
    

  }
  
let type_logic =
  { logic_eqty = coq_Id; logic_eqrefl = coq_Id_refl; logic_sort = InType;
    logic_zero = coq_Empty; logic_one = coq_unit; logic_one_val = coq_tt }
  
let logic = ref prop_logic
	     
let set_logic l = logic := l
	     
let get_sort () = !logic.logic_sort
let get_eq () = (!logic).logic_eqty
let get_eq_refl () = (!logic).logic_eqrefl
let get_one () = (!logic).logic_one
let get_one_prf () = (!logic).logic_one_val
let get_zero () = (!logic).logic_zero

let fresh_logic_sort evd =
  let evars, sort = Evd.fresh_sort_in_family (Global.env ()) !evd (get_sort ()) in
  evd := evars; mkSort sort

let mkapp env evdref t args =
  let evd, c = Evd.fresh_global env !evdref (Lazy.force t) in
  let _ = evdref := evd in
    mkApp (c, args)

let refresh_universes_strict env evd t = 
  let evd', t' = Evarsolve.refresh_universes (Some true) env !evd t in
    evd := evd'; t'

let mkEq env evd t x y = 
  mkapp env evd (get_eq ()) [| refresh_universes_strict env evd t; x; y |]
    
let mkRefl env evd t x = 
  mkapp env evd (get_eq_refl ()) [| refresh_universes_strict env evd t; x |]

let mkHEq env evd t x u y =
  mkapp env evd coq_heq [| refresh_universes_strict env evd t; x;
                           refresh_universes_strict env evd u; y |]
    
let mkHRefl env evd t x =
  mkapp env evd coq_heq_refl
    [| refresh_universes_strict env evd t; x |]

let dummy_loc = Loc.dummy_loc 
type 'a located = 'a Loc.located

let tac_of_string str args =
  Tacinterp.interp (TacArg(dummy_loc, 
			   TacCall(dummy_loc, Qualid (dummy_loc, qualid_of_string str), args)))

let equations_path = ["Equations";"Equations"]

let get_class c =
  let x = Typeclasses.class_of_constr c in
    fst (snd (Option.get x))

type esigma = Evd.evar_map ref

let functional_induction_class evd =
  let evdref = ref evd in
  let cl = init_constant ["Equations";"FunctionalInduction"] "FunctionalInduction" evdref in
  !evdref, get_class cl

let functional_elimination_class evd =
  let evdref = ref evd in
  let cl = init_constant ["Equations";"FunctionalInduction"] "FunctionalElimination" evdref in
  !evdref, get_class cl

let dependent_elimination_class evd =
  get_class
    (init_constant ["Equations";"DepElim"] "DependentEliminationPackage" evd)

let below_path = ["Equations";"Below"]

let coq_wellfounded_class = init_constant ["Equations";"Classes"] "WellFounded"
let coq_wellfounded = init_constant ["Coq";"Init";"Wf"] "well_founded"
let coq_relation = init_constant ["Coq";"Relations";"Relation_Definitions"] "relation"
let coq_clos_trans = init_constant ["Coq";"Relations";"Relation_Operators"] "clos_trans"
let coq_id = init_constant ["Coq";"Init";"Datatypes"] "id"

let list_path = ["Lists";"List"]
let coq_list_ind = init_constant list_path "list"
let coq_list_nil = init_constant list_path "nil"
let coq_list_cons = init_constant list_path "cons"

let coq_noconfusion_class = lazy (init_reference ["Equations";"DepElim"] "NoConfusionPackage")
  
let coq_inacc = lazy (init_reference ["Equations";"DepElim"] "inaccessible_pattern")
let coq_block = lazy (init_reference ["Equations";"DepElim"] "block")
let coq_hide = lazy (init_reference ["Equations";"DepElim"] "hide_pattern")
let coq_add_pattern = lazy (init_reference ["Equations";"DepElim"] "add_pattern")
let coq_end_of_section_id = id_of_string "eos"
let coq_end_of_section_constr = init_constant ["Equations";"DepElim"] "the_end_of_the_section"
let coq_end_of_section = init_constant ["Equations";"DepElim"] "end_of_section"
let coq_end_of_section_ref = lazy (init_reference ["Equations";"DepElim"] "end_of_section")

let coq_notT = init_constant ["Coq";"Init";"Logic_Type"] "notT"
let coq_ImpossibleCall = init_constant ["Equations";"DepElim"] "ImpossibleCall"

let unfold_add_pattern =
  lazy (Tactics.unfold_in_concl [(Locus.AllOccurrences,
			     EvalConstRef (Globnames.destConstRef (Lazy.force coq_add_pattern)))])

let subterm_relation_base = "subterm_relation"

let coq_sigma = lazy (init_reference ["Equations";"Init"] "sigma")
let coq_sigmaI = lazy (init_reference ["Equations";"Init"] "sigmaI")

let init_projection dp i =
  let r = init_reference dp i in
  Names.Projection.make (Globnames.destConstRef r) false
			
let coq_pr1 = lazy (init_projection ["Equations";"Init"] "pr1")
let coq_pr2 = lazy (init_projection ["Equations";"Init"] "pr2")
			    
(* Misc tactics *)


let rec head_of_constr t =
  let t = strip_outer_cast(collapse_appl t) in
    match kind_of_term t with
    | Prod (_,_,c2)  -> head_of_constr c2 
    | LetIn (_,_,_,c2) -> head_of_constr c2
    | App (f,args)  -> head_of_constr f
    | _      -> t

let nowhere = { onhyps = Some []; concl_occs = NoOccurrences }

(* Lifting a [rel_context] by [n]. *)

let lift_rel_contextn k n sign =
  let open Context.Rel in
  let open Declaration in
  let rec liftrec k = function
    | rel::sign -> let (na,c,t) = to_tuple rel in
      of_tuple (na,Option.map (liftn n k) c,liftn n k t)::(liftrec (k-1) sign)
    | [] -> []
  in
  liftrec (Context.Rel.length sign + k) sign

let lift_context n sign = lift_rel_contextn 0 n sign

let lift_list l = List.map (lift 1) l

(* let compute_params cst =  *)
(*   let body = constant_value (Global.env ()) cst in *)
(*   let init, n, c =  *)
(*     let ctx, body =  *)
(*       match kind_of_term body with *)
(*       | Lambda _ -> decompose_lam_assum c  *)
(*       | _ -> [], c *)
(*     in *)
(*       (interval 0 (List.length ctx),  *)
(*       List.length ctx, body) *)
(*   in *)
(*   let params_of_args pars n args = *)
(*     Array.fold_left *)
(*       (fun (pars, acc) x -> *)
(* 	match pars with *)
(* 	| [] -> (pars, acc) *)
(* 	| par :: pars -> *)
(* 	    if isRel x then *)
(* 	      if n + par = destRel x then *)
(* 		(pars, par :: acc) *)
(* 	      else (pars, acc) *)
(* 	    else (pars, acc)) *)
(*       (pars, []) args *)
(*   in *)
(*   let rec aux pars n c = *)
(*     match kind_of_term c with *)
(*     | App (f, args) -> *)
(* 	if f = mkConst cst then *)
(* 	  let _, pars' = params_of_args pars n args in *)
(* 	    pars' *)
(* 	else pars *)
(*     | _ -> pars *)
(*   in aux init n c *)



let unfold_head env (ids, csts) c = 
  let rec aux c = 
    match kind_of_term c with
    | Var id when Idset.mem id ids ->
	(match Environ.named_body id env with
	| Some b -> true, b
	| None -> false, c)
    | Const (cst,_ as c) when Cset.mem cst csts ->
	true, Environ.constant_value_in env c
    | App (f, args) ->
	(match aux f with
	| true, f' -> true, Reductionops.whd_betaiota Evd.empty (mkApp (f', args))
	| false, _ -> 
	    let done_, args' = 
	      Array.fold_left_i (fun i (done_, acc) arg -> 
		if done_ then done_, arg :: acc 
		else match aux arg with
		| true, arg' -> true, arg' :: acc
		| false, arg' -> false, arg :: acc)
		(false, []) args
	    in 
	      if done_ then true, mkApp (f, Array.of_list (List.rev args'))
	      else false, c)
    | _ -> 
	let done_ = ref false in
	let c' = map_constr (fun c -> 
	  if !done_ then c else 
	    let x, c' = aux c in
	      done_ := x; c') c
	in !done_, c'
  in aux c

open Auto
open CErrors

let autounfold_first db cl gl =
  let st =
    List.fold_left (fun (i,c) dbname -> 
      let db = try Hints.searchtable_map dbname 
	with Not_found -> errorlabstrm "autounfold" (str "Unknown database " ++ str dbname)
      in
      let (ids, csts) = Hints.Hint_db.unfolds db in
	(Idset.union ids i, Cset.union csts c)) (Idset.empty, Cset.empty) db
  in
  let did, c' = unfold_head (pf_env gl) st
    (match cl with Some (id, _) -> pf_get_hyp_typ gl id | None -> pf_concl gl) 
  in
    if did then
      match cl with
      | Some hyp -> Proofview.V82.of_tactic (change_in_hyp None (make_change_arg c') hyp) gl
      | None -> Proofview.V82.of_tactic (convert_concl_no_check c' DEFAULTcast) gl
    else tclFAIL 0 (str "Nothing to unfold") gl

type hintdb_name = string

let rec db_of_constr c = match kind_of_term c with
  | Const (c,_) -> string_of_label (con_label c)
  | App (c,al) -> db_of_constr c
  | _ -> assert false

let dbs_of_constrs = map db_of_constr

(** Bindings to Coq *)

let below_tactics_path =
  make_dirpath (List.map id_of_string ["Below";"Equations"])

let below_tac s =
  make_kn (MPfile below_tactics_path) (make_dirpath []) (mk_label s)

let tacident_arg h =
  Reference (Ident (dummy_loc,h))

let tacvar_arg h =
  let ipat = Genarg.in_gen (Genarg.rawwit Constrarg.wit_intro_pattern) 
    (dummy_loc, Misctypes.IntroNaming (Misctypes.IntroIdentifier h)) in
    TacGeneric ipat

let rec_tac h h' = 
  TacArg(dummy_loc, TacCall(dummy_loc, 
    Qualid (dummy_loc, qualid_of_string "Equations.Below.rec"),
    [tacvar_arg h'; ConstrMayEval (Genredexpr.ConstrTerm h)]))

let rec_wf_tac h h' rel = 
  TacArg(dummy_loc, TacCall(dummy_loc, 
    Qualid (dummy_loc, qualid_of_string "Equations.Subterm.rec_wf_eqns_rel"),
    [tacvar_arg h';
     ConstrMayEval (Genredexpr.ConstrTerm h);
     ConstrMayEval (Genredexpr.ConstrTerm rel)]))

let unfold_recursor_tac () = tac_of_string "Equations.Subterm.unfold_recursor" []

let equations_tac_expr () = 
  (TacArg(dummy_loc, TacCall(dummy_loc, 
   Qualid (dummy_loc, qualid_of_string "Equations.DepElim.equations"), [])))

let solve_rec_tac_expr () =
  (TacArg(dummy_loc, TacCall(dummy_loc, 
   Qualid (dummy_loc, qualid_of_string "Equations.Equations.solve_rec"), [])))

let equations_tac () = tac_of_string "Equations.DepElim.equations" []

let set_eos_tac () = tac_of_string "Equations.DepElim.set_eos" []
    
let solve_rec_tac () = tac_of_string "Equations.Equations.solve_rec" []

let find_empty_tac () = tac_of_string "Equations.DepElim.find_empty" []

let pi_tac () = tac_of_string "Equations.Subterm.pi" []

let noconf_tac () = tac_of_string "Equations.NoConfusion.solve_noconf" []

let eqdec_tac () = tac_of_string "Equations.EqDecInstances.eqdec_proof" []

let simpl_equations_tac () = tac_of_string "Equations.DepElim.simpl_equations" []

let reference_of_global c =
  Qualid (dummy_loc, Nametab.shortest_qualid_of_global Idset.empty c)

let mp = MPfile (DirPath.make (List.map Id.of_string ["DepElim"; "Equations"]))
let solve_equation = KerName.make mp DirPath.empty (Label.make "solve_equation")

open Names
open Tacexpr
open Misctypes

let solve_equation_tac (c : Globnames.global_reference) =
  let var = Id.of_string "x" in
  let solve_equation = ArgArg (dummy_loc, solve_equation) in
  let val_reference = Geninterp.val_tag (Genarg.topwit Constrarg.wit_reference) in
  let c = Geninterp.Val.inject val_reference c in
  let ist = Tacinterp.default_ist () in
  let ist = Geninterp.{ ist with lfun = Id.Map.add var c ist.lfun } in
  let var = Reference (ArgVar (dummy_loc, var)) in
  let tac = TacArg (dummy_loc, TacCall (dummy_loc, solve_equation, [var])) in
  Tacinterp.eval_tactic_ist ist tac

let impossible_call_tac c = Tacintern.glob_tactic
  (TacArg(dummy_loc,TacCall(dummy_loc,
  Qualid (dummy_loc, qualid_of_string "Equations.DepElim.impossible_call"),
  [Reference (reference_of_global c)])))

let depelim_tac h = tac_of_string "Equations.DepElim.depelim"
  [tacident_arg h]

let do_empty_tac h = tac_of_string "Equations.DepElim.do_empty"
  [tacident_arg h]

let depelim_nosimpl_tac h = tac_of_string "Equations.DepElim.depelim_nosimpl"
  [tacident_arg h]

let simpl_dep_elim_tac () = tac_of_string "Equations.DepElim.simpl_dep_elim" []

let depind_tac h = tac_of_string "Equations.DepElim.depind"
  [tacident_arg h]

let mkNot t =
  mkApp (Coqlib.build_coq_not (), [| t |])

let mkNot t =
  mkApp (Coqlib.build_coq_not (), [| t |])

open Context.Rel.Declaration

let mkProd_or_subst decl c =
  match get_value decl with
    | None -> mkProd (get_name decl, get_type decl, c)
    | Some b -> subst1 b c

let mkProd_or_clear decl c =
  if not (dependent (mkRel 1) c) then
    subst1 mkProp c
  else mkProd_or_LetIn decl c

let it_mkProd_or_clear ty ctx = 
  fold_left (fun c d -> mkProd_or_clear d c) ty ctx
      
let mkLambda_or_subst decl c =
  match get_value decl with
    | None -> mkLambda (get_name decl, get_type decl, c)
    | Some b -> subst1 b c

let mkLambda_or_subst_or_clear decl c =
  let (na,body,t) = to_tuple decl in
  match body with
  | None when dependent (mkRel 1) c -> mkLambda (na, t, c)
  | None -> subst1 mkProp c
  | Some b -> subst1 b c

let mkProd_or_subst_or_clear decl c =
  let (na,body,t) = to_tuple decl in
  match body with
  | None when dependent (mkRel 1) c -> mkProd (na, t, c)
  | None -> subst1 mkProp c
  | Some b -> subst1 b c

let it_mkProd_or_subst ty ctx = 
  nf_beta Evd.empty (List.fold_left 
		       (fun c d -> whd_betalet Evd.empty (mkProd_or_LetIn d c)) ty ctx)

let it_mkProd_or_clean ty ctx =
  let open Context.Rel.Declaration in
  nf_beta Evd.empty (List.fold_left 
		       (fun c d -> whd_betalet Evd.empty 
			 (if (get_name d) == Anonymous then subst1 mkProp c
			  else (mkProd_or_LetIn d c))) ty ctx)

let it_mkLambda_or_subst ty ctx = 
  whd_betalet Evd.empty
    (List.fold_left (fun c d -> mkLambda_or_LetIn d c) ty ctx)

let it_mkLambda_or_subst_or_clear ty ctx = 
  (List.fold_left (fun c d -> mkLambda_or_subst_or_clear d c) ty ctx)

let it_mkProd_or_subst_or_clear ty ctx = 
  (List.fold_left (fun c d -> mkProd_or_subst_or_clear d c) ty ctx)


let lift_constrs n cs = map (lift n) cs

let ids_of_constr ?(all=false) vars c =
  let rec aux vars c =
    match kind_of_term c with
    | Var id -> Idset.add id vars
    | App (f, args) -> 
	(match kind_of_term f with
	| Construct ((ind,_),_)
	| Ind (ind, _) ->
            let (mib,mip) = Global.lookup_inductive ind in
	      Array.fold_left_from
		(if all then 0 else mib.Declarations.mind_nparams)
		aux vars args
	| _ -> fold_constr aux vars c)
    | _ -> fold_constr aux vars c
  in aux vars c
    
let decompose_indapp f args =
  match kind_of_term f with
  | Construct ((ind,_),_) 
  | Ind (ind,_) ->
      let (mib,mip) = Global.lookup_inductive ind in
      let first = mib.Declarations.mind_nparams_rec in
      let pars, args = Array.chop first args in
	mkApp (f, pars), args
  | _ -> f, args

let e_conv env evdref t t' =
  try let sigma, b = Reductionops.infer_conv env !evdref ~pb:Reduction.CONV t t' in
      if b then (evdref := sigma; true) else b
  with Reduction.NotConvertible -> false

      
let deps_of_var id env =
  Environ.fold_named_context
    (fun _ decl (acc : Idset.t) ->
       let n, b, t = Context.Named.Declaration.to_tuple decl in
      if Option.cata (occur_var env id) false b || occur_var env id t then
	Idset.add n acc
      else acc)
    env ~init:Idset.empty
    
let idset_of_list =
  List.fold_left (fun s x -> Idset.add x s) Idset.empty

let pr_smart_global = Pptactic.pr_or_by_notation pr_reference
let string_of_smart_global = function
  | Misctypes.AN ref -> string_of_reference ref
  | Misctypes.ByNotation (loc, s, _) -> s

let ident_of_smart_global x = 
  id_of_string (string_of_smart_global x)

let pf_get_type_of               = pf_reduce Retyping.get_type_of
  
let move_after_deps id c =
  let open Context.Named.Declaration in
  let enter gl =
    let gl = Proofview.Goal.assume gl in
    let hyps = Proofview.Goal.hyps gl in
    let deps = collect_vars c in
    let iddeps = 
      collect_vars (Tacmach.New.pf_get_hyp_typ id gl) in
    let deps = Id.Set.diff deps iddeps in
    let find decl = Id.Set.mem (get_id decl) deps in
    let first = 
      match snd (List.split_when find (List.rev hyps)) with
      | a :: _ -> get_id a
      | [] -> errorlabstrm "move_before_deps"
        Pp.(str"Found no hypothesis on which " ++ pr_id id ++ str" depends")
    in
    Tactics.move_hyp id (Misctypes.MoveAfter first)
  in Proofview.Goal.enter { Proofview.Goal.enter = enter }

let observe s tac = 
  let open Proofview in
  let open Proofview.Notations in
  if not !debug then tac
  else
    fun gls ->
    Feedback.msg_debug (str"Applying " ++ str s ++ str " on " ++ Printer.pr_goal gls);
    to82
      (Proofview.tclORELSE
         (Proofview.tclTHEN
            (of82 tac)
            (Proofview.numgoals >>= fun gls ->
             if gls = 0 then (Feedback.msg_debug (str "succeeded"); Proofview.tclUNIT ())
             else
               (of82
                  (fun gls -> Feedback.msg_debug (str "Subgoal: " ++ Printer.pr_goal gls);
                           Evd.{ it = [gls.it]; sigma = gls.sigma }))))
         (fun iexn -> Feedback.msg_debug (str"Failed with: " ++
                                Coqloop.print_toplevel_error iexn);
                   Proofview.tclUNIT ())) gls

(** Compat definitions *)

type rel_context = Context.Rel.t
type rel_declaration = Context.Rel.Declaration.t
type named_declaration = Context.Named.Declaration.t
type named_context = Context.Named.t

let extended_rel_vect n ctx =
  Context.Rel.to_extended_vect n ctx
let extended_rel_list n ctx =
  Context.Rel.to_extended_list n ctx
let to_tuple = Context.Rel.Declaration.to_tuple
let to_named_tuple = Context.Named.Declaration.to_tuple
let of_tuple = Context.Rel.Declaration.of_tuple
let of_named_tuple = Context.Named.Declaration.of_tuple
let to_context c =
  List.map of_tuple c

let localdef c = LocalDefEntry c
let localassum c = LocalAssumEntry c

let get_type = Context.Rel.Declaration.get_type
let get_value = Context.Rel.Declaration.get_value
let get_name = Context.Rel.Declaration.get_name
let get_named_type = Context.Named.Declaration.get_type
let get_named_value = Context.Named.Declaration.get_value
let make_assum n t = Context.Rel.Declaration.LocalAssum (n, t)
let make_def n b t = 
  match b with
  | None -> Context.Rel.Declaration.LocalAssum (n, t)
  | Some b -> Context.Rel.Declaration.LocalDef (n, b, t)

let make_named_def n b t = 
  match b with
  | None -> Context.Named.Declaration.LocalAssum (n, t)
  | Some b -> Context.Named.Declaration.LocalDef (n, b, t)

open Context.Rel.Declaration

let lookup_rel = Context.Rel.lookup

let named_of_rel_context ?(keeplets = false) default l =
  let acc, args, _, ctx =
    List.fold_right
      (fun decl (subst, args, ids, ctx) ->
        let decl = Context.Rel.Declaration.map_constr (substl subst) decl in
	let id = match get_name decl with Anonymous -> default () | Name id -> id in
	let d = Named.Declaration.of_tuple (id, get_value decl, get_type decl) in
	let args = if keeplets || is_local_assum decl then mkVar id :: args else args in
	  (mkVar id :: subst, args, id :: ids, d :: ctx))
      l ([], [], [], [])
  in acc, rev args, ctx

let rel_of_named_context ctx = 
  List.fold_right (fun decl (ctx',subst) ->
      let (n, b, t) = to_named_tuple decl in
      let decl = make_def (Name n) (Option.map (subst_vars subst) b) (subst_vars subst t) in 
      (decl :: ctx', n :: subst)) ctx ([],[])

let empty_hint_info = Hints.empty_hint_info

(* Substitute a list of constrs [cstrs] in rel_context [ctx] for variable [k] and above. *)

let subst_rel_context k cstrs ctx = 
  let (_, ctx') = fold_right 
    (fun decl (k, ctx') ->
      (succ k, map_constr (substnl cstrs k) decl :: ctx'))
    ctx (k, [])
  in ctx'

(* A telescope is a reversed rel_context *)

let subst_telescope cstr ctx = 
  let (_, ctx') = fold_left
    (fun (k, ctx') decl ->
      (succ k, (map_constr (substnl [cstr] k) decl) :: ctx'))
    (0, []) ctx
  in rev ctx'

(* Substitute rel [n] by [c] in [ctx]
   Precondition: [c] is typable in [ctx] using variables 
   above [n] *)
    
let subst_in_ctx (n : int) (c : constr) (ctx : rel_context) : rel_context =
  let rec aux k after = function
    | [] -> []
    | decl :: before ->
	if k == n then (subst_rel_context 0 [lift (-k) c] (rev after)) @ before
	else aux (succ k) (decl :: after) before
  in aux 1 [] ctx

let set_in_ctx (n : int) (c : constr) (ctx : rel_context) : rel_context =
  let rec aux k after = function
    | [] -> []
    | decl :: before ->      
      if k == n then
        (rev after) @ LocalDef (get_name decl, lift (-k) c, get_type decl) :: before
      else aux (succ k) (decl :: after) before
  in aux 1 [] ctx

let get_id decl = Context.Named.Declaration.get_id decl

let fold_named_context_reverse = Context.Named.fold_inside
let map_rel_context = Context.Rel.map
let map_rel_declaration = Context.Rel.Declaration.map_constr
let map_named_declaration = Context.Named.Declaration.map_constr
let map_named_context = Context.Named.map
let lookup_named = Context.Named.lookup

let subst_in_named_ctx (n : Id.t) (c : constr) (ctx : named_context) : named_context =
  let rec aux after = function
    | [] -> []
    | decl :: before ->
       let name = get_id decl in
       if Id.equal name n then (rev after) @ before
       else aux (map_named_declaration (replace_vars [n,c]) decl :: after)
                before
  in aux [] ctx

let pp cmds = Feedback.msg_info cmds

let user_err_loc (loc, s, pp) =
  CErrors.user_err_loc (loc, s, pp)
let error = CErrors.error
let errorlabstrm = CErrors.errorlabstrm
let is_anomaly = CErrors.is_anomaly
let print_error e = CErrors.print e

let nf_betadeltaiota = nf_all
let anomaly ?label pp = CErrors.anomaly ?label pp

let evar_declare sign ev ty ?src evm =
  let evi = Evd.make_evar sign ty in
  let evi = match src with Some src -> { evi with Evd.evar_source = src }
                         | None -> evi in
  Evd.add evm ev evi

let new_evar env evm ?src ty =
  let Sigma.Sigma (term, evm, _) = Evarutil.new_evar env (Sigma.Unsafe.of_evar_map evm) ?src ty in
  Sigma.to_evar_map evm, term

let new_type_evar env evm ?src rigid =
  let Sigma.Sigma (term, evm, _) = Evarutil.new_type_evar env (Sigma.Unsafe.of_evar_map evm) rigid ?src in
  Sigma.to_evar_map evm, term
                           
let to_evar_map = Sigma.to_evar_map
let of_evar_map = Sigma.Unsafe.of_evar_map
let evar_absorb_arguments = Evardefine.evar_absorb_arguments

let hintdb_set_transparency cst b db =
  Hints.add_hints false [db] 
    (Hints.HintsTransparencyEntry ([EvalConstRef cst], b))
                          
