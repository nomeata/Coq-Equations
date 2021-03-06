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
open Globnames
open Reductionops
open Typeops
open Type_errors
open Pp
open Proof_type
open Glob_term
open Retyping
open Pretype_errors
open Evarutil
open Evarconv
open List
open Libnames
open Topconstr
open Entries
open Constrexpr
open Vars
open Tacexpr
open Tactics
open Tacticals
open Tacmach
open Context
open Evd
open Evarutil
open Evar_kinds
open Equations_common
open Depelim
open Printer
open Ppconstr
open Decl_kinds
open Constrintern

open Syntax
open Covering
open Splitting


module PathOT =
  struct
    type t = Covering.path
    let rec compare p p' =
      match p, p' with
      | ev :: p, ev' :: p' ->
         let c = Evar.compare ev ev' in
         if c == 0 then compare p p'
         else c
      | _ :: _, [] -> -1
      | [], _ :: _ -> 1
      | [], [] -> 0
  end

module PathMap = struct

  include Map.Make (PathOT)

  let union f = merge (fun k l r ->
                  match l, r with
                  | Some l, Some r -> f k l r
                  | Some _, _ -> l
                  | _, Some _ -> r
                  | _, _ -> l)
end

type where_map = (constr * Names.Id.t * splitting) Evar.Map.t

type equations_info = {
 equations_id : Names.Id.t;
 equations_where_map : where_map;
 equations_f : Constr.constr;
 equations_prob : Covering.context_map;
 equations_split : Covering.splitting }

type ind_info = {
  term_info : term_info;
  pathmap : (Names.Id.t * Constr.t list) PathMap.t; (* path -> inductive name *)
  wheremap : where_map }

   
let find_helper_info info f =
  try List.find (fun (ev', arg', id') ->
	 Globnames.eq_gr (Nametab.locate (qualid_of_ident id')) (global_of_constr f))
	info.helpers_info
  with Not_found -> anomaly (str"Helper not found while proving induction lemma.")

let below_transparent_state () =
  Hints.Hint_db.transparent_state (Hints.searchtable_map "Below")

let simpl_star = 
  tclTHEN (to82 simpl_in_concl) (onAllHyps (fun id -> to82 (simpl_in_hyp (id, Locus.InHyp))))

let eauto_with_below ?depth l =
  to82 (Class_tactics.typeclasses_eauto ~depth
    ~st:(below_transparent_state ()) (l@["subterm_relation"; "Below"; "rec_decision"]))

let wf_obligations_base info =
  info.base_id ^ "_wf_obligations"

let simp_eqns l =
  tclREPEAT (tclTHENLIST [Proofview.V82.of_tactic 
			     (Autorewrite.autorewrite (Tacticals.New.tclIDTAC) l);
			  (* simpl_star; Autorewrite.autorewrite tclIDTAC l; *)
			  tclTRY (eauto_with_below l)])

let simp_eqns_in clause l =
  tclREPEAT (tclTHENLIST 
		[Proofview.V82.of_tactic
		    (Autorewrite.auto_multi_rewrite l clause);
		 tclTRY (eauto_with_below l)])

let autorewrites b = 
  tclREPEAT (Proofview.V82.of_tactic (Autorewrite.autorewrite Tacticals.New.tclIDTAC [b]))

let autorewrite_one b =
  let rew_rules = Autorewrite.find_rewrites b in
  let rec aux rules =
    match rules with
    | [] -> Tacticals.New.tclFAIL 0 (str"Couldn't rewrite")
    | r :: rules ->
       let global = global_of_constr r.Autorewrite.rew_lemma in
       let tac = Tacticals.New.pf_constr_of_global global
          (if r.Autorewrite.rew_l2r then Equality.rewriteLR else Equality.rewriteRL)
       in
       Proofview.tclOR
         (if !debug then
            (Proofview.Goal.nf_enter
               Proofview.Goal.{
               enter = fun gl -> let concl = Proofview.Goal.concl gl in
                                 Feedback.msg_debug (str"Trying " ++ pr_global global ++ str " on " ++
                                                       pr_constr concl);
                                 tac })
          else tac)
         (fun e -> if !debug then Feedback.msg_debug (str"failed"); aux rules)
  in Proofview.V82.of_tactic (aux rew_rules)

(** fix generalization *)

let rec mk_holes env sigma = function
| [] -> (sigma, [])
| arg :: rem ->
  let (sigma, arg) = Equations_common.new_evar env sigma arg in
  let (sigma, rem) = mk_holes env sigma rem in
  (sigma, arg :: rem)

let rec check_mutind env sigma k cl = match kind_of_term (strip_outer_cast cl) with
| Prod (na, c1, b) ->
  if Int.equal k 1 then
    try
      let ((sp, _), u), _ = Inductiveops.find_inductive env sigma c1 in
      (sp, u)
    with Not_found -> error "Cannot do a fixpoint on a non inductive type."
  else
    check_mutind (push_rel (Context.Rel.Declaration.LocalAssum (na, c1)) env) sigma (pred k) b
| LetIn (na, c1, t, b) ->
    check_mutind (push_rel (Context.Rel.Declaration.LocalDef (na, c1, t)) env) sigma k b
| _ -> CErrors.user_err_loc (Loc.ghost, "check_mutind",
                             str"Not enough products in " ++ print_constr_env env cl)

open Context.Named.Declaration
(* Refine as a fixpoint *)
let mutual_fix li l =
  let open Proofview in
  let open Notations in
  let mfix env sigma gls =
    let types = List.map (fun ev -> (Evd.evar_concl (Evd.find sigma ev))) gls in
    let env =
      let ctxs = List.map (fun ev -> Evd.evar_context (Evd.find sigma ev)) gls in
      let fst, rest = List.sep_last ctxs in
      if List.for_all (fun y -> Context.Named.equal fst y) rest then
        Environ.push_named_context fst env
      else env
    in
    let li =
      match li with
      | [] ->
         List.mapi (fun i ev -> match Evd.evar_ident ev sigma with
                                | Some id -> id
                                | None -> Id.of_string ("fix_" ^ string_of_int i)) gls
      | l -> List.map Id.of_string l
    in
    let () =
      let lenid = List.length li in
      let lenidxs = List.length l in
      let lengoals = List.length types in
      if not (Int.equal lenid lenidxs && Int.equal lenid lengoals) then
        user_err_loc (Loc.ghost, "mfix",
                         (str "Cannot apply mutual fixpoint, invalid arguments: " ++
                            int lenid ++ (str (String.plural lenid " name")) ++ str " " ++
                            int lenidxs ++ str (if lenidxs == 1 then " index"
                                                else " indices") ++ str" and " ++
                            int lengoals ++ str(String.plural lengoals " subgoal")))
    in
    let all = CList.map3 (fun id n ar -> (id,n,ar)) li l types in
    let (_, n, ar) = List.hd all in
    let (sp, u) = check_mutind env sigma n ar in
    let rec mk_sign sign = function
      | [] -> sign
      | (f, n, ar) :: oth ->
         let (sp', u')  = check_mutind env sigma n ar in
         if not (eq_mind sp sp') then
           error "Fixpoints should be on the same mutual inductive declaration.";
         if try ignore (lookup_named f sign); true with Not_found -> false then
           user_err_loc (Loc.ghost, "Logic.prim_refiner",
                    (str "Name " ++ pr_id f ++ str " already used in the environment"));
         mk_sign ((LocalAssum (f, ar)) :: sign) oth
    in
    let sign = mk_sign (Environ.named_context env) all in
    let idx = Array.map_of_list pred l in
    let nas = Array.map_of_list (fun id -> Name id) li in
    let body = ref (fun i -> assert false) in
    let one_body =
      Refine.refine ~unsafe:true
      ({Sigma.run = fun sigma ->
        let sigma = Sigma.to_evar_map sigma in
        let nenv = Environ.reset_with_named_context (Environ.val_of_named_context sign) env in
        let (sigma, evs) = mk_holes nenv sigma types in
        let evs = Array.map_of_list (Vars.subst_vars (List.rev li)) evs in
        let types = Array.of_list types in
        let decl = (nas,types,evs) in
        let () = body := (fun i -> mkFix ((idx,i),decl)) in
        Sigma.here (!body 0) (Sigma.Unsafe.of_evar_map sigma)})
    in
    let other_body i =
      Refine.refine ~unsafe:true
      ({Sigma.run = fun sigma -> Sigma.here (!body (succ i)) sigma})
    in
    tclDISPATCH (one_body :: List.init (Array.length idx - 1) other_body)
  in
  tclENV >>= fun env ->
  tclEVARMAP >>= fun sigma ->
  Unsafe.tclGETGOALS >>= mfix env sigma


let find_helper_arg info f args =
  let (ev, arg, id) = find_helper_info info f in
    ev, arg, args.(arg)
      
let find_splitting_var pats var constrs =
  let rec find_pat_var p c =
    match p, decompose_app c with
    | PRel i, (c, l) when i = var -> Some (destVar c)
    | PCstr (c, ps), (f,l) -> aux ps l
    | _, _ -> None
  and aux pats constrs =
    List.fold_left2 (fun acc p c ->
      match acc with None -> find_pat_var p c | _ -> acc)
      None pats constrs
  in
    Option.get (aux (rev pats) constrs)

let rec intros_reducing gl =
  let concl = pf_concl gl in
    match kind_of_term concl with
    | LetIn (_, _, _, _) -> tclTHEN (to82 hnf_in_concl) intros_reducing gl
    | Prod (_, _, _) -> tclTHEN (to82 intro) intros_reducing gl
    | _ -> tclIDTAC gl
  
let cstrtac info =
  tclTHENLIST [to82 (any_constructor false None)]

let destSplit = function
  | Split (_, _, _, splits) -> Some splits
  | _ -> None

let destRefined = function
  | Refined (_, _, s) -> Some s
  | _ -> None

let destWheres = function
  | Compute (_, wheres, _, _) -> Some wheres
  | _ -> None

let map_opt_split f s =
  match s with
  | None -> None
  | Some s -> f s

let solve_ind_rec_tac info =
  Tacticals.New.pf_constr_of_global info.term_id (fun c ->
  Proofview.tclTHEN (Tactics.pose_proof Anonymous c)
                    (of82 (eauto_with_below ~depth:10 [info.base_id; wf_obligations_base info])))

let change_in_app f args idx arg =
  let args' = Array.copy args in
  args'.(idx) <- arg;
  mkApp (f, args')

let hyps_after sigma pos args =
  let args' = Array.sub args (pos + 1) (Array.length args - (pos + 1)) in
  Array.fold_right (fun c acc -> ids_of_constr ~all:true acc c) args' Id.Set.empty

let rec aux_ind_fun info chop unfs unfids = function
  | Split ((ctx,pats,_), var, _, splits) ->
     let unfs =
       let unfs = map_opt_split destSplit unfs in
       match unfs with
       | None -> fun i -> None
       | Some f -> fun i -> f.(i)
     in
     observe "split"
     (tclTHEN_i
       (fun gl ->
	match kind_of_term (pf_concl gl) with
	| App (ind, args) -> 
	   let pats' = List.drop_last (Array.to_list args) in
           let pats' = 
             if fst chop < 0 then pats'
             else snd (List.chop (fst chop) pats') in
	   let pats = filter (fun x -> not (hidden x)) pats in
	   let id = find_splitting_var pats var pats' in
	      to82 (depelim_nosimpl_tac id) gl
	| _ -> tclFAIL 0 (str"Unexpected goal in functional induction proof") gl)
	(fun i -> 
	  match splits.(pred i) with
	  | None -> to82 (simpl_dep_elim_tac ())
	  | Some s ->
	      tclTHEN (to82 (simpl_dep_elim_tac ()))
		(aux_ind_fun info chop (unfs (pred i)) unfids s)))
	  
  | Valid ((ctx, _, _), ty, substc, tac, valid, rest) ->
     observe "valid"
    (tclTHEN (to82 intros)
      (tclTHEN_i tac (fun i -> let _, _, subst, invsubst, split = nth rest (pred i) in
				 tclTHEN (to82 (Lazy.force unfold_add_pattern))
				   (aux_ind_fun info chop unfs unfids split))))

  | RecValid (id, cs) -> aux_ind_fun info chop unfs unfids cs
      
  | Refined ((ctx, _, _), refinfo, s) -> 
    let unfs = map_opt_split destRefined unfs in
    let id = pi1 refinfo.refined_obj in
    let elimtac gl =
      match kind_of_term (pf_concl gl) with
      | App (ind, args) ->
         let before, last_arg = CArray.chop (Array.length args - 1) args in
         let f, fargs = destApp last_arg.(0) in
         let _, pos, elim = find_helper_arg info.term_info f fargs in
         let id = pf_get_new_id id gl in
         let hyps = Id.Set.elements (hyps_after (project gl) (pos - snd chop) before) in
         let occs = Some (List.map (fun h -> (Locus.AllOccurrences, h), Locus.InHyp) hyps) in
         let occs = Locus.{ onhyps = occs; concl_occs = NoOccurrences } in
         let newconcl =
           let fnapp = change_in_app f fargs pos (mkVar id) in
           let indapp = change_in_app ind before (pos - snd chop) (mkVar id) in
           mkApp (indapp, [| fnapp |])
         in
         tclTHENLIST
          [observe "letin" (to82 (letin_pat_tac None (Name id) ((project gl, project gl), elim) occs));
           observe "convert concl" (to82 (convert_concl_no_check newconcl DEFAULTcast));
           Proofview.V82.of_tactic (clear_body [id]);
           aux_ind_fun info chop unfs unfids s] gl
      | _ -> tclFAIL 0 (str"Unexpected refinement goal in functional induction proof") gl
    in
    observe "refine"
    (tclTHENLIST [ to82 intros;
                   tclTHENLAST (tclTHEN (tclTRY (autorewrite_one info.term_info.base_id))
                                        (cstrtac info.term_info)) (tclSOLVE [elimtac]);
		   to82 (solve_ind_rec_tac info.term_info)])

  | Compute (_, wheres, _, c) ->
    let unfswheres =
      let unfs = map_opt_split destWheres unfs in
      match unfs with
      | None -> List.map (fun _ -> None) wheres
      | Some wheres -> List.map (fun w -> Some w) wheres
    in
    let wheretac = 
      if not (List.is_empty wheres) then
        let wheretac acc s unfs =
          let where_term, fstchop, unfids, where_nctx = match unfs with
            | None -> s.where_term, fst chop + List.length s.where_nctx, unfids, s.where_nctx
            | Some w ->
               let assoc, unf, split =
                 try Evar.Map.find (List.hd w.where_path) info.wheremap
                 with Not_found -> assert false
               in
               (* msg_debug (str"Unfolded where " ++ str"term: " ++ pr_constr w.where_term ++ *)
               (*              str" type: " ++ pr_constr w.where_type ++ str" assoc " ++ *)
               (*              pr_constr assoc); *)
               assoc, fst chop + List.length w.where_nctx, unf :: unfids, w.where_nctx
          in
          let chop = fstchop, snd chop in
          let wheretac =
            observe "one where"
            (tclTHENLIST [tclTRY (to82 (move_hyp coq_end_of_section_id Misctypes.MoveLast));
                         to82 intros;
                         if Option.is_empty unfs then tclIDTAC
                         else autorewrite_one (info.term_info.base_id ^ "_where");
                         (aux_ind_fun info chop (Option.map (fun s -> s.where_splitting) unfs)
                                      unfids s.where_splitting)])
          in
          let wherepath, args =
            try PathMap.find s.where_path info.pathmap
            with Not_found ->
              error "Couldn't find associated args of where"
          in
          if !debug then
            Feedback.msg_debug (str"Found path " ++ str (Id.to_string wherepath) ++ str" where: " ++
                                  pr_id s.where_id ++ str"term: " ++ pr_constr s.where_term ++
                                  str" instance: " ++ prlist_with_sep spc pr_constr args ++ str" context map " ++
                                  pr_context_map (Global.env ()) s.where_prob);
          let ty =
            let ind = Nametab.locate (qualid_of_ident wherepath) in
            let ctx = pi1 s.where_prob in
            let subst = List.map (fun x -> mkVar (get_id x)) where_nctx in
            let fnapp = applistc (substl subst where_term) (extended_rel_list 0 ctx) in
            let args = List.append subst (extended_rel_list 0 ctx) in
            let app = applistc (Universes.constr_of_global ind) (List.append args [fnapp]) in
            it_mkProd_or_LetIn app ctx
          in
          tclTHEN acc (to82 (assert_by (Name s.where_id) ty (of82 wheretac)))
        in
        let tac = List.fold_left2 wheretac tclIDTAC wheres unfswheres in
        tclTHENLIST [tac;
                     tclTRY (autorewrite_one info.term_info.base_id);
                     cstrtac info.term_info;
                     if Option.is_empty unfs then tclIDTAC
                     else observe "whererev"
                                  (tclTRY (autorewrite_one (info.term_info.base_id ^ "_where_rev")));
                     eauto_with_below []]
      else tclIDTAC
    in
    (match c with
     | REmpty _ -> 
      observe "compute empty"
       (tclTHENLIST [intros_reducing; wheretac; to82 (find_empty_tac ())])
     | RProgram _ ->
      observe "compute "
      (tclTHENLIST
         [intros_reducing;
          tclTRY (autorewrite_one info.term_info.base_id);
          observe "wheretac" wheretac;
          observe "applying compute rule" (cstrtac info.term_info);
          (** Each of the recursive calls result in an assumption. If it
              is a rec call in a where clause to itself we need to
              explicitely rewrite with the unfolding lemma (as the where
              clause induction hypothesis is about the unfolding whereas
              the term itself mentions the original function. *)
          tclMAP (fun i ->
              tclTRY (to82 (Tacticals.New.pf_constr_of_global
                              (Equations_common.global_reference i)
                              Equality.rewriteLR))) unfids;
          (to82 (solve_ind_rec_tac info.term_info))]))

  | Mapping (_, s) -> aux_ind_fun info chop unfs unfids s

let observe_tac s tac =
  let open Proofview in
  let open Proofview.Notations in
  if not !debug then tac
  else
    tclENV >>= fun env ->
    tclEVARMAP >>= fun sigma ->
    Unsafe.tclGETGOALS >>= fun gls ->
    Feedback.msg_debug (str"Applying " ++ str s ++ str " on " ++
                          Printer.pr_subgoals None sigma [] [] [] gls);
    Proofview.tclORELSE
      (Proofview.tclTHEN tac
                         (Proofview.numgoals >>= fun gls ->
                          if gls = 0 then (Feedback.msg_debug (str s ++ str "succeeded");
                                           Proofview.tclUNIT ())
             else
               (of82
                  (fun gls -> Feedback.msg_debug (str "Subgoal: " ++ Printer.pr_goal gls);
                           Evd.{ it = [gls.it]; sigma = gls.sigma }))))
      (fun iexn -> Feedback.msg_debug
                     (str"Failed with: " ++
                        (match fst iexn with
                         | Refiner.FailError (n,expl) ->
                            (str" Fail error " ++ int n ++ str " for " ++ str s ++
                               spc () ++ Lazy.force expl ++
                               str " on " ++
                               Printer.pr_subgoals None sigma [] [] [] gls)
                         | _ -> CErrors.iprint iexn));
                   Proofview.tclUNIT ())

let ind_fun_tac is_rec f info fid split unfsplit progs =
  match is_rec with
  | Some (Syntax.Structural [_]) ->
    let c = constant_value_in (Global.env ()) (Term.destConst f) in
    let i = let (inds, _), _ = Term.destFix c in inds.(0) in
    let recid = add_suffix fid "_rec" in
      (* tclCOMPLETE  *)
      of82 (tclTHENLIST
	  [to82 (set_eos_tac ()); to82 (fix (Some recid) (succ i));
	   onLastDecl (fun decl gl ->
             let (n,b,t) = to_named_tuple decl in
	     let fixprot pats =
               { Sigma.run = fun sigma ->
	       let c = 
		 mkLetIn (Anonymous, Universes.constr_of_global (Lazy.force coq_fix_proto),
			  Universes.constr_of_global (Lazy.force coq_unit), t) in
	       Sigma.here c sigma }
	     in
	     Proofview.V82.of_tactic
	       (change_in_hyp None fixprot (n, Locus.InHyp)) gl);
           to82 intros; aux_ind_fun info (0, 1) None [] split])

  | Some (Structural l) ->
     let open Proofview in
     let open Notations in
     let mutual, nested = List.partition (function (_, StructuralOn _, _) -> true | _ -> false) l in
     let mutannots = List.map (function (_, StructuralOn ann, _) -> ann + 1 | _ -> -1) mutual in
     let mutprogs, nestedprogs =
       List.partition (fun (p,_,e) -> match p.program_rec_annot with
                                      | Some (StructuralOn _) -> true
                                      | _ -> false) progs
     in
     let eauto = Class_tactics.typeclasses_eauto ["funelim"; info.term_info.base_id] in
     let rec splits l =
       match l with
       | [] | _ :: [] -> tclUNIT ()
       | _ :: l -> Tactics.split Misctypes.NoBindings <*> tclDISPATCH [tclUNIT (); splits l]
     in
     let prove_progs progs =
       intros <*>
         tclDISPATCH (List.map (fun (_,_,e) -> (* observe_tac "proving one mutual " *) (of82 (aux_ind_fun info (0, List.length mutual) None [] e.equations_split)))
                               progs)
     in
     let prove_nested =
       tclDISPATCH (List.map (function (_,NestedOn (Some ann),_) -> fix None (ann + 1)
                                     | _ -> tclUNIT ()) nested) <*>
         prove_progs nestedprogs
     in
     let mutfix =
       mutual_fix [] mutannots <*> prove_progs mutprogs
     in
     let mutlen = List.length mutprogs in
     (* let intros_conj len = *)
     (*   if len == 1 then *)
     (*     Tactics.intro *)
     (*   else *)
     (*     Tactics.intros_patterns false *)
     (*     Proofview.Goal.enter (fun gl -> *)
     (*         match concl_kind gl with *)
     (*         | Prod (na, a, b) -> *)
     (*            match kind *)
     (* in *)
     let tac gl =
       let mutprops, nestedprops =
         let rec aux concl i =
           match kind_of_term concl with
             | App (conj, [| a; b |]) ->
                if i == 1 then
                  a, Some b
                else
                  let muts, nested = aux b (pred i) in
                  mkApp (conj, [| a ; muts |]), nested
             | _ -> if i == 1 then concl, None
                    else assert false
         in aux (Goal.concl gl) mutlen
       in
       set_eos_tac () <*>
         (match nestedprops with
          | Some p ->
             assert_before Anonymous (mkProd (Anonymous, mutprops, p)) <*>
               tclDISPATCH
                 [observe_tac "assert mut -> nest first subgoal " (* observe_tac *)
                  (*   "proving mut -> nested" *)
                              (intro <*> observe_tac "spliting nested" (splits nestedprogs) <*> prove_nested);
                  tclUNIT ()]
          | None -> tclUNIT ()) <*>
         assert_before Anonymous mutprops <*>
         tclDISPATCH
           [observe_tac "mutfix"
                        (splits mutprogs <*> tclFOCUS 1 (List.length mutual) mutfix);
            tclUNIT ()] <*>
         (* On the rest of the goals, do the nested proofs *)
         observe_tac "after mut -> nested and mut provable" (eauto ~depth:None)
     in Proofview.Goal.nf_enter ({enter = fun gl -> tac gl})

  | _ -> of82 (tclCOMPLETE (tclTHENLIST
      [to82 (set_eos_tac ()); to82 intros; aux_ind_fun info (0, 0) unfsplit [] split]))


let simpl_except (ids, csts) =
  let csts = Cset.fold Cpred.remove csts Cpred.full in
  let ids = Idset.fold Idpred.remove ids Idpred.full in
    CClosure.RedFlags.red_add_transparent CClosure.all
      (ids, csts)
      
let simpl_of csts =
  let opacify () = List.iter (fun cst -> 
    Global.set_strategy (ConstKey cst) Conv_oracle.Opaque) csts
  and transp () = List.iter (fun cst -> 
    Global.set_strategy (ConstKey cst) Conv_oracle.Expand) csts
  in opacify, transp

let get_proj_eval_ref p =
  match p with
  | LogicalDirect (loc, id) -> EvalVarRef id
  | LogicalProj r -> EvalConstRef r.comp_proj

let prove_unfolding_lemma info where_map proj f_cst funf_cst split unfold_split gl =
  let depelim h = depelim_tac h in
  let helpercsts = List.map (fun (_, _, i) -> fst (destConst (global_reference i)))
			    info.helpers_info in
  let opacify, transp = simpl_of (destConstRef (Lazy.force coq_hidebody) :: helpercsts) in
  let opacified tac gl = opacify (); let res = tac gl in transp (); res in
  let simpltac gl = opacified (to82 (simpl_equations_tac ())) gl in
  let my_simpl = opacified (to82 (simpl_in_concl)) in
  let unfolds = tclTHEN (autounfold_first [info.base_id] None)
    (autounfold_first [info.base_id ^ "_unfold"] None)
  in
  let solve_rec_eq gl =
    match kind_of_term (pf_concl gl) with
    | App (eq, [| ty; x; y |]) ->
	let xf, _ = decompose_app x and yf, _ = decompose_app y in
	  if eq_constr (mkConst f_cst) xf && is_rec_call proj yf then
            let proj_unf = get_proj_eval_ref proj in
	    let unfolds = unfold_in_concl 
	      [((Locus.OnlyOccurrences [1]), EvalConstRef f_cst); 
	       ((Locus.OnlyOccurrences [1]), proj_unf)]
	    in 
	      tclTHENLIST [to82 unfolds; simpltac; to82 (pi_tac ())] gl
	  else to82 reflexivity gl
    | _ -> to82 reflexivity gl
  in
  let solve_eq = tclORELSE (to82 reflexivity) solve_rec_eq in
  let abstract tac = tclABSTRACT None tac in
  let rec aux split unfold_split =
    match split, unfold_split with
    | Split (_, _, _, splits), Split ((ctx,pats,_), var, _, unfsplits) ->
       observe "split"
	(fun gl ->
	  match kind_of_term (pf_concl gl) with
	  | App (eq, [| ty; x; y |]) -> 
	     let f, pats' = decompose_app y in
             let c, unfolds =
                if !Equations_common.ocaml_splitting then
                  let _, _, c, _ = Term.destCase f in c, tclIDTAC
                else
                  List.nth (List.rev pats') (pred var), unfolds
             in
             let id = destVar (fst (decompose_app c)) in
	     let splits = List.map_filter (fun x -> x) (Array.to_list splits) in
	     let unfsplits = List.map_filter (fun x -> x) (Array.to_list unfsplits) in
	       to82 (abstract (of82 (tclTHEN_i (to82 (depelim id))
				               (fun i -> let split = nth splits (pred i) in
                                                      let unfsplit = nth unfsplits (pred i) in
					      tclTHENLIST [unfolds; aux split unfsplit])))) gl
	  | _ -> tclFAIL 0 (str"Unexpected unfolding goal") gl)
	    
    | Valid (_, _, _, _, _, rest), (* Valid ((ctx, _, _), ty, substc, tac, valid, unfrest) -> *) _ ->
       (* FIXME: Valid could take a splitting with more than 1 branch *)
       observe "valid"
               (aux (let (_, _, _, _, split) = List.nth rest 0 in split) unfold_split)
       (* tclTHEN_i tac (fun i -> let _, _, _, _, split = nth rest (pred i) in *)
       (*                      (\* let _, _, _, _, unfsplit = nth unfrest (pred i) in *\) *)
       (*  		    tclTHEN (Lazy.force unfold_add_pattern) (aux split unfold_split)) *)

    | RecValid (id, cs), unfsplit ->
       observe "recvalid"
	       (tclTHEN (to82 (unfold_recursor_tac ())) (aux cs unfsplit))

    | _, Mapping (lhs, s) -> aux split s
       
    | Refined (_, _, s), Refined ((ctx, _, _), refinfo, unfs) ->
	let id = pi1 refinfo.refined_obj in
	let ev = refinfo.refined_ex in
	let rec reftac gl = 
	  match kind_of_term (pf_concl gl) with
	  | App (f, [| ty; term1; term2 |]) ->
	      let f1, arg1 = destApp term1 and f2, arg2 = destApp term2 in
              let _, posa1, a1 = find_helper_arg info f1 arg1
              and ev2, posa2, a2 = find_helper_arg info f2 arg2 in
	      let id = pf_get_new_id id gl in
		if Evar.equal ev2 ev then 
	  	  tclTHENLIST
	  	    [to82 (Equality.replace_by a1 a2
	  		     (of82 (tclTHENLIST [solve_eq])));
	  	     to82 (letin_tac None (Name id) a2 None Locusops.allHypsAndConcl);
	  	     Proofview.V82.of_tactic (clear_body [id]); unfolds; aux s unfs] gl
		else tclTHENLIST [unfolds; simpltac; reftac] gl
	  | _ -> tclFAIL 0 (str"Unexpected unfolding lemma goal") gl
	in
        let reftac = observe "refined" reftac in
	  to82 (abstract (of82 (tclTHENLIST [to82 intros; simpltac; reftac])))
	    
    | Compute (_, wheres, _, RProgram _), Compute (_, unfwheres, _, RProgram c) ->
       let wheretac acc w unfw =
         let assoc, id, _ =
           try Evar.Map.find (List.hd unfw.where_path) where_map
           with Not_found -> assert false
         in
         (* msg_debug (str"Found where: " ++ *)
         (*              pr_id unfw.where_id ++ str"term: " ++ pr_constr unfw.where_term ++ *)
         (*              str " where assoc " ++ pr_constr assoc); *)
         fun gl ->
         let env = pf_env gl in
         let evd = ref (project gl) in
         let ty =
           let ctx = pi1 unfw.where_prob in
           let lhs = mkApp (assoc, extended_rel_vect 0 ctx) in
           let rhs = mkApp (unfw.where_term, extended_rel_vect 0 ctx) in
           let eq = mkEq env evd unfw.where_arity lhs rhs in
           it_mkProd_or_LetIn eq ctx
         in
         let headcst f =
           let f, _ = decompose_app f in
           if isConst f then fst (destConst f)
           else assert false
         in
         let f_cst = headcst assoc and funf_cst = headcst unfw.where_term in
         let unfolds gl =
           let res = to82 (unfold_in_concl
	     [Locus.OnlyOccurrences [1], EvalConstRef f_cst;
	      (Locus.OnlyOccurrences [1], EvalConstRef funf_cst)]) gl in
           (* Global.set_strategy (ConstKey f_cst) Conv_oracle.Opaque; *)
	   (* Global.set_strategy (ConstKey funf_cst) Conv_oracle.Opaque; *)
           res
         in
         let tac =
           let tac =
             of82 (tclTHENLIST [to82 intros; unfolds;
                                (observe "where"
                                         (aux w.where_splitting unfw.where_splitting))])
           in
           assert_by (Name id) ty (of82 (tclTHEN (to82 (keep [])) (to82 (tclABSTRACT (Some id) tac))))
         in
         tclTHENLIST [Refiner.tclEVARS !evd; to82 tac;
                      to82 (Equality.rewriteLR (mkVar id));
                      acc] gl
       in
       let wheretacs =
         assert(List.length wheres = List.length unfwheres);
         List.fold_left2 wheretac tclIDTAC wheres unfwheres
       in
       observe "compute"
               (to82 (abstract (of82 (tclTHENLIST [to82 intros; wheretacs;
                                                   observe "compute rhs" (tclTRY unfolds);
                                                   simpltac; solve_eq]))))

    | Compute (_, _, _, _), Compute ((ctx,_,_), _, _, REmpty id) ->
	let d = nth ctx (pred id) in
	let id = out_name (get_name d) in
	to82 (abstract (depelim id))

    | _, _ -> assert false
  in
    try
      let unfolds = unfold_in_concl
	[Locus.OnlyOccurrences [1], EvalConstRef f_cst; 
	 (Locus.OnlyOccurrences [1], EvalConstRef funf_cst)]
      in
      let res =
	tclTHENLIST 
	  [to82 (set_eos_tac ()); to82 intros; to82 unfolds; my_simpl;
	   (* to82 (unfold_recursor_tac ()); *)
	   (fun gl ->
	     Global.set_strategy (ConstKey f_cst) Conv_oracle.Opaque;
	     Global.set_strategy (ConstKey funf_cst) Conv_oracle.Opaque;
	     aux split unfold_split gl)] gl
      in Global.set_strategy (ConstKey f_cst) Conv_oracle.Expand;
	Global.set_strategy (ConstKey funf_cst) Conv_oracle.Expand;
	res
    with e ->
      Global.set_strategy (ConstKey f_cst) Conv_oracle.Expand;
      Global.set_strategy (ConstKey funf_cst) Conv_oracle.Expand;
      raise e
  

let unfold s = to82 (Tactics.unfold_in_concl [Locus.AllOccurrences, s])

(* let rec mk_app_holes env sigma = function *)
(* | [] -> (sigma, []) *)
(* | decl :: rem -> *)
(*   let (sigma, arg) = Equations_common.new_evar env sigma (Context.Rel.Declaration.get_type decl) in *)
(*   let (sigma, rem) = mk_app_holes env sigma (subst_rel_context 0 [arg] rem) in *)
(*   (sigma, arg :: rem) *)

let goal_sigma gl = Sigma.to_evar_map (Proofview.Goal.sigma gl)

let ind_elim_tac indid inds mutinds info ind_fun =
  let open Proofview in
  let open Notations in
  let open Tacticals.New in
  let eauto = Class_tactics.typeclasses_eauto ["funelim"; info.base_id] in
  let prove_methods c =
    Proofview.Goal.enter {enter = fun gl ->
        let sigma, _ = Typing.type_of (Goal.env gl) (goal_sigma gl) c in
        tclTHENLIST [Proofview.Unsafe.tclEVARS sigma;
                     Tactics.apply c;
                     Tactics.simpl_in_concl;
                     eauto ~depth:None]}
  in
  let rec applyind leninds args =
    Proofview.Goal.nf_enter {enter = fun gl ->
    let env = Goal.env gl in
    let sigma = goal_sigma gl in
    match leninds, kind_of_term (Goal.concl gl) with
    | 0, _ ->
       if mutinds == 1 then
         tclTHENLIST [Tactics.simpl_in_concl; Tactics.intros;
                      prove_methods (Reductionops.nf_beta (goal_sigma gl)
                                                          (applistc indid (List.rev args)))]
       else
         let app = applistc indid (List.rev args) in
         let sigma, ty = Typing.type_of env sigma app in
         let ctx, concl = decompose_prod_assum ty in
         Tactics.simpl_in_concl <*> Tactics.intros <*>
           Tactics.cut concl <*>
           tclDISPATCH
             [tclONCE (Tactics.intro <*>
                         (pf_constr_of_global ind_fun (fun ind_fun ->
                                      Tactics.pose_proof Anonymous ind_fun <*>
                                        eauto ~depth:None)));
              tclONCE (Tactics.apply app <*>
                                Tactics.simpl_in_concl <*> eauto ~depth:None)]


    | _, LetIn (_, b, _, t') ->
       tclTHENLIST [Tactics.convert_concl_no_check (subst1 b t') DEFAULTcast;
                    applyind (pred leninds) (b :: args)]
    | _, Prod (_, _, t') ->
        tclTHENLIST [Tactics.intro;
                     onLastHypId (fun id -> applyind (pred leninds) (mkVar id :: args))]
    | _, _ -> assert false}
  in
  try applyind inds []
  with e -> tclFAIL 0 (Pp.str"exception")
