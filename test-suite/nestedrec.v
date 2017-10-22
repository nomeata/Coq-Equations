Require Import Equations.Equations.

Inductive term : Set :=
| Var (n : nat)
| App (t : term) (l : list term).

Equations(noeqns noind) id_term (t : term) : term := {
id_term (Var n) := Var n;
id_term (App t l) := App (id_term t) (id_tlist l) }

Nested id_tlist (t : list term) : list term := {
  id_tlist t := List.map id_term t }.

Next Obligation.
  revert t. fix ft 1 with (ftl (l : term_list) {struct l} : id_term_ind_1 l (id_tlist l));
              (destruct t || destruct l); constructor; auto.
Defined.
