Require Import Equations.Equations.

Inductive vect : nat -> Type :=
| vnil : vect O
| vcons {n : nat} : nat -> vect n -> vect (S n).

Goal forall n (x y : vect n), existT _ n x = existT _ n x -> True.
Proof.

(*
         (fun (n : nat) (x _ : vect n) =>
 @apply_noConfusion (@sigT nat vect) (NoConfusionPackage_sigT nat vect) (@existT nat vect n x)
   (@existT nat vect n x) (fun _ : @eq (@sigT nat vect) (@existT nat vect n x) (@existT nat vect n x) => True)
   (@eq_simplification_sigma1_dep@{Coq.Init.Specif.7 Coq.Init.Specif.8 Top.19} nat 
      (fun x0 : nat => vect x0) True n n x x
      (@simplification_K_dec nat nat_eqdec n
         (fun e : @eq nat n n =>
          forall _ : @eq ((fun x0 : nat => vect x0) n) (@eq_rect nat n (fun x0 : nat => vect x0) x n e) x, True)
         (fun _ : @eq (vect n) x x => I)))) *)
  intros n x y.
  simplify $-. Show Proof. Show Universes. simplify -. reflexivity. Set Printing Universes. Set Printing All. Qed. Show Proof. simplify -. exact I. Qed. Show Proof. simplify -. Show Proof. Qed. intros _. reflexivity. Qed. Show Proof.
  reflexivity. Set Printing All. Set Printing Universes. Show Proof.
Qed.


Require Import Equations.DepElimDec.

Ltac simplify_one_dep_elim' :=
match goal with
| |- let _ := block in _ => fail 1
| |- _ => simplify ?
| |- ?f ?x = ?g ?y -> _ => let H := fresh in progress (intros H ; injection H ; clear H)
| |- Id (?f ?x) (?g ?y) -> _ => let H := fresh in progress (intros H ; inversion H ; clear H)
| |- forall x, _ => let H := fresh x in intro H
| |- _ => intro
end.

Ltac simplify_dep_elim ::= repeat simplify_one_dep_elim'.

Inductive vect : nat -> Type :=
| vnil : vect O
| vcons {n : nat} : nat -> vect n -> vect (S n).

Derive Signature for vect.

From Equations Require Import EqDec.

Axiom cheat : forall A, A.

Goal forall n (x y : vect n), existT _ n x = existT _ n y -> x = y.
Proof. intros n x y.

set (P1 := forall
    H : @NoConfusion (@sigT nat vect) (NoConfusionPackage_sigT nat vect) (@existT nat vect n x)
          (@existT nat vect n y),
  (fun _ : @eq (@sigT nat vect) (@existT nat vect n x) (@existT nat vect n y) => @eq (vect n) x y)
    (@noConfusion_inv (@sigT nat vect) (NoConfusionPackage_sigT nat vect) (@existT nat vect n x)
       (@existT nat vect n y) H)).
set (P2 := forall
    _ : @eq (sigma nat (fun x : nat => vect x)) (@sigmaI nat (fun x : nat => vect x) n x)
          (@sigmaI nat (fun x : nat => vect x) n y), @eq (vect n) x y).

unify P1 P2.
simplify ${-->}. reflexivity. Show Proof. Qed.




Goal forall n m (x y : vect n), vcons m x = vcons m y -> x = y.
Proof. intros n m x y H. injection H. simplify ?. reflexivity. Qed.


Instance vect_eqdec {n} : EqDec (vect n).
Proof. intros x. induction x. left. now depelim y.
  intro y; depelim y.
  destruct (eq_dec n0 n2); subst.
  destruct (IHx y). subst. Show Proof.
  left. reflexivity.
  right. intro. apply n. injection H. simpdep. reflexivity.
  right. intro. apply n. injection H. simpdep. reflexivity.
Defined.
