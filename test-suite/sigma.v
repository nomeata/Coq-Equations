Require Import Equations.

Inductive fin : nat -> Set :=
| fz : forall {n}, fin (S n)
| fs : forall {n}, fin n -> fin (S n).
Derive NoConfusion for fin.

Inductive fle : forall {n}, fin n -> fin n -> Prop :=
| flez : forall {n j}, @fle (S n) fz j
| fles : forall {n i j}, fle i j -> @fle (S n) (fs i) (fs j).
Derive Signature for @fle.

Equations(nocomp noind) fle_trans {n : nat} {i j k : fin n} (p : fle i j) (q : fle j k) : fle i k :=
fle_trans ?(S n) _ _ _ flez _ := flez;
fle_trans ?(S n) _ _ _ (fles p') (fles q') := fles (fle_trans p' q').

Require Import EqDec.

Ltac dup :=
  let d := fresh in assert (forall P, P -> P -> P) as d by auto; apply d; clear d.

Ltac case_sigma := destruct 0; intro.

Ltac simplify_sigma :=
  match goal with
  | [ H : existT _ _ _ = existT _ _ _ |- _ ] =>
    apply inj_right_pair in H || apply inj_pair2 in H || inversion H; subst; clear H
  end.

Ltac solve_sigma :=
  repeat simplify_sigma; 
  match goal with
  | [ m := _ : _ |- _ ] => solve [intros; eapply m; eauto]
  end.

Lemma foo : (let target := 6 in
                                let branches := 2 in
                                let m_0 := 1 in
                                let m_1 :=
                                  λ
                                  (fle_trans : fix_proto
                                                 (∀ (n : nat) (i j k : fin n), fle i j → fle j k → fle i k))
                                  (n : nat) (i0 i j : fin n) (f : fle i0 i) 
                                  (f0 : fle i j), fles (fle_trans n i0 i j f f0) in
                                fix_proto (∀ (n : nat) (i j k : fin n), fle i j → fle j k → fle i k)
                                → ∀ (n0 : nat) (i0 j0 : fin n0) (k : fin (S n0)),
                                  fle i0 j0 → fle (fs j0) k → fle (fs i0) k).
Proof.
  intros target branches m_0 m_1.
  do 7 intro.

  dup.

  generalize_eqs H1; do_case H1; solve_method idtac.
  generalize sigma H1; case_sigma; solve_sigma.
Defined.

Lemma bar : (let target := 5 in
 let branches := 2 in
 let m_0 :=
   λ (_ : fix_proto (∀ (n : nat) (i j k : fin n), fle i j → fle j k → fle i k)) 
   (n0 : nat) (j0 k : fin (S n0)) (_ : fle j0 k), @flez n0 in
 let m_1 :=
   foo
   :fix_proto (∀ (n : nat) (i j k : fin n), fle i j → fle j k → fle i k)
    → ∀ (n0 : nat) (i0 j0 : fin n0) (k : fin (S n0)), fle i0 j0 → fle (fs j0) k → fle (fs i0) k in
 fix_proto (∀ (n : nat) (i j k : fin n), fle i j → fle j k → fle i k)
 → ∀ (n : nat) (i j k : fin n), fle i j → fle j k → fle i k).
Proof.
  intros target branches m_0 m_1.
  do 6 intro.

  generalize sigma H0; case_sigma; solve_sigma.
Defined.