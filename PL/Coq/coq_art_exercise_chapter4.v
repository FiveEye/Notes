Require Import ZArith.
Section section_for_chapter_4.

(* 4.1 p70 *)

(* 4.2 p82 *)

(* 4.3 p85 *)

Section A_declared.
Variable (A:Set) (P Q:A->Prop) (R:A->A->Prop).

Theorem all_perm : (forall a b : A, R a b)->forall a b : A, R b a.
Proof.
intros. apply H.
Qed.

Theorem all_imp_dist: (forall a:A, P a -> Q a)->(forall a:A, P a)->forall a:A, Q a.
Proof.
intros. apply H. apply H0.
Qed.

Theorem all_delta : (forall a b:A, R a b)->forall a:A, R a a.
Proof.
intros. apply H.
Qed.

End A_declared.

(* 4.4 p88 *)

Definition id' : forall A:Set, A->A.
intros.
assumption.
Qed.

Print id'.

Definition diag : forall A B:Set, (A->A->B)->A->B := fun A B f a => f a a.

Definition permute: forall A B C:Set, (A->B->C)->B->A->C := fun A B C f b a => f a b.

Definition f_nat_Z: forall A:Set, (nat->A)->Z->A := fun A f z => f (Z.to_nat  z).

(* 4.5 p89 *)
Theorem all_perm' : forall (A : Type) (P : A -> A -> Prop),
  (forall (x y : A), P x y) -> forall (x y : A), P y x.
Proof.
intros.
apply H.
Qed.

Theorem resolution : forall (A : Type) (P Q R S : A->Prop),
  (forall (a : A), Q a -> R a -> S a) ->
  (forall (b : A), P b -> Q b) ->
  (forall (c : A), P c -> R c -> S c).
Proof.
intros.
apply H;[apply H0; assumption | assumption].
Qed.

End section_for_chapter_4.