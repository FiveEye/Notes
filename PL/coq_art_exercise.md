#My solution for coq'art

##Index
* [Chapter 3](#chapter-3)
* [Chapter 4](#chapter-4)
* [Chapter 5](#chapter-5)
* [Chapter 6](#chapter-6)
* [Chapter 7](#chapter-7)
* [Chapter 9](#chapter-9)
* [Chapter 12](#chapter-12)
* [Chapter 13](#chapter-13)

##Chapter 3

[Source Code](coq_art_exercise_chapter3.v)

<pre>
(* Chapter 3 *)

Section section_for_chapter_3.
Hypotheses (P Q R T : Prop) (H : P -> Q) (H0 : Q -> R) (H1 : (P -> R) -> T -> Q) (H2 : (P -> R) -> T).

(* 3.1 p47 *)

Check ((P -> Q) -> (Q -> R) -> P -> R).

(* 3.2 p52 *)

Lemma id_P : P -> P.
Proof (fun x => x).

Lemma id_PP : (P->P) -> (P->P).
Proof (fun x => x).

Lemma imp_trans : (P->Q) -> (Q->R) -> P -> R.
Proof (fun f0 f1 p => f1 (f0 p)).

Lemma imp_perm : (P->Q->R) -> (Q->P->R).
Proof (fun f => (fun x y => f y x)).

Lemma ignore_Q : (P -> R) -> P -> Q -> R.
Proof (fun f p q => f p).

Lemma delta_imp : (P->P->Q)->P->Q.
Proof (fun f p => f p p).

Lemma delta_impR : (P->Q)->(P->P->Q).
Proof (fun f p => f).
Print delta_impR.

Lemma diamond : (P->Q)->(P->R)->(Q->R->T)->P->T.
Proof (fun f g h p => h (f p) (g p)).

Lemma weak_peirce : ((((P->Q)->P)->P)->Q)->Q.
Proof.
intros.
apply H3.
intros.
apply H4.
assumption.
Qed.
Print weak_peirce.

(* 3.3 p59 redo 3.2 *)

(* 3.4 p61 proof *)

(* 3.5 p63 *)

Theorem cut_example : Q.
Proof.
  cut (P -> R).
  intro H3.
  apply H1. assumption. apply H2. assumption.
  intro. apply H0. apply H. assumption.
Qed.

Print cut_example.

Theorem cut_example' : Q.
Proof.
apply H1. intro. apply H0. apply H. assumption.
apply H2. intro. apply H0. apply H. assumption.
Qed.

Print cut_example'.

End section_for_chapter_3.
</pre>

##Chapter 4

[Source Code](coq_art_exercise_chapter4.v)

<pre>
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
</pre>

##Chapter 5
<pre>

</pre>

##Chapter 6

There are too many exercises in this chapter, so I create a single file for chapter 6.

[Source Code](coq_art_exercise_chapter6.v)

##Chapter 7

[Source Code](coq_art_exercise_chapter7.v)

##Chapter 9

[Source Code](coq_art_exercise_chapter9.v)

##Chapter 12

[Source Code](coq_art_exercise_chapter12.v)

##Chapter 13

[Source Code](coq_art_exercise_chapter13.v)
