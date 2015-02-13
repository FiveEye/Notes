#My solution for coq'art

##Chapter 3
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

(* 3.3 *)

(* 3.4 *)

(* 3.5 p63*)

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




</pre>
