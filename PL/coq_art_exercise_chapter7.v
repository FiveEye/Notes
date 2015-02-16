Require Import Arith.
Require Import Omega.

Section section_for_chapter_7.

(* 7.1 p186 *)

Definition divides (n m:nat) := exists (p:nat), p*n=m.

Theorem divides_0 : forall n, divides n 0.
Proof.
intros.
unfold divides.
exists 0.
trivial.
Qed.

Print divides_0.

Check ex_intro (fun p : nat => p * 1 = 0) 0 eq_refl.

Theorem divides_plus : forall n m, divides n m -> divides n (n + m).
Proof.
intros.
elim H.
intros.
elim H0.
exists (S x).
simpl.
trivial.
Qed.

Theorem not_divides_plus : forall n m:nat, ~ divides n m -> ~ divides n (n+m).
Proof.
intros n m H; red; intro H'; elim H'; intro y.
case y; simpl.
intro H2; apply H.
cut (m=0).
intro H3; rewrite H3; apply divides_0.
omega.
intros n0 Hn0.
apply H.
exists n0.
omega.
Qed.

Theorem not_divides_lt : forall n m:nat, 0 < m ->  m < n -> ~ divides n m.
Proof.
intros n m H H0 H1.
elim H1; intros q Hq.
rewrite <- Hq in H.
rewrite <- Hq in H0.
generalize H H0. case q.
simpl.  
intros; absurd (0 < 0); auto with arith.
clear H H0; intros y Hy Hy'.
simpl in Hy'. 
absurd (n <= n + y * n); auto with arith. 
Qed.


Theorem not_lt_2_divides : forall n m:nat, n <> 1 -> n < 2 -> 0 < m -> ~ divides n m.
Proof.
intros n m H H0; cut (n=0).
intro e;rewrite e.   
case m.
intro; absurd (0 < 0); auto with arith.
intros n0 Hn0 H1.
elim H1; intros q Hq.
rewrite mult_0_r in Hq; discriminate Hq.
omega.
Qed.

Theorem le_plus_minus : forall n m:nat, le n m -> m = n+(m-n).
Proof.
intros; omega.
Qed.

Theorem lt_lt_or_eq : forall n m:nat, n < S m ->  n<m \/  n=m.
Proof.
intros; omega.
Qed.




End section_for_chapter_7.
