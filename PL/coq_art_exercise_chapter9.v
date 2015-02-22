Require Import Arith ZArith.


Section section_for_chapter_9.

(* 9.1 p233 *)
Open Scope Z_scope.
Definition extract : forall (A:Set) (P:A->Prop), sig P -> A :=
fun (A : Set) (P : A -> Prop) (H : {x | P x}) => let (x, _) := H in x.

Print extract.

Theorem P91 : forall (A:Set) (P:A->Prop) (y:{x:A|P x}),
  P (extract A (fun x:A => P x) y).
Proof.
intros.
destruct y.
cut ((extract A (fun x0 : A => P x0) (exist (fun x0 : A => P x0) x p)) = x).
intros.
rewrite H.
exact p.
unfold extract.
reflexivity.
Qed.

Theorem sig_extract_ok :
 forall (A:Set) (P:A -> Prop) (y:sig P), P (extract A P y).
Proof.
 intros A P y. case y. simpl. trivial.
Qed.

(* 9.2 p233 *)
Parameter div_pair : forall (a b:Z), 0 < b -> {p:Z*Z | a = (fst p)*b + snd p /\ 0 <= snd p < b}.

Definition div_pair' (a:Z) (x:{b:Z|0<b}) : Z*Z :=
  match x with
  | exist b h => let (v, _) := div_pair a b h in v
  end.


Definition div_pair'' (a:Z) (x:{b:Z|0<b}) : {p:Z*Z | a = (fst p)*(extract _ _ x) + snd p /\ 0 <= snd p < (extract _ _ x)}.
Proof.
case x.
simpl.
apply div_pair.
Defined.

Print div_pair''.

Close Scope Z_scope.

(* 9.3 p233 *)
Definition sig_rec_simple (A:Set) (P: A -> Prop) (B : Set) :
  (forall x, P x -> B) -> (sig P) -> B.
Proof.
intros.
case H0.
exact H.
Defined.

(* 9.4 p235 *)

Require Import Coq.Arith.Even.

Parameter div2_of_even : forall n:nat, even n -> {p:nat|n=p+p}.
Parameter test_even : forall n:nat, {even n}+{even (pred n)}.

Definition div2_gen (n:nat) :
  {p:nat | n = p+p}+{p:nat | pred n = p+p} :=
  match test_even n with
  | left h => inl _ (div2_of_even n h)
  | right h' => inr _ (div2_of_even (pred n) h')
  end.

Definition eq_dec (A : Type) := forall a a' : A, {a = a'} + {a <> a'}.

Check eq_dec.

Definition nat_eq_dec : eq_dec nat.
Proof.
unfold eq_dec.
induction a; destruct a'.
left; reflexivity.
intros; right; auto.
intros; right; auto.
case (IHa a'). auto. auto.
Qed.

(* 9.5 p235 *)

Fixpoint count (l : list nat) (n : nat) : nat :=
  match l with
  | nil => 0
  | (cons p l') => 
    match eq_nat_dec n p with 
    | left _ => S (count l' n)
    | right _ => count l' n
    end
  end.

(* p236 *)

Definition pred' (n:nat) : {p:nat | n = S p}+{n = 0} :=
  match n return {p:nat | n = S p}+{n = 0} with
  | O => inright _ (refl_equal 0)
  | S p =>
    inleft _
      (exist (fun p':nat => S p = S p') p (refl_equal (S p)))
  end.

Definition pred'' : forall (n:nat), {p:nat | n = S p}+{n = 0}.
  intros n; case n.
  right; apply refl_equal.
  intros p; left; exists p; reflexivity.
Defined.

(* p237 *)

Definition pred_partial : forall (n:nat), n <> 0 -> nat.
  intros n; case n.
  intros h. elim h. reflexivity.
  intros p h'. exact p.
Defined.

Print pred_partial.

(* p238 *)

Theorem le_2_n_not_zero : forall (n:nat), 2 <= n -> n <> 0.
Proof.
intros n Hle; elim Hle; intros; discriminate.
Qed.

(* p245 *)

Fixpoint div2 (n:nat) : nat :=
  match n with 
  | O => O
  | S O => O
  | S (S p) => S (div2 p)
  end.

Theorem div2_le : forall (n:nat), div2 n <= n.
Proof.
intros n.
cut (div2 n <= n /\ div2 (S n) <= S n).
tauto.
elim n.
simpl; auto.
intros p [H1 H2].
split; auto.
simpl; auto with arith.
Qed.

(* 9.6 p248 *)

Fixpoint div3 (n:nat) : nat :=
  match n with 
  | O => O
  | S O => O
  | S (S O) => O
  | S (S (S p)) => S (div3 p)
  end.

Theorem div3_le : forall (n:nat), div3 n <= n.
Proof.
intros n.
cut (div3 n <= n /\ div3 (S n) <= (S n) /\ div3 (S (S n)) <= (S (S n))).
tauto.
elim n.
simpl; auto.
intros p [H1 [H2 H3]].
split; auto.
simpl; auto with arith.
Qed.

(* 9.7 p248 *)

Fixpoint mod2 (n:nat) : nat :=
  match n with 
  | O => O
  | S O => 1
  | S (S p) => mod2 p
  end.

Theorem p97 : forall (n:nat), n = 2 * (div2 n) + (mod2 n).
Proof.
intros.
cut (n = 2 * (div2 n) + (mod2 n) /\ (S n) = 2 * (div2 (S n)) + (mod2 (S n))).
tauto.
elim n.
simpl; auto.
intros p [H1 H2].
split; auto.
cut (mod2 (S (S p)) = mod2 p /\ div2 (S (S p)) = S (div2 p)).
intros [H3 H4].
rewrite H3.
rewrite H4.
rewrite H1 at 1.
ring.
split; auto.
Qed.

Print p97.

Section mod_proof.
 Let P (n:nat) := (n = 2 * (div2 n) + mod2 n).

 Remark R : forall n : nat, P n /\ P (S n).
 Proof.
  simple induction n.
  unfold P; simpl; auto.
  intros n0 [H0 H1]; split.
  trivial.
  unfold P.
  pattern n0 at 1.
  rewrite H0; simpl; ring.
 Qed.

 Lemma div2_mod2 : forall n: nat, n = 2 * (div2 n) + mod2 n.
 Proof. 
  intro n; case (R n); auto.
 Qed.

End mod_proof.

(* 9.8 p248 *)

Fixpoint fib (n:nat) : nat :=
  match n with
  | O => 1
  | S O => 1
  | S (S p as q) => fib p + fib q
  end.

Fixpoint fib_pair (n:nat) : nat * nat :=
  match n with
  | O => (1, 1)
  | S p => match fib_pair p with
           | (x, y) => (y, x + y)
           end
  end.

(* author's answer *)

Definition linear_fib (n:nat) := fst (fib_pair n).

Lemma fib_pair_correct : forall n:nat, fib_pair n = (fib n, fib (S n)).
Proof.
 intro n; elim n; simpl.
 auto.
 intros n0 Hrec; rewrite Hrec; auto.
Qed.

Theorem linear_fib_correct : forall n:nat, linear_fib n = fib n.
Proof. 
 unfold linear_fib; intro n; rewrite fib_pair_correct; simpl; auto.
Qed.

(* 9.9 p249 *)

Theorem induc3 : forall P: nat-> Prop,
                 P 0 -> P 1 -> P 2 ->
                 (forall p, P p -> P (S (S (S p)))) ->
                 forall n, P n.
Proof.
intros P H0 H1 H2 H n.
cut (P n /\ P (S n) /\ P (S (S n))).
tauto.
elim n; intuition.
Qed.

(* author's answer *)
Theorem induc4 : forall P: nat-> Prop,
                 P 0 -> P 1 -> P 2 -> P 3 ->
                 (forall p, P p -> P (S (S (S (S p))))) ->
                 forall n, P n.
Proof.
 intros P H0 H1 H2 H3 H.
 cut (forall n, (P n /\ P (S n) /\ P (S (S n)) /\ P (S (S (S n))))).
 intros H4 n. case (H4 n). auto.
 induction n.
 repeat split; auto.
 intuition.  
Qed.

(* 9.10 p249 *)

(* author's answer *)
Lemma fib_ind : 
  forall P:nat -> Prop,
    P 0 ->
    P 1 -> 
    (forall n:nat, P n -> P (S n) -> P (S (S n))) ->
  forall n:nat, P n.
Proof.
 intros P H0 H1 HSSn n.
 cut (P n /\ P (S n)).
 tauto.
 elim n.
 split; auto.
 intros n0 Hn0; case Hn0; auto.
Qed.

Lemma fib_SSn : forall n:nat, fib (S (S n)) = fib n + fib (S n).
Proof.
 simpl; auto.
Qed.

Require Import Omega.
Require Import ArithRing.
Require Arith.
Lemma fib_SSn_p :
 forall n p:nat, fib (S (S p) + n) = fib (S n) * fib (S p) + fib n * fib p.
Proof.
 intro n; elim n using fib_ind.
 simpl.
 intros; repeat rewrite  plus_0_r.
 rewrite plus_comm; auto.
 intro p; replace (S (S p) + 1) with (S (S (S p))).
 rewrite (fib_SSn (S p)).
 simpl (fib 2); simpl (fib 1).
 rewrite (fib_SSn p).
 ring.
 rewrite plus_comm; simpl; auto.
 intros n0 H0 H1 p.
 replace (S (S p) + S (S n0)) with (S (S (S (S p) + n0))).
 2: omega.
 rewrite (fib_SSn (S (S p) + n0)).
 rewrite H0.
 replace (S (S (S p) + n0)) with (S (S p) + S n0).
 2: omega.
 rewrite H1.
 rewrite (fib_SSn (S n0)).
 rewrite (fib_SSn n0).
 repeat rewrite mult_plus_distr.
 ring.
Qed.

(* 9.11 p249 *)

(* 9.12 p249 *)

(* 9.13 p254 *)

(* 9.14 p254 *)

(* 9.15 p254 *)

(* 9.16 p261 *)

(* 9.17 p262 *)

End section_for_chapter_9.