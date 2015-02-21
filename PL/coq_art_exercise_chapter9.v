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

End section_for_chapter_9.