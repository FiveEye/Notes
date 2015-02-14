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
<pre>
Require Import ZArith.
Section section_for_chapter_6.
Inductive month : Set :=
  | January : month
  | February : month
  | March : month
  | April : month
  | May : month
  | June : month
  | July : month
  | August : month
  | September : month
  | October : month
  | November : month
  | December : month.

(* 6.1 p127 *)
Inductive season : Set :=
  | Spring : season
  | Summer : season
  | Autumn : season
  | Winter : season.

(* 6.2 p127 *)
Check bool_ind.
Check bool_rec.

(* 6.3 p128 *)
Theorem bool_equal : forall b:bool, b = true \/ b = false.
Proof.
intros.
pattern b.
apply bool_ind;[left; reflexivity | right; reflexivity].
Qed.

Theorem bool_equal' : forall b:bool, b = true \/ b = false.
Proof(bool_ind
  (fun b => b = true \/ b = false)
  (or_introl (eq_refl true))
  (or_intror (eq_refl false))).

(* 6.4 p132 *)
Check month_rec.

Definition mtos := month_rect (fun m:month => season)
  Winter Winter Winter
  Spring Spring Spring
  Summer Summer Summer
  Autumn Autumn Autumn.

(* 6.5 p132 *)

Definition month_length (leap:bool) :=
  month_rec (fun m:month => nat)
  31 (if leap then 29 else 28) 31 30 31 30 31 31 30 31 30 31.

Fixpoint nat_even (n:nat) : bool :=
  match n with
    | O => true
    | (S O) => false
    | (S (S m)) => nat_even m
  end.

Definition month_length_even (leap:bool) (m:month):=
  if nat_even (month_length leap m) then true else false.

Eval compute in month_length_even true February.
Eval compute in month_length_even false February.

(* 6.6 p132 *)

Definition bool_not (b:bool) : bool := if b then false else true.

Definition bool_xor (b b':bool) : bool := if b then bool_not b' else b'.

Definition bool_and (b b':bool) : bool := if b then b' else false.

Definition bool_or (b b':bool) := if b then true else b'.

Definition bool_eq (b b':bool) := if b then b' else bool_not b'.

Theorem bool_xor_not_eq :
 forall b1 b2:bool, bool_xor b1 b2 = bool_not (bool_eq b1 b2).
Proof.
intros.
case b1. simpl; trivial.
case b2. simpl; trivial. simpl; trivial.
Qed.

Theorem bool_not_and :
 forall b1 b2:bool,
   bool_not (bool_and b1 b2) = bool_or (bool_not b1) (bool_not b2).
Proof.
intros.
case b1. simpl; trivial.
case b2. simpl; trivial. simpl; trivial.
Qed.

Theorem bool_not_not : forall b:bool, bool_not (bool_not b) = b.
Proof.
intros.
case b. simpl; trivial. simpl; trivial.
Qed.

Theorem bool_ex_middle : forall b:bool, bool_or b (bool_not b) = true.
Proof.
intros.
case b. simpl; trivial. simpl; trivial.
Qed.

Theorem bool_eq_reflect : forall b1 b2:bool, bool_eq b1 b2 = true -> b1 = b2.
Proof.
intros b1 b2.
case b1. simpl. intros. rewrite H. trivial.  
case b2. simpl; trivial. simpl; trivial.
Qed.

Theorem bool_eq_reflect' : forall b1 b2:bool, bool_eq b1 b2 = true -> b1 = b2.
Proof.
  intros b1 b2. case b1; case b2; simpl; trivial.
  discriminate.
Qed.


Theorem bool_eq_reflect2 : forall b1 b2:bool, b1 = b2 -> bool_eq b1 b2 = true.
Proof.
intros b1 b2.
case b1. simpl. intros. rewrite H. trivial.  
case b2. simpl; trivial. simpl; trivial.
Qed.

Theorem bool_eq_reflect2' : forall b1 b2:bool, b1 = b2 -> bool_eq b1 b2 = true.
Proof.
  intros b1 b2. case b1; case b2; simpl; trivial.
  discriminate.
Qed.


Theorem bool_not_or :
 forall b1 b2:bool,
   bool_not (bool_or b1 b2) = bool_and (bool_not b1) (bool_not b2).
Proof.
intros b1 b2.
case b1; case b2; simpl; trivial.  
Qed.


Theorem bool_distr :
 forall b1 b2 b3:bool,
   bool_or (bool_and b1 b3) (bool_and b2 b3) = bool_and (bool_or b1 b2) b3.
Proof.
intros b1 b2 b3.
case b1; case b2; case b3; simpl; trivial.
Qed.

(* 6.7 p133 *)

Record plane : Set := point {abscissa : Z; ordinate : Z}.

Check plane_rec.

(* 6.8 p133*)

Definition manhattan_dist (p1 p2 : plane) : Z :=
 Z.add (Z.abs (abscissa p1 - abscissa p2)) (Z.abs (ordinate p1 - ordinate p2)).

(* 6.9 p135 *)

Inductive vehicle : Set :=
  | bicycle : nat -> vehicle
  | motorized : nat -> nat -> vehicle.

Check vehicle_rec.

Definition nb_seats := vehicle_rec (fun v => nat) (fun x => 2) (fun x n => n).

Eval compute in nb_seats (bicycle 5).

Eval compute in nb_seats (motorized 2 3).

(* 6.10 p140 *)

Definition is_Jan := month_rect (fun m => bool)
  true false false false
  false false false false
  false false false false.

Eval compute in is_Jan January.
Eval compute in is_Jan February.

(* 6.11 p140 *)

Check bool_rect.

Theorem neq_tf : true <> false.
Proof.
unfold not.
discriminate.
Qed.

Section proof_of_bool_discr.

 Let is_true (b:bool) : Prop :=
   match b with
   | true => True
   | _ => False
   end.

 Theorem bool_discr : true <> false.
 Proof.
  intro e.
  change (is_true false).
  rewrite <- e. simpl. trivial.
 Qed.

End proof_of_bool_discr.

Print bool_discr.

(* 6.12 p140 *)

Theorem neq_bm : forall (x y z:nat), bicycle x <> motorized y z.
Proof.
unfold not.
discriminate.
Qed.

Section proof_of_vehicle_discr.

 Let is_bicycle (v:vehicle) : Prop :=
   match v with
   | (bicycle x) => True
   | _ => False
   end.

 Theorem vehicle_discr : forall (x y z:nat), bicycle x <> motorized y z.
 Proof.
  intros.
  unfold not.
  intros.
  change (is_bicycle (motorized y z)).
  rewrite <- H. simpl. trivial.
 Qed.

End proof_of_vehicle_discr.

(* 6.13 p143 *)
(* this part includes a proof of false *)
(*
Require Import Arith.
Record RatPlus : Set := mkRat
  {top : nat; bottom : nat; bottom_condition : bottom <> 0}.

Axiom
  eq_RatPlus :
    forall r r':RatPlus, top r * bottom r' = top r' * bottom r -> r = r'.

Theorem rp1 : forall (x0 y0 x1 y1:nat) (p0:y0<>0) (p1:y1<>0), mkRat x0 y0 p0 = mkRat x1 y1 p1 -> x0 = x1.
Proof.
intros.
injection H.
trivial.
Qed.

SearchPattern (_ <> _).

Definition n0 := mkRat 2 6 (not_eq_sym (O_S 5)).

Definition n1 := mkRat 1 3 (not_eq_sym (O_S 2)).

Theorem rp2 : mkRat 2 6 (not_eq_sym (O_S 5)) = mkRat 1 3 (not_eq_sym (O_S 2)) -> False.
Proof.
intros.
discriminate.
Qed.

Theorem rp3 : mkRat 2 6 (not_eq_sym (O_S 5)) = mkRat 1 3 (not_eq_sym (O_S 2)).
Proof.
apply eq_RatPlus.
compute.
trivial.
Qed.

Theorem proof_false : False.
Proof.
apply rp2.
exact rp3.
Qed.
*)

(* 6.14 p152 *)
(* 6.15 p152 *)
(* 6.16 p152 *)
(* 6.17 p152 *)

End section_for_chapter_6.
</pre>
