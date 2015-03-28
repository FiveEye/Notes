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
Definition lt3 (n:nat) : bool :=
  match n with
    | O => true
    | S O => true
    | (S (S O)) => true
    | _ => false
  end.

(* 6.16 p152 *)
Fixpoint add' (n m:nat) : nat :=
  match m with
    | O => n
    | S a => S (add' n a)
  end.

(* 6.17 p152 *)
Fixpoint sum_f (n:nat) (f:nat->Z) : Z :=
  match n with
    | O => f O
    | S a => Z.add (f (S a)) (sum_f a f)
  end.

(* 6.18 p152 *)
Fixpoint two_power (n:nat) : nat :=
  match n with
    | O => S O
    | S a => (two_power a) + (two_power a)
  end.

Eval compute in two_power 3.

(* 6.19 p154 *)

Open Scope Z_scope.

Print Z.

Print positive.

Check Zpos (xO (xO (xO (xI (xO (xI (xI (xI (xI xH))))))))).
Check Zpos (xI (xO (xO (xI xH)))).
Check Zpos (xO (xO (xO (xO (xO (xO (xO (xO (xO xH))))))))).

(* 6.20 p154 *)

Definition pos_even_bool (n:positive) : bool :=
  match n with
    | (xO _) => true
    | _ => false
  end.

(* 6.21 p154 *)

Definition pos_div4 (n:positive) : Z :=
  match n with
    | (xO (xO x)) => Zpos x
    | (xO (xI x)) => Zpos x
    | (xI (xO x)) => Zpos x
    | (xI (xI x)) => Zpos x
    | _ => Z0
  end.

(* 6.22 p154 *)

Open Scope positive_scope.

Fixpoint pos_succ (n : positive) : positive :=
  match n with
    | xH => (xO xH)
    | xO x => xI x
    | xI x => xO (pos_succ x)
  end.

Fixpoint pos_add (a b : positive) : positive :=
  match (a, b) with
    | (xH, b) => pos_succ b
    | (a, xH) => pos_succ a
    | ((xO a'), (xO b')) => xO (pos_add a' b')
    | ((xI a'), (xO b')) => xI (pos_add a' b')
    | ((xO a'), (xI b')) => xI (pos_add a' b')
    | ((xI a'), (xI b')) => xO (pos_succ (pos_add a' b'))
  end.

Eval compute in pos_succ xH.
Eval compute in (pos_succ (xI (xI (xI (xI xH))))).
Eval compute in (pos_add (xI (xI (xI (xI xH)))) (xI (xI (xI (xI xH))))).

Search positive.

Eval compute in shift (5) (xI xH).

Fixpoint pos_mult (a b : positive) : positive :=
  match (a, b) with
    | (xH, b) => b
    | (a, xH) => a
    | ((xO a'), (xO b')) => xO (xO (pos_mult a' b'))
    | ((xI a'), (xO b')) => pos_add (xO (xO (pos_mult a' b'))) b
    | ((xO a'), (xI b')) => pos_add (xO (xO (pos_mult a' b'))) a
    | ((xI a'), (xI b')) => pos_add (xO (xO (pos_mult a' b'))) (pos_add (xO a') b)
  end.

Eval compute in (pos_mult (xI (xI (xI (xI xH)))) (xI (xI (xI (xI xH))))).
Eval compute in (pos_mult (xI (xO (xI (xO xH)))) (xI (xO (xI (xO xH))))).

Print Z.

Definition Z_mult (a b : Z) : Z :=
  match (a, b) with
    | (Z0, b) => Z0
    | (a, Z0) => Z0
    | (Zpos x, Zpos y) => Zpos (pos_mult x y)
    | (Zpos x, Zneg y) => Zneg (pos_mult x y)
    | (Zneg x, Zpos y) => Zneg (pos_mult x y)
    | (Zneg x, Zneg y) => Zpos (pos_mult x y)
  end.

(* 6.23 p154 *)

Inductive L : Set :=
  | L_true : L
  | L_false : L
  | L_disj : L -> L -> L
  | L_conj : L -> L -> L
  | L_impl : L -> L -> L
  | L_not : L -> L.

(* 6.24 p155 *)

Inductive F: Set :=
 | one : F
 | n : F -> F
 | d : F -> F.

(* 6.25 p155 *)

Inductive Z_btree : Set :=
 | Z_leaf : Z_btree 
 | Z_bnode : Z->Z_btree->Z_btree->Z_btree.

Search bool.

Fixpoint value_present (z:Z) (t:Z_btree) : bool :=
  match t with
    | Z_leaf => false
    | (Z_bnode x' t1 t2) => if (Zeq_bool x' z) then true else orb (value_present z t1) (value_present z t2)
  end.

(* 6.26 p155 *)

Fixpoint power (z:Z) (n:nat) : Z := 
  match n with
    | O => 1%Z
    | (S x) => Z_mult z (power z x)
  end.

Eval compute in power 3 10.

Fixpoint discrete_log (n:positive) : nat :=
  match n with
    | xH => O
    | (xI x) => S (discrete_log x) 
    | (xO x) => S (discrete_log x) 
  end.

Eval compute in discrete_log (xI (xI (xI (xI xH)))).

(* 6.27 p156 *)

Inductive Z_fbtree : Set :=
  | Z_fleaf : Z_fbtree
  | Z_fnode : Z -> (bool -> Z_fbtree) -> Z_fbtree.

Definition right_son (t:Z_btree) : Z_btree :=
  match t with
  | Z_leaf => Z_leaf
  | Z_bnode a t1 t2 => t2
  end.

Definition fright_son (t:Z_fbtree) : Z_fbtree :=
  match t with
  | Z_fleaf => Z_fleaf
  | Z_fnode a f => f false
  end.

Fixpoint fsum_all_values (t:Z_fbtree) : Z :=
  (match t with
  | Z_fleaf => 0
  | Z_fnode v f =>
    v + fsum_all_values (f true) + fsum_all_values (f false)
  end)%Z.

Check Z.eq_dec.

Fixpoint fzero_present (t:Z_fbtree) : bool :=
  match t with
  | Z_fleaf => false
  | Z_fnode v f => if (Z.eq_dec v 0%Z) then true else orb (fzero_present (f true)) (fzero_present (f false))
  end.

(* 6.28 p157 *)

Inductive Z_inf_branch_tree : Set :=
  | Z_inf_leaf : Z_inf_branch_tree
  | Z_inf_node : Z -> (nat->Z_inf_branch_tree)->Z_inf_branch_tree.


(*
(* Error: Cannot guess decreasing argument of fix. *)
Fixpoint izero_present (n:nat) (t:Z_inf_branch_tree) : bool :=
  match (t, n) with
  | (Z_inf_leaf, _) => false
  | (Z_inf_node 0%Z f, _) => true
  | (Z_inf_node _ f, 0%nat) => izero_present n (f 0%nat)
  | (Z_inf_node _ f, (S m)) => orb (izero_present n (f m)) (izero_present m t)
  end.
*)

Fixpoint any_true (n:nat) (f:nat->bool):bool :=
  match n with 
  | 0%nat => f 0%nat
  | S m => orb (f (S m)) (any_true m f)
  end.

Fixpoint izero_present (n:nat) (t:Z_inf_branch_tree) : bool :=
  match t with
  | Z_inf_leaf => false
  | Z_inf_node v f =>
    match v with
    | 0%Z => true
    | _ => any_true n (fun x => izero_present n (f x))
    end
  end.

(* 6.29 p158 *)

Open Scope nat_scope.

Theorem plus_n_O : forall (n:nat), n = n + 0.
Proof.
intro n.
elim n.
simpl.
reflexivity.
intros.
simpl.
elim H.
reflexivity.
Qed.

(* 6.30 p158 *)

(* 6.31 p158 *)

(* 6.32 p158 *)

(* 6.33 p159 *)

(* 6.34 p161 *)

(* 6.35 p161 *)

(* 6.36 p161 *)

(* 6.37 p161 *)

(* 6.38 p162 *)

(* 6.39 p163 *)

(* 6.40 p163 *)

(* 6.41 p163 *)

(* 6.42 p163 *)

(* 6.43 p163 *)

(* 6.44 p164 *)

(* 6.45 p164 *)

(* 6.46 p167 *)

(* 6.47 p167 *)

(* 6.48 p167 *)

(* 6.49 p167 *)

(* 6.50 p167 *)

(* 6.51 p169 *)

End section_for_chapter_6.