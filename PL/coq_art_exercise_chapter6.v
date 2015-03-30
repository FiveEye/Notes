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
 | F_one : F
 | F_n : F -> F
 | F_d : F -> F.

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


(* Error: Cannot guess decreasing argument of fix. *)
(*
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

Fixpoint f1 (bt:Z_btree) : Z_fbtree :=
  match bt with
  | Z_leaf => Z_fleaf
  | Z_bnode v t1 t2 => Z_fnode v (fun b => if b then (f1 t1) else (f1 t2))
  end.

Fixpoint f2 (ft:Z_fbtree) : Z_btree :=
  match ft with
  | Z_fleaf => Z_leaf
  | Z_fnode v f => Z_bnode v (f2 (f true)) (f2 (f false))
  end.

Theorem f2_f1 : forall t: Z_btree, f2 (f1 t) = t.
Proof.
intros.
elim t.
simpl.
trivial.
intros.
simpl.
rewrite H.
rewrite H0.
trivial.
Qed.

Require Import Logic.FunctionalExtensionality.

Theorem f1_f2 : forall t: Z_fbtree, f1 (f2 t) = t.
Proof.
intros.
induction t.
simpl; trivial.
simpl. rewrite H. rewrite H.
rewrite <- (functional_extensionality (fun b:bool => if b then z0 true else z0 false) z0).
trivial.
intros. elim x; trivial.
Qed.

(* 6.31 p158 *)

Fixpoint mult2 (n:nat) : nat :=
  match n with
  | O => O
  | (S p) => (S (S (mult2 p)))
  end.

Lemma mult2_double : forall n:nat, mult2 n = n + n.
Proof.
intros.
elim n.
simpl. trivial.
intros.
simpl. rewrite H. rewrite plus_n_Sm. trivial.
Qed.

(* 6.32 p158 *)

Fixpoint sum_n (n:nat) : nat :=
  match n with
  | O => O
  | S p => S p + sum_n p
  end.

Require Import ArithRing.

Theorem sum_closed_form : forall n:nat, 2 * sum_n n = n * S n.
Proof.
intro n.
induction n.
simpl. trivial.
simpl (sum_n (S n)).
ring_simplify.
rewrite IHn.
ring_simplify.
trivial.
Qed.

Theorem sum_closed_form' : forall n:nat, 2 * sum_n n = n * S n.
Proof.
induction n; trivial.
unfold sum_n; fold sum_n.
rewrite mult_plus_distr_l.
rewrite IHn.
simpl.
f_equal.
rewrite <- plus_n_O.
repeat rewrite mult_succ_r.
repeat rewrite plus_n_Sm.
rewrite plus_assoc_reverse.
f_equal.
rewrite <- plus_comm.
trivial.
Qed.

Print sum_closed_form'.

(* 6.33 p159 *)

Require Import Omega.

Theorem sum_n_le_n : forall n:nat, n <= sum_n n.
Proof.
intro n.
assert ((2 * n) <= (2 * sum_n n)).
rewrite sum_closed_form.
ring_simplify.
induction n.
simpl; omega.
ring_simplify. omega.
omega.
Qed.

Print sum_n_le_n.

Theorem sum_n_le_n' : forall n:nat, n <= sum_n n.
Proof.
 simple induction n.
 auto with arith.
 intros n1 Hn0. simpl.
 auto with arith.
Qed.

Print sum_n_le_n'.

(* 6.34 p161 *)
Require Import List.
Definition two_first (A:Set)(l:list A) : list A :=
 match l with 
 | a :: b :: l' => a :: b :: nil
 | _ => (nil (A:=A))
 end.

(* 6.35 p161 *)

Fixpoint take (A:Set)(n:nat)(l:list A): list A :=
   match (n,l) with
   | (0, l') => nil
   | (S n', nil) => nil
   | (S n', a::l') => 
     match take _ n' l' with
     | nil => nil
     | l'' => a :: l''
     end
  end.

(* 6.36 p161 *)

Fixpoint sum_list (l:list nat) : nat :=
  match l with
  | nil => 0
  | a::l' => a + sum_list l'
  end.

(* 6.37 p161 *)

Fixpoint ones (n:nat) : list nat :=
  match n with
  | O => nil
  | (S m) => 1 :: ones m
  end.

(* 6.38 p162 *)

Fixpoint natlist (n:nat) : list nat :=
  (fix f (m:nat):list nat :=
    match m with
    | O => nil
    | (S x) => (n - x)::(f x)
    end) n.

Eval compute in natlist 5.

(* 6.39 p163 *)

Fixpoint nth_option (A:Set)(n:nat)(l:list A) {struct l}: option A :=
  match n, l with
  | O, cons a tl =>  Some a
  | S p, cons a tl => nth_option A p tl
  | _, nil => None
  end.

Fixpoint nth_option' (A:Set)(n:nat)(l:list A) {struct n}: option A :=
  match n, l with
  | O, cons a tl =>  Some a
  | O, nil => None
  | S p, cons a tl => nth_option' A p tl
  | S p, nil => None
  end.

(* 6.40 p163 *)

Lemma nth_length : forall (A:Set)(n:nat)(l:list A), nth_option A n l = None <-> length l <= n.
Proof.
simple induction n.
destruct l.
simpl; split; auto.
simpl; split; [discriminate | inversion 1].
destruct l; split; simpl; auto with arith.
case (H l); auto with arith.
case (H l); auto with arith.
Qed.

(* 6.41 p163 *)

Fixpoint first_in_list (A:Set)(f:A->bool)(l:list A) : option A :=
  match l with
  | nil => None
  | a::l' => if f a then Some a else first_in_list A f l'
  end.

(* 6.42 p163 *)

Fixpoint split (A B: Set)(l: list (A * B)) : (list A)*(list B) :=
  match l with
  | nil => (nil, nil)
  | (a,b)::l' => let ll := (split _ _ l') in (a::(fst ll), b::(snd ll))
  end.

Fixpoint combine (A B: Set)(l1 : list A)(l2 :list B): list (A*B):=
  match l1, l2 with
  | nil, _ => nil
  | _, nil => nil
  | a::l1', b::l2' => (a,b)::(combine _ _ l1' l2')
  end.

(*copy from the answer*)
Theorem combine_of_split : forall (A B:Set) (l:list (A*B)),
   let ( l1,l2) :=  (split _ _ l) 
   in combine _ _ l1 l2 = l.
Proof.
 simple induction l; simpl; auto.
 intros p l0; case (split A B l0); simpl; auto.
 case p; simpl; auto.
 destruct 1; auto. 
Qed.

Print combine_of_split.

(* 6.43 p163 *)

Inductive btree (A:Set) :Set :=
  | bleaf : btree A 
  | bnode : A ->btree A->btree A->btree A.

Fixpoint Z_btree_to_btree (t:Z_btree) : btree Z :=
  match t with
  | Z_leaf => bleaf Z
  | Z_bnode x t1 t2 => 
      bnode Z x (Z_btree_to_btree t1) (Z_btree_to_btree t2)
  end.

Fixpoint btree_to_Z_btree (t:btree Z) : Z_btree :=
  match t with
  | bleaf => Z_leaf
  | bnode x t1 t2 => 
      Z_bnode x (btree_to_Z_btree t1) (btree_to_Z_btree t2)
  end.

Theorem btree_to_Z_inv : forall t, Z_btree_to_btree (btree_to_Z_btree t) = t.
Proof.
intros.
induction t.
simpl.
trivial.
simpl.
rewrite IHt1.
rewrite IHt2.
trivial.
Qed.

Theorem Z_btree_to_inv : forall t, btree_to_Z_btree (Z_btree_to_btree t) = t.
Proof.
intros.
induction t; simpl; trivial.
simpl; rewrite IHt1; rewrite IHt2; trivial.
Qed.

(* 6.44 p164 *)

Fixpoint F_to_PQ (f:F) : nat * nat :=
  match f with
  | F_one => (1, 1)
  | F_n g => let (p,q) := F_to_PQ g in (p+q,q)
  | F_d g => let (p,q) := F_to_PQ g in (p,p+q)
  end.

Eval compute in F_to_PQ (F_one).

Eval compute in F_to_PQ (F_n F_one).

Eval compute in F_to_PQ (F_d (F_n F_one)).

(* 6.45 p164 *)

Inductive cmp : Set := 
  | Less : cmp
  | Equal : cmp
  | Greater : cmp.

Fixpoint three_way_compare (a b:nat) : cmp :=
  match a, b with
  | O, O => Equal
  | S _, O => Greater
  | O, S _ => Less
  | S n, S m => three_way_compare n m
  end.

Fixpoint update_primes (k:nat) (l:list (nat*nat)) : (list (nat*nat))*bool :=
  match l with
  | nil => (nil, false)
  | (p,m)::l' => let (a, b) := update_primes k l' in
    match three_way_compare k m with
    | Less => ((p, m)::a, b)
    | Equal => ((p, m+p)::a, true)
    | Greater => ((p, m+p)::a, b)
    end
  end.

Fixpoint prime_sieve (n:nat) : (list (nat*nat)) :=
  match n with
  | O => nil
  | S O => nil
  | S m => let (a, b) := update_primes (S m) (prime_sieve m) in
    if b then a else (S m, 2 * (S m))::a
  end.

Eval compute in prime_sieve 100.

(* It is so hard to prove the soundness and completeness! *)

(* 6.46 p167 *)

Inductive htree (A:Set) : nat -> Set :=
  | hleaf : A -> (htree A O)
  | hnode : forall n:nat, A -> htree A n -> htree A n -> htree A (S n).

Fixpoint invert (A:Set)(n:nat)(t:htree A n) : htree A n :=
  match t with
  | hleaf v => hleaf A v
  | hnode p v t1 t2 =>
    hnode A p v (invert A p t2) (invert A p t1)
  end.

(*copy from the answer*)

Definition first_of_htree :
  forall (A:Set) (n:nat), htree A n -> htree A (S n) -> htree A n.
 intros A n v t.

 generalize v.
 change (htree A (pred (S n)) -> htree A (pred (S n))).
 case t.
 intros x v'; exact v'.
 intros p x t1 t2 v'; exact t1.
Defined.
 
Print first_of_htree.

Eval compute in (pred O).

Theorem injection_first_htree :
 forall (n:nat) (t1 t2 t3 t4:htree nat n),
   hnode nat n 0 t1 t2 = hnode nat n 0 t3 t4 -> t1 = t3.
 intros n t1 t2 t3 t4 h.
 change
  (first_of_htree nat n t1 (hnode nat n 0 t1 t2) =
   first_of_htree nat n t1 (hnode nat n 0 t3 t4)).
 rewrite h.
 reflexivity.
Qed.

(* 6.47 p167 *)

Fixpoint make_htree (n:nat) : htree Z n :=
  match n with
  | O => hleaf Z 0%Z
  | (S m) => hnode Z m 0%Z (make_htree m) (make_htree m)
  end.

(* 6.48 p167 *)

Inductive binary_word : nat -> Set :=
  | empty_binary_word :  binary_word 0
  | cons_binary_word :
    forall p:nat, bool -> binary_word p -> binary_word (S p).

Fixpoint binary_word_concat (n:nat)(w1:binary_word n)(m:nat)(w2:binary_word m) : binary_word (n+m) :=
  match w1 with
  | empty_binary_word => w2
  | cons_binary_word q b w1' =>
    cons_binary_word (q+m) b (binary_word_concat q w1' m w2)
 end.

(* 6.49 p167 *)
Fixpoint binary_word_or (l : nat) (wl wr : binary_word l) : binary_word l.
  destruct wl.
  exact wr.
  inversion wr.
  exact(cons_binary_word p (orb b H0) (binary_word_or p wl H1)).
Defined.

Definition bw1:= cons_binary_word 1 false (cons_binary_word 0 true empty_binary_word).
Definition bw2:= cons_binary_word 1 true (cons_binary_word 0 false empty_binary_word).

Eval compute in binary_word_or 2 bw1 bw2.

Print binary_word_or.

Eval compute in eq_rec 2 binary_word bw1 2 eq_refl.

Fixpoint binary_word_or1 (l : nat) (wl wr : binary_word l) : binary_word l.
  refine(
    match wl in binary_word n return binary_word n -> binary_word n with
    | empty_binary_word => (fun x => x)
    | cons_binary_word ll lb lw => 
        (fun wr' : binary_word (S ll) => match wr' with
        | empty_binary_word => (fun p : False => wr')
        | cons_binary_word rl rb rw => 
            (fun p : ll = rl => 
              cons_binary_word
              rl
              (bool_or lb rb) 
              (binary_word_or rl (eq_rec ll binary_word lw rl p) rw))
        end _)
    end wr).
    reflexivity.
Defined.

Print binary_word_or1.

Fixpoint binary_word_or2 (n:nat)(w1 w2:binary_word n) : binary_word n.
  refine(
  match w1 in binary_word p return binary_word p -> binary_word p with
  | empty_binary_word => (fun x => x)
  | cons_binary_word q1 b1 w1' => (fun w3 =>
    match w3 with 
    | empty_binary_word => w3
    | cons_binary_word q2 b2 w2' => (fun P:q1=q2 =>
      cons_binary_word q2 (orb b1 b2) (binary_word_or q2 (eq_rec q1 binary_word w1' q2 P) w2'))
    end eq_refl
  )
  end w2).
Qed.

Print binary_word_or2.
(* 6.50 p167 *)

(* 6.51 p169 *)

Check Empty_set.

Theorem all_equal : forall x y : Empty_set, x = y.
Proof.
destruct x.
Qed.

Theorem all_diff : forall x y : Empty_set, x <> y.
Proof.
destruct x.
Qed.

End section_for_chapter_6.