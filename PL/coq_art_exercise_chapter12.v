Module Type DICT.
  Parameters key data dict : Set.
  Parameter empty : dict.
  Parameter add : key->data->dict->dict.
  Parameter find : key->dict->option data.
  Axiom empty_def : forall (k:key), find k empty = None.
  Axiom success :
    forall (d:dict) (k:key) (v:data), find k (add k v d) = Some v.
  Axiom diff_key :
    forall (d:dict) (k k':key) (v:data),
      k <> k' -> find k (add k' v d) = find k d.
End DICT.

Module Type KEY.
  Parameter A : Set.
  Parameter eqdec : forall (a b:A), {a = b}+{a <> b}.
End KEY.

Require Import ZArith.

Open Scope Z_scope.

Module ZKey : KEY.
  Definition A:=Z.
  SearchPattern ({_ = _:>Z}+{~_}).
  Definition eqdec := Z_eq_dec.
End ZKey.

Print ZKey.eqdec.

Require List.

Module LKey (K:KEY) : KEY with Definition A := list K.A.
  Definition A := list K.A.
  Definition eqdec : forall (a b:A), {a = b}+{a <> b}.
    intro a; elim a.
    induction b; [left; auto | right; red; discriminate 1].
    intros a0 k Ha; induction b.
    right; red; discriminate 1.
    case (K.eqdec a0 a1); intro H0.
    case (Ha b); intro H1.
    left; rewrite H1; rewrite H0; auto.
    right; red; injection 1.
    intro H3; case (H1 H3).
    right; red; injection 1.
    intros H3 H4; case (H0 H4).
Defined.
End LKey.

Module LZKey := LKey ZKey.

Module Type DEC_ORDER.
  Parameter A : Set.
  Parameter le : A->A->Prop.
  Parameter lt : A->A->Prop.
  Axiom ordered : order A le.

