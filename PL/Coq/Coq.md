**A Tutorial for The Coq Proof Assistant** 我看的版本是Nov 7, 2014的,好新...

**Coq'Art: the Calculus of Inductive Constructions** 这本有中文版

[**Software Foundations**](http://www.cis.upenn.edu/~bcpierce/sf/current/index.html) 在线免费教程

[**Certified Programming with Dependent Types**](http://adam.chlipala.net/cpdt/) 另一本免费教材

70年代,数学家用计算机证明了四色定理,然后2004年有人用Coq证明了这个计算机程序的正确性...

随便记点有意思的,笔记新开一篇文章~

<pre>
(* forall (l : list A, reverse (reverse l) = l. *)
Inductive list (A : Type) : Type :=
  | nil  : list A
  | cons : A -> list A -> list A.

Fixpoint append {A} (a : A) (l : list A) : list A :=
  match l with
    | nil      => cons _ a (nil _)
    | cons h t => cons _ h (append a t)
  end.

Fixpoint reverse {A} (l : list A) : list A :=
  match l with
   | nil => nil _
   | cons x xs => append x (reverse xs)
end.

Theorem rev_app {A} : forall (a : A) (l : list A),
  reverse (append a l) = cons A a (reverse l).
Proof.
  intros a l.
  induction l.
  simpl; reflexivity.
  simpl. rewrite IHl. simpl. reflexivity.
Qed.

Theorem rev_rev {A} : forall (l : list A),
  reverse (reverse l) = l.
Proof.
  intro l.
  induction l.
  simpl; reflexivity.
  simpl. rewrite rev_app. rewrite IHl. reflexivity.
Qed.
</pre>

##Tactics

case elim induction

omege

ring

intuition
