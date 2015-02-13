**A Tutorial for The Coq Proof Assistant** 我看的版本是Nov 7, 2014的,好新...

**Coq'Art: the Calculus of Inductive Constructions** 这本有中文版

[**Software Foundations**](http://www.cis.upenn.edu/~bcpierce/sf/current/index.html) 在线免费教程

[**Certified Programming with Dependent Types**](http://adam.chlipala.net/cpdt/) 另一本免费教材

70年代,数学家用计算机证明了四色定理,然后2004年有人用Coq证明了这个计算机程序的正确性...

随便记点有意思的,读书笔记先不弄了.

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

#Coq'Art

#Chapter 2 类型和表达式

##2.4 计算

cbv(传值调用), lazy

###alpha-变换

t{v/u}把v用u替换

###delta-归约

v = t', t{v/t'} 将标识符展开成值.

<pre>
Require Import Arith.
Require Import ZArith.
Require Import Bool.

Open Scope Z_scope.

Definition Zsqr (z:Z) : Z := z * z.

Definition my_fun (f:Z->Z) (z:Z) : Z := f (f z).

Eval cbv delta [my_fun Zsqr] in (my_fun Zsqr).

Eval cbv delta [my_fun] in (my_fun Zsqr).

Eval cbv delta [Zsqr] in (my_fun Zsqr).
</pre>

###beta-归约

(fun v:T => e1) e2, e1{v/e2} 将形参替换成实参.

<pre>
Eval cbv beta delta [my_fun Zsqr] in (my_fun Zsqr).
</pre>

###zata-归约

let v:=e1 in e2, e2{v/e1} 将局部变量替换.

<pre>
Definition h x y := let a := x + y in let b := x - y in a*a + b*b.

Eval cbv beta delta [h] in (h 1 2).

Eval cbv beta zeta delta [h] in (h 1 2).
</pre>

###iota-归约

6.1.4介绍

Eval compute in e = Eval cbv iota beta zeta delta in e

###2.4.3 归约序列

强正则性:有限步完成归约

合流性:不同归约次序结果一样,唯一范式

##2.5 类型

Set大类,表达数据类型和程序规范.都可以认为是程序.

#Chapter 3 命题和证明

最小命题逻辑,经典逻辑和直觉主义.直觉逻辑和lambda演算等价.

Prop大类

##3.1 最小命题逻辑

不是经典逻辑,没有排中率,不承认非真即假.

全局变量

Axiom x : P.

Parameter x : P.

局部变量

Hypothesis h : P.

Variable h : P.

定理和引理
Theorem Lemma

匿名证明 Goal

最基础的策略
intros, apply, assumption, exact

##3.4 证明的无关性

这里讲的很有意思,Theorem和Definition是等价的.但Theorem是不透明的.

<pre>
Theorem nat_exist : nat.
Proof 0.

Check nat_exist.
Print nat_exist.

Definition nat_exist' : nat := 0.
Check nat_exist'.
Print nat_exist'.

Eval compute in 1 + nat_exist.
Eval compute in 1 + nat_exist'.
</pre>

#Chapter 4 依赖积

#Chapter 5 常用逻辑

#Chapter 6 归纳数据类型

##枚举类型

<pre>
Inductive M : Set :=
  | A | B.

Check M_ind.

M_ind : forall P : M -> Prop,
  P A -> P B -> forall m : M, P m
</pre>

这里展示ind如何构建forall.

<pre>
Theorem M_equal : forall m : M, m = A \/ m = B.
Proof.
  (*intro m; pattern m; apply M_ind.*)
  induction m.
  apply or_introl.
  exact eq_refl.
  apply or_intror.
  exact eq_refl.
Qed.

</pre>

#Chapter 7 证明策略和自动化证明

#Chapter 8 归纳谓词

#Chapter 9 函数及其规范
