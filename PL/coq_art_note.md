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

定理和引理 Theorem Lemma

匿名证明 Goal

最基础的策略 intros, apply, assumption, exact

##3.4 证明的无关性

这里讲的很有意思,Theorem和Definition是等价的.但Theorem是不透明的.所以Theorem没办法进行deta-归约.

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

##3.6 证明策略的结合

简单组合使用分号 tac0; tac1.

处理各个子目标使用 tac0;[tac1 | tac2].

orelse (tac0 || tac1).

idtac 什么都不做

fail 失败

try策略 try tac = tac || idtac.

##3.7 命题逻辑的完备性

((P->Q)->P)->P 不可证.

##3.8 其他证明策略

cut策略: 需要证明P,引入Q->P,然后证明Q. exercise 3.5

assert策略: 引入新的事实.

两个自动证明策略: auto和trivial.

结束的时候提了一下forall.

#Chapter 4 依赖积

#Chapter 5 常用逻辑

这章就是介绍各种策略的,最后非直谓定义好像很好玩.

###5.1.3 apply

apply with (z:=Z)

eapply

Search Zle.

SearchPattern (_ + _ <= _)%Z.

###5.1.4 unfold

###5.2.1 intros elim

###5.2.2 False

###5.2.3 not

###5.2.4 split left right

###5.2.5 repeat

###5.2.6 exists

###5.3.1 reflexivity

###5.3.2 rewrite <-> e in H

###5.3.3 pattern x at 1.

###5.3.4 条件重写

###5.3.5 SearchRewrite p

###5.3.6 replace cutrewrite symmetry transitivity

##5.5 非直谓定义

#Chapter 6 归纳数据类型

##6.1 非递归类型

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

6.2 分情形推理

6.2.1 case

6.2.2 矛盾等式

6.2.2.1 discriminate

6.2.3 单射的构造子

6.2.3.1 injection

6.3 递归类型

6.4 多态类型

6.4.2 option类型 Some, None

6.4.3 二元组类型 prod

6.4.4 不相交和的类型 inl, inr

6.5 依赖归纳类型

这里讲的比较简单,但是练习题各种不会啊! 需要再熟悉一下.

6.6 空类型

这个比较简单.

#Chapter 7 证明策略和自动化证明

Ltac

#Chapter 8 归纳谓词

这章的核心想法很简单,就是使用类型表达属性,每种属性都是一种类型,构造器是他的构造方法.比如小于关系.

#Chapter 9 函数及其规范

**弱规范**: 写出函数A->B,然后再单独证明他满足的属性.

**强规范**: 函数类型就带有约束.

#Chapter 10 程序抽取和命令式程序设计

#Chapter 11 实例分析

#Chapter 12 模块系统

#Chapter 13 无穷对象和证明

#Chapter 14 归纳类型基础

#Chapter 15 一般递归

#Chapter 16 自反证明

#附录 插入排序
