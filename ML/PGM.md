#Probailistic Graphical Models

[Blog Link](http://www.freopen.com/?p=10846)

开个坑...去年因某种不可抗力...追了一半就被迫停止了...现在捡一下...但愿还能捡的起来... lol

前两章是预备知识

#Chapter 1: Introduction

#Chapter 2: Foundations

**Chebyshev inequality**: $latex P(|X - E_p[X]| \ge t) \le \frac{Var_P[X]}{t^2}$

#Chapter 3: The Bayesian Network Representation

**Box 3.A** Concept: The Naive Bayes Model

介绍了一下朴素贝叶斯,它的一个很明显的缺点就是,fetures不是相互独立的,那么就会影响正确性,在medical diagnosis的应用中,体现的很明显.不过在spam/non-spam中naive Bayes工作的很好,有论文来讨论这件事情.

**Box 3.B** Case Study: The Genetics Example

很简单直观的例子,血型与基因遗传模型.Coursera上貌似有这个的练习.

###3.2.3 Graphs and Distributions

**I-Map**: 把联合概率分解成合法的贝叶斯网络

Factorization to I-Map: the conditional Independencies imply factorization

**Box 3.C** Skill: Knowledge Engineering

Picking variables:

Picking structure: causes are parents of the effect.只是通常,也可能反着,对保险公司来讲,是否有过事故记录->是否是一个好司机

Picking probabilities:

**Box 3.D** Case Study: Medical Diagnosis System

One of the first models used was a simple naive Bayes model. First, 10 percent of the cases were diagnosed incorrectly.Second, the expert estimated the probabilities P(Finding | Disease) by fixing a single disease and evaluating the probabilities of all its findings. It was found that the expert was more confortable considering a single finding and evaluating its probability across all diseases.

the Bayesian network model: 75000 parameters, 35 hours to define its structure, and 40 hours for the parameters.

##3.3 Independencies in Graphs

###D-separation

Indirect connection:
  * Causal trail: X -> Z -> Y
  * Evidential trail: X <- Z <- Y
  * Common cause: X <- Z -> Y
  * Common effect: X -> Z <- Y

**Algorithm 3.1** Algorithm for finding nodes reachable from X given Z via active trails

标记Z和Z的祖先,然后从X开始BFS

###I-Equivalence

A v-structure X -> Z <- Y is an immorality if there is no direct edge between X and Y. If there is such an edge, it is called a covering edge for the v-structure.

Let G1 and G2 be two graphs over X. Then G1 and G2 have the same skeleton and the same set of immoralities if and only if they are I-equivalent.

##3.4 From Distributions to Graphs

###Minimal I-Maps

**Algorithm 3.2** Procedure to build a minimal I-map given an ordering

很简单暴力的一个算法,枚举所有节点i,然后从0到i-1中暴力枚举选最小的一个合法子集作为i的父亲.

a minimal I-map is not able to remove any edges.

minimal I-map的质量取决于节点遍历的顺序,所以还需要改进.

###Perfect Maps

但是并非所有的distribution都有perfect map,比如1, x xor y xor z. 2. ABCD组成的无向图. $latex A \perp C | \{B, D\}, B \perp D | \{A, C\}$.

###3.4.3 Finding Perfect Maps

P-Map可能存在也可能存在多个.

####Identifying the Undirected Skeleton

**Algorithm 3.3** Recovering the undirected skeleton for a distribution P that has a P-map

很简单,先假设是完全图H,枚举任意两个节点i,j.然后枚举其余点组成的集合的实例(witness),如果i,j条件独立就删掉i-j这条边,返回H,同时返回让i,j条件独立的条件集合Uij.复杂度指数级的.

####Idnentifying Immoralities

**Algorithm 3.4** Marking immoralities in the construction of a perfecrt map

这个算法是找v-structure的在skeleton上枚举i-j-k并且i和k不相连的三元组,如果j不在Uik里面,就说明是个v-structure.

####Representing Equivalence Classes

找出skeleton和immoralities,其余的边并不能随便标记方向,可能会产生v-structure.所以还要一个算法标记其余边的方向.

**Algorithm 3.5** Finding the class PDAG characterizing the P-map of a distribution P

一共有三条规则 {X->Y-Z} => {X->Y->Z}, {X->Y->Z-X} => {X->Y->Z<-X}, {X-(Y1,Y2,Z), Y1->Z, Y2->Z} => {X-(Y1,Y2), X->Z, Y1->Z, Y2->Z}.

如果还有无向边,就找符合这三条规则的边,然后标记方向.

#Chapter 4: Undirected Graphical Models

Markov network

##4.1 The Misconception Example

$latex P \models (X \perp Y | Z)$ if and only if we can write P in the form $latex P(\chi) = \phi_1(X,Z) \cdot \phi_2(Y,Z)$.

$latex P(a, b, c, d) = \frac{1}{Z} \phi_1(a,b) \cdot \phi_2(b,c) \cdot \phi_3(c,d) \cdot \phi_4(d,a)$.

$latex Z = \sum_{a,b,c,d}P(a, b, c, d)$.

##4.2 Parameterization

###4.2.1 Factors

$latex \psi(X,Y,Z) = \phi_1(X,Y) \cdot \phi_2(Y,Z)$.

###4.2.2 Gibbs Distributions and Markov Networks

就是能分解成factor的分布都是Gibbs Distribution.

Markov Networks分解成clique,每个clique是一个complete subgraph.

**Box 4.A** Concept: Pairwise Markov Networks.

目测就是clique最多两个节点

###4.2.3 Reduced Markov Network

就讲条件概率,给定evidence怎么化解一下.

**Box 4.B** Case Study: Markov Networks for Computer Vision.

##4.3 Markov Network Independencies

###4.3.1 Basic Independencies

无向图上独立比较简单,只要被观察的点是一个割,两侧就相互独立了.

**Soundness**

如果P是一个Gibbs分布,H是MN over X,那么H是P的I-Map

P是一个正分布,H是MN over X,如果H是P的I-Map,那么P是H上的Gibbs分布

**Completeness**

如果Z没有把X和Y分离,那么X和Y在H上的P分布中是相关的.

###4.3.2 Independencies Revisited

MN上的独立性比BN上简单,因为MN上没有v-structure.所以随便就能YY出来了.

  * pairwise independencies: 两个没有相连的节点在给定其他节点值得情况下独立$latex X \perp Y | \chi - \{X,Y\}$.

  * local independencies: 一个节点所有的邻居被观察到,则他和其余点独立$latex X \perp \chi - \{X\} -MB_H(X) | MB_H(X)$.

###4.3.3 From Distributions to Graphs

想法很简单,枚举所有节点对,如果他们不满足pairwise independencies,则添加一条x-y的边,最后得到I-map.

同样可以使用local independencies来获得I-map.

##4.4 Parameterization Revisited

同一个MN可以有不同的表示方式,一种是一个clique一个factor,另一种是一条边一个factor.

###4.4.1 Finer-Grained Parameterization

##4.5 Bayesian Networks and Markov Networks

###4.5.1 From Bayesian Networks to Markov Networks

一个节点和他的parents们组成一个clique,这个叫Moralizing. 这就是BN的转换成的一个 minimal I-map MN.

如果一个BN是moral的,转换出来的MN是perfect的,很简单,没有v-structure.

###4.5.1 From Markov Networks to Bayesian Networks

转换方法很简单,依次加入新的点,如果新的节点和旧节点没有条件独立,那么就加一条旧节点到新节点的边.

MN转换到的BN minimal I-map没有immoralities.

如果BN上有4个节点以上的loop,那么至少有一个immorality.

###4.5.3 Chordal Graphs

BN和MN都能表示的交集

clique tree

##4.6* Partially Directed Models

#Chapter 9 Exact Inference: Variable Elimination

#Chapter 10 Exact Inference: Clique Trees

##10.1 Variable Elimination and Clique Trees

**Definition 10.2** 在cluster tree上,如果两个节点都含有x,那么中间节点也都含有x.

##10.2 Message Passing: Sum Product

这个本质还是VE,不过可以在clique tree上做dp,这样所有变量的post probablity可以在2c的时间内计算出来.

##10.3 Message Passing: Belief Update

这个挺有意思的,本质还是Sum Product.不过是用的不同的观点来看这件事情.

我们注意到一个节点i到j传递的信息$latex \alpha_{i->j} = \beta_i / \alpha_{j->i}$.

所以我们初始化所有的$latex \alpha_{i->j}$都为1,然后随意更新,直到全部稳定.每条边记录当前的消息$latex u_{i->j}$,更新$latex \beta_j *= \alpha_{i->j} / u_{i->j}$.

如果我们按照Sum Product的顺序来来更新,肯定是最高效的,所以这只是另一个角度看待Message Passing,并没有提供更好的做法.

###10.3.3 Answering Queries

**Incremental Updates** : 被观察到的变量不断增多,刷新概率. 比较暴力的方法就是每次redo the process from beginning.

这个很适合用Belief Update,技术角度讲,SP和BU保持的信息量一样的,而BU是更新单一变量的方法.

**Queries Outside a Clique** : 查询的变量不在同一个clique里面.

找到一个含有所有查询变量的子树,然后做VE.因为已经求出了$\beta$和$\u$,所以不是对整颗树做VE,可以加速.

**Multiple Queries** :

这个算法也很简单,对每一对相邻的$C_i$和$C_j$预处理$P(C_i,C_j)$,每次求解可以dp.

##10.4 Constructing a Clique Tree
