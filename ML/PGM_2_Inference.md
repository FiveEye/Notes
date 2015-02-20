#Probailistic Graphical Models

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

**Incremental Updates**: 被观察到的变量不断增多,刷新概率. 比较暴力的方法就是每次redo the process from beginning.

这类查询很适合用Belief Update,技术角度讲,SP和BU保持的信息量一样的,而BU是更新单一变量的方法.

**Queries Outside a Clique**: 查询的变量不在同一个clique里面.

找到一个含有所有查询变量的子树,然后做VE.因为已经求出了$\beta$和$\u$,所以不是对整颗树做VE,可以加速.

**Multiple Queries**: 这个算法也很简单,对每一对相邻的$C_i$和$C_j$预处理$P(C_i,C_j)$,每次求解可以dp.

##10.4 Constructing a Clique Tree

介绍了两种构建的方式:

**Variable Elimination** : VE的过程其实就是在创建Clique Tree,所以直接记录下来就可以了.

**Chordal Graphs** : 这个也简单,先把图转换成chordal图,然后再转成clique,这两步的精确解都是NPC问题.
  * chordal graphs: node-elimination techniques in section 9.4.3.2
  * find cliques: maximum cardinality search.

#Chapter 11: Inference as Optimization*

和第十章连在一起的一章,有必要读一下.

#Chapter 12: Particle-Based Approximate Inference

Particle-based methods can be roughly characterized along two axes. On one axis, approaches vary on the process by which particles are generated. On the other axis, techniques use different notions of particle.

##12.1 Forward Sampling

The simplest approach to the generation of particles. Finding a topological ordering of X, then sampling.

Because the Bayesian network is a DAG, so it is easy to use topological ordering to compute P(x), but it cannot work well for computing P(x|e). So the rest of this chapter seems to focus on P(x|e).

###12.1.1 Sampling from a Bayesian Network

**Algorithm 12.1** Forward Sampling in a Bayesian network

```
Let X_1, ..., X_2 be a topological ordering of X

for i = 1, ..., n
  u_i <- x(Pa_{X_i})
  Sample x_i from P(X_i | u_i)

return (x_1, ..., x_n)

```

**Box 12.A** Skill: Sampling from a Discrete Distribution.
  It is simple.

###12.1.2 Analysis of Error

a basic question about sampling is how many particles required to guarantee the performance.

So there is a theorem named Hoeffding bound which shows the relationship.

###12.1.3 Conditional Probability Queries

**Rejection Sampling**: do forward sampling but throw out sample where $latex E \neq e$

##12.2 Likelihood Weighting and Importance Sampling

This sampling deals with conditional probability queries. It gives us a more effective way than the rejection sampling. The basic idea is that we still use forward sampling, but weight every particle, and use them to calculate P(x|e).

###12.2.1 Likelihood Weighting: Intuition

**Algorithm 12.2** Likelihood-weighted particle generation

```
Z is observed.

Let X_1, ..., X_2 be a topological ordering of X

w <- 1

for i = 1, ..., n
  u_i <- x(Pa_{X_i})
  if x_i is not in Z then
    Sample x_i from P(X_i | u_i)
  else
    x_i <- z(X_i)
    w <- w * P(x_i | u_i)

return (x_1, ..., x_n), w

```

$latex P(y|e) = \frac{\sum w[m]*I{y[m]=y}}{\sum w[m]}$

###12.2.2 Importance Sampling

Likelihood-weighted is a special case of a very general approach called importance sampling.

It is a very interesting analysis for sampling. Let $Q(x)$ is a different distribution, and the key point is that $Q(x)$ is easy to calculate, and the relationship $w(x) = \frac{P(X)}{Q(X)}$ between $P(x) and $Q(x)$ also is easy to calculate. Then we can use $Q(x)$ and $w(x)$ to represent $P(x)$.

####12.2.2.1 Unnormalized Importance Sampling

```
$latex E_P[f] = \frac{1}{M} \sum f(x[m])$ we use sampling and this formula to estimate $E_P[f]$

$latex E_{P(X)}[f(X)] = \sum P(x)f(x)$ this is what $E_P[f]$ exactly is.

$latex E_{P(X)}[f(X)] = E_{Q(X)}[f(X)\frac{P(X)}{Q(X)}]$ the equality between P(X) and Q(X).

$latex E_{Q(X)}[f(X)w(X)] = \frac{1}{M} \sum f(x[m])w(x[m])$
```
We also call this estimator the unweighted importance sampling.

**Analysis**:

####12.2.2.2 Normalized Importance Sampling

If P(X) is known, we don't need to normalize it. But we often don't know P(X), but P'(X) which is a unormailized distribution, and P'(X) = ZP(X). For example, we know P(x, e) = P(e) * P(x | e). P(x | e) is what we want, but P(x, e) is easy to get. Let $w(x) = P'(x) / Q(x)$.

```
$latex E_{Q(X)}[w(X)] = Z$

$latex E_{P(X)}[f(X)] = E_{P'(X)}[f(X)]     / Z$
$latex                = E_{Q(X)}[f(X)w(X)]  / E_{Q(X)}[w(X)]$
$latex                = \sum f(x[m])w(x[m]) / \sum w(x[m])$
```

**Analysis**:

###12.2.3 Importance Sampling for Bayesian Networks

##12.3 Markov Chain Monte Carlo Methods

###12.3.1 Gibbs Sampling Algorithm

###12.3.2 Markov Chains

###12.3.3 Gibbs Sampling Revisited