#Probabilistic Graphical Models

#9 Exact Inference: Variable Elimination

#10 Exact Inference: Clique Trees

##10.1 Variable Elimination and Clique Trees

**Definition 10.2** 在cluster tree上,如果两个节点都含有x,那么中间节点也都含有x.

##10.2 Message Passing: Sum Product

这个本质还是VE,不过可以在clique tree上做dp,这样所有变量的post probablity可以在2c的时间内计算出来.

##10.3 Message Passing: Belief Update

这个挺有意思的,本质还是Sum Product.不过是用的不同的观点来看这件事情.

我们注意到一个节点i到j传递的信息$$\alpha_{i->j} = \beta_i / \alpha_{j->i}$$.

所以我们初始化所有的$$\alpha_{i->j}$$都为1,然后随意更新,直到全部稳定.每条边记录当前的消息$$u_{i->j}$$,更新$$\beta_j *= \alpha_{i->j} / u_{i->j}$$.

如果我们按照Sum Product的顺序来来更新,肯定是最高效的,所以这只是另一个角度看待Message Passing,并没有提供更好的做法.

###10.3.3 Answering Queries

**Incremental Updates**: 被观察到的变量不断增多,刷新概率. 比较暴力的方法就是每次redo the process from beginning.

这类查询很适合用Belief Update,技术角度讲,SP和BU保持的信息量一样的,而BU是更新单一变量的方法.

**Queries Outside a Clique**: 查询的变量不在同一个clique里面.

找到一个含有所有查询变量的子树,然后做VE.因为已经求出了$$\beta$$和$$u$$,所以不是对整颗树做VE,可以加速.

**Multiple Queries**: 这个算法也很简单,对每一对相邻的$$C_i$$和$$C_j$$预处理$$P(C_i,C_j)$$,每次求解可以dp.

##10.4 Constructing a Clique Tree

介绍了两种构建的方式:

**Variable Elimination** : VE的过程其实就是在创建Clique Tree,所以直接记录下来就可以了.

**Chordal Graphs** : 这个也简单,先把图转换成chordal图,然后再转成clique,这两步的精确解都是NPC问题.
  * chordal graphs: node-elimination techniques in section 9.4.3.2
  * find cliques: maximum cardinality search.

#11: Inference as Optimization*

和第十章连在一起的一章,有必要读一下.

#12: Particle-Based Approximate Inference

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

**Rejection Sampling**: do forward sampling but throw out sample where $$E \neq e$$

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

$$P(y|e) = \frac{\sum w[m]*I\{y[m]=y\}}{\sum w[m]}$$

###12.2.2 Importance Sampling

Likelihood-weighted is a special case of a very general approach called importance sampling.

It is a very interesting analysis for sampling. Let $$Q(x)$$ is a different distribution, and the key point is that $$Q(x)$$ is easy to calculate, and the relationship $$w(x) = \frac{P(X)}{Q(X)}$$ between $$P(x)$$ and $$Q(x)$$ also is easy to calculate. Then we can use $$Q(x)$$ and $$w(x)$$ to represent $$P(x)$$.

####12.2.2.1 Unnormalized Importance Sampling

```
$$E_P[f] = \frac{1}{M} \sum f(x[m])$$ we use sampling and this formula to estimate $$E_P[f]$$

$$E_{P(X)}[f(X)] = \sum P(x)f(x)$$ this is what $$E_P[f]$$ exactly is.

$$E_{P(X)}[f(X)] = E_{Q(X)}[f(X)\frac{P(X)}{Q(X)}]$$ the equality between P(X) and Q(X).

$$E_{Q(X)}[f(X)w(X)] = \frac{1}{M} \sum f(x[m])w(x[m])$$
```
We also call this estimator the unweighted importance sampling.

**Analysis**:

####12.2.2.2 Normalized Importance Sampling

If P(X) is known, we don't need to normalize it. Unfortunately, we often don't know P(X), but P'(X) which is a unnormailized distribution, and P'(X) = ZP(X). For example, we know P(x, e) = P(e) * P(x | e). We want to get P(x | e), but P(x, e) is easy to get. Let $$w(x) = P'(x) / Q(x)$$.

```
$$E_{Q(X)}[w(X)] = Z$$

$$E_{P(X)}[f(X)] = E_{P'(X)}[f(X)]     / Z$$
$$               = E_{Q(X)}[f(X)w(X)]  / E_{Q(X)}[w(X)]$$
$$               = \sum f(x[m])w(x[m]) / \sum w(x[m])$$
```

**Analysis**:

###12.2.3 Importance Sampling for Bayesian Networks

This part focuses on how many particles should be sampled, when we use weighted importance sampling.

####12.2.3.3 Ratio Likelihood Weighting

we use P(x, e) / P(e) to compute P(x | e), then it is ratio likelihood weighting...

####12.2.3.4 Normalized Likelihood Weighting

The quality of the importance sampling estimator depends largely on how close the proposal distribution Q is to the target distribution P.

If all of the evidences is at the roots, LW will work well.

If all of the evidences is at the leaf, and the posterior distribution P(X) is very different than the prior distribution Q(X), then LW cannot work.

####12.2.3.5 Conditional Probabilities: Comparison

The ratio LW has two advantages. The first one is having lower variance, and leading to more robust estimates. The second one is that it is much easier to analyze.

A significant disadvantage of ratio LW is the fact that each query y requires that we generate a new set of samples for the event y,e.

##12.3 Markov Chain Monte Carlo Methods

The idea is that the first sample may be generated from the prior, successive samples are generated from distributions that provably get closer and closer to the posterior distribution. So this approach can come over the limitation of likelihood weighting.

###12.3.1 Gibbs Sampling Algorithm

**Algorithm 12.4** Generating a Gibbs chain trajectory
```
Procedure Gibbs-Sample (
  X, // Set of variables to be sampled
  \Phi, // Set of factors defining P_\Phi
  P^0(X), // Initial state distribution
  T // Number of time steps
)
  Sample x^0 from P^0(X)
  for t = 1, ..., T
    Sample x^t_i from P_\Phi(X_i | x_{-i})
    //Change X_i in x^t
  return x^0, ..., x^T
```
We formalize this intuitive argument using a framework called Markov chain Monte Carlo (MCMC).

###12.3.2 Markov Chains
At a high level, a Markov chain is defined in terms of a graph of states over which the sampling algorithm takes a random walk.

**Algorithm 12.5** Generating a Markov chain trajectory
```
Procedure Gibbs-Sample (
  P^0(X), // Initial state distribution
  \tau, // Markov chain transition model
  T // Number of time steps
)
  Sample x^0 from P^0(X)
  for t = 1, ..., T
    Sample x^t from \tau(X^{t - 1} \to X)
  return x^0, ..., x^T
```

Intuitively, as the process converges, we would expect P^{t+1} to be close to P^t.

$$P^t(x') = P^{t+1}(x') = \sum_{x \in Val(X)} P^t(x) \tau(x \to x')$$

A stationary distribution \pi(X) is also called an invariant distribution.

In general, there is no guarantee that our MCMC sampling process converges to a stationary distribution.

If a finite state Markov chain \tau is regular, then it has a unique stationary distribution.

####12.3.2.4 Multiple Transition Models

It is a interesting analysis for a factorized structure. So if we have two independent variable X and Y, then our state space is 2D. But we can factorize it to two kernel X and Y, one graphical model is for X, and the other one is for Y.

###12.3.3 Gibbs Sampling Revisited

Gibbs sampling is easy to implement in the many graphical models where we can compute the transition probability very efficiently. It can be done based only on the Markov blanket of X_i.

###12.3.4 A Broader Class of Markov Chains

The Gibbs sampling uses only very local moves over the state space: moves that change one variable at a time. The high-probability states will form strong basins of attraction, and the chain will be very unlikely to move away from such a state. In this case, we often want to consider chains that allow a broader rang
e of moves, including much larger steps in the space. The framework we develop in this section allows us to construct a broad family of chains in a way that guarantees the desired stationary distribution.

####12.3.4.1 Detailed Balance

$$\pi(x)\tau(x \to x') = \pi(x')\tau(x' \to x)$$

####12.3.4.2 Metropolis-Hastings Algorithm

The high level idea is similar with the importance sampling.

###12.3.5 Using a Markov Chain



#13 MAP Inference
