#Probabilistic Graphical Models

#16 Learning Graphical Models: Overview

##16.1 Motivation

The manual network construction is problematic for several reasons.

This task of constructing a model from a set of instances is generally called *model learning*.

Let us assume that the domain is governed by some underlying distribution P*, which is induced by some network model M* = (K*, \theta*). We are given a data set D = {d[1], ..., d[M]} of M samples from P*. The standard assumption is that the data instances are sampled independently from P*; as we discussed, such data instances are called *independent and identically distributed (IID)*. We are also given some family of models, and our task is to learn some model M in this family that defines a distribution P_M. We may want to learn only model parameters for a fixed structure, or some or all of the structure of the model. In some cases, we might wish to present a spectrum of different hypotheses, and so we might return not a single model but rather a probability distribution over models, or perhaps some estimate of our confidence in the model learned.

We first describe the set of goals that we might have when learning a model and the different evaluation metrics to which they give rise. We then discuss how learning can be viewed as an optimization problem and the issues raised by the design of that problem. Finally, we provide a detailed taxonomy of the different types of learning tasks and discuss some of their computational ramifications.

##16.2 Goals of Learning

In practice, the high-dimensional distribution involving many variables. Thus, we have to select M so as the construct the "best" approximation to M*. The notion of "best" depends on our goals. Different models will generally embody different trade-offs.

###16.2.1 Density Estimation

We can formulate our learning goal as one of *density estimation*: constructing a model M such that P is "close" to the generating distribution P*.

How to evaluate the quality of an approximation M? One commonly used option is to use the relative entropy distance measure:

  $$D(P^*\|P') = E_{\xi \sim P^*}[\log{\frac{P^*(\xi)}{P'(\xi)}}]$$

It is exactly the information gain, so

  $$D(P^*\|P') = -H_{P^*}(X) - E_{\xi \sim P^*}[\log{P'(\xi)}]$$

Then we want to maximize the second term, and it is called an expected log-likelihood.

The log-likelihood : \(l(D:M) = \log{P(D:M)}.\)

The probability that M ascribes to D is $$P(D:M) = \prod_{m=1}^M P(\xi[m]:M).$$ Taking the logarithm, we obtain $$\log{P(D:M)} = \sum_{m=1}^{M}\log{P(\xi[m]:M)},$$ which is precisely the negative of the empirical log-loss that appears inside the summation of equation (16.1).

###16.2.2 Specific Prediction Tasks

##16.3 Learning as Optimization

##16.4 Learning Tasks

#17 Parameter Estimation

##17.1 Maximum Likelihood Estimation




#18 Structure Learning in Bayesian Networks
