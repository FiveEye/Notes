#Probabilistic Graphical Models

#Chapter 16 Learning Graphical Models: Overview

##16.1 Motivation

The manual network construction is problematic for several reasons.

This task of constructing a model from a set of instances is generally called *model learning*.

Let us assume that the domain is governed by some underlying distribution P*, which is induced by some network model M* = (K*, \theta*). We are given a data set D = {d[1], ..., d[M]} of M samples from P*. The standard assumption is that the data instances are sampled independently from P*; as we discussed, such data instances are called *independent and identically distributed (IID)*. We are also given some family of models, and our task is to learn some model M in this family that defines a distribution P_M. We may want to learn only model parameters for a fixed structure, or some or all of the structure of the model. In some cases, we might wish to present a spectrum of different hypotheses, and so we might return not a single model but rather a probability distribution over models, or perhaps some estimate of our confidence in the model learned.

We first describe the set of goals that we might have when learning a model and the different evaluation metrics to which they give rise. We then discuss how learning can be viewed as an optimization problem and the issues raised by the design of that problem. Finally, we provide a detailed taxonomy of the different types of learning tasks and iscuss some of their computational ramifications.

##16.2 Goals of Learning



#Chapter 17 Parameter Estimation

##17.1 Maximum Likelihood Estimation




#Chapter 18 Structure Learning in Bayesian Networks
