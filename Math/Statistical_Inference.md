#Statistical Inference

# 1 Probability Theory

## 1.1 Set Theory

**Definition 1.1.1** The set, S, of all possible outcomes of a particular experiment is called the sample space for the experiment.

**Definition 1.1.2** An event is any collection of possible outcomes of an experiment, that is, any subset of S(including S itself).

**Definition 1.1.5** Two events $$A$$ and $$B$$ are disjoint if $$A \cap B = \emptyset$$. The events $$A_1, A_2, \dots$$ are pairwise disjoint if $$A_i \cap B_j = \emptyset$$ for all $$i \neq j$$.

**Definition 1.1.6** If $$A_1, A_2, \dots$$ are pairwise disjoint and $$\cup_{i=1}^
{\infty}A_i = S$$, then the collection $$A_1, A_2, \dots$$ forms a partition of $$S$$.

## 1.2 Basics of Probability Theory

**Definition 1.2.1** A collection of subset of $$S$$ is called a sigma algebra (or Borel field), denoted by B, if it satisfies the following three properties:

  * $$\emptyset \in B$$.
  * If $$A \in B$$, then $$A^c \in B$$.
  * If $$A_1, A_2, \dots \in B$$, then $$\cup_{i=1}^{\infty}A_i \in B$$.

**Definition 1.2.4** Given a sample space $$S$$ and an associated sigma algebra $$B$$, a probability function $$P$$ with domain $$B$$ that satisfies
  * $$P(A) \ge 0$$ for all $$A \in B$$.
  * $$P(S) = 1$$.
  * If $$A_1, A_2, \dots \in B$$ are pairwise disjoint, then $$P(\cup_{i=1}^{\infty}A_i)= \sum_{i=1}^{\infty}P(A_i)$$.


## 1.3 Conditional Probability and Independence

## 1.4 Random Variables

## 1.5 Distribution Functions

## 1.6 Density and Mass Functions


# 2 Transformations and Expectations

## 2.1 Distribution of Functions of a Random Variable

## 2.2 Expected Values

## 2.3 Moments and Moment Generating Functions

## 2.4 Differentiating Under an Integral Sign

## 2.6 Miscellanea

# 3 Common Families of Distributions

## 3.1 Introduction

## 3.2 Discrete Distribution

**Discrete Uniform Distribution**
$$
P(X=x|N) = \frac{1}{N}, \quad x = 1,2,\dots,N. \\
\mathrm{E}X = \frac{N+1}{2} \\
\mathrm{Var}X = \frac{(N+1)(N-1)}{12} \\
$$

**Hypergeometric Distribution**

$$
P(X=x|N,M,K) = \frac{\binom{M}{x}\binom{N-M}{K-x}}{\binom{N}{K}}, \quad x = 0,1,\dots,K. \\
\mathrm{E}X = \frac{KM}{N} \\
\mathrm{Var}X = \frac{KM}{N}(\frac{(N-M)(N-K)}{N(N-1)}) \\
$$

**Binomial Distribution**

$$
P(X=x|n,p) = \binom{n}{x}p^x(1-p)^{n-x}, \quad x=0,1,\dots,n. \\
\mathrm{E}X = np \\
\mathrm{Var}X = np(1-p) \\
\mathrm{M}_X(t) = [pe^t + (1-p)]^n \\
$$

**Poisson Distribution**

$$
P(X = x | \lambda) = \frac{e^{-\lambda}\lambda^x}{x!}, \quad x = 0, 1, \dots \\
\mathrm{E}X = \lambda \\
\mathrm{Var}X = \lambda \\
\mathrm{M}_X(t) = e^{\lambda(e^\lambda-1)} \\
$$

**Negative Binomial Distribution**

$$
P()
$$


**Geometric Distribution**

## 3.3 Continuous Distribution

**Uniform Distribution**

**Gamma Distribution**

**Normal Distribution**

**Beta Distribution**

**Cauchy Distribution**

**Lognormal Distribution**

**Double Exponential Distribution**

## 3.4 Exponential Families



# 4 Multiple Random Variables