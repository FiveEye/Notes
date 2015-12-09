---
layout: post
title: "Statistical Inference 1"
date: 2015-12-07 17:28:00 -0800
categories: Math
---

#Statistical Inference 1

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

## 1.8 Miscellanea

# 2 Transformations and Expectations

## 2.1 Distribution of Functions of a Random Variable

**Theorem 2.1.4** Let $$X$$ have pdf $$f_X(x)$$ and let $$Y = g(X)$$, where $$g$$ is a monotone function. Let $$X$$ and $$Y$$ be defined by (2.1.7). Suppose that $$f_X(x)$$ is continuous on $$X$$ and that $$g^{-1}(y)$$ has a continuous derivative on $$Y$$. Then the pdf of $$Y$$ is given by

$$
f_Y(y) = f_X(g^{-1}(y))|\frac{d}{dy}g^{-1}(y)| \quad y \in Y
$$


## 2.2 Expected Values

## 2.3 Moments and Moment Generating Functions

## 2.4 Differentiating Under an Integral Sign

**Theorem 2.4.1 (Leibnitz's Rule)** If $$f(x,\theta), a(\theta), b(\theta)$$ are differentiable with respect to $$\theta$$, then
$$
\frac{d}{d\theta}\int_{a(\theta)}^{b(\theta)}f(x,\theta)dx=f(b(\theta),\theta)\frac{d}{d\theta}b(\theta)
 - f(a(\theta),\theta)\frac{d}{d\theta}a(\theta)+\int_{a(\theta)}^{b(\theta)}\frac{d}{d\theta}f(x,\theta)dx
$$

Notice that if $$a(\theta)$$ and $$b(\theta)$$ are constant, we have a special case of Leibnitz's Rule:

$$
\frac{d}{d\theta}\int_{a}^{b}f(x,\theta)dx=\int_{a}^{b}\frac{d}{d\theta}f(x,\theta)dx
$$


## 2.6 Miscellanea

# 3 Common Families of Distributions

## 3.1 Introduction

## 3.2 Discrete Distribution

**Discrete Uniform Distribution**

$$
\begin{eqnarray}
P(X=x|N) &=& \frac{1}{N}, \quad x = 1,2,\dots,N. \\
\mathrm{E}X &=& \frac{N+1}{2} \\
\mathrm{Var}X &=& \frac{(N+1)(N-1)}{12} \\
\end{eqnarray}
$$

**Hypergeometric Distribution**

$$
\begin{eqnarray}
P(X=x|N,M,K) &=& \frac{\binom{M}{x}\binom{N-M}{K-x}}{\binom{N}{K}}, \quad x = 0,1,\dots,K. \\
\mathrm{E}X &=& \frac{KM}{N} \\
\mathrm{Var}X &=& \frac{KM}{N}(\frac{(N-M)(N-K)}{N(N-1)}) \\
\end{eqnarray}
$$

**Binomial Distribution**

$$
\begin{eqnarray}
P(X=x|n,p) &=& \binom{n}{x}p^x(1-p)^{n-x}, \quad x=0,1,\dots,n. \\
\mathrm{E}X &=& np \\
\mathrm{Var}X &=& np(1-p) \\
\mathrm{M}_X(t) &=& [pe^t + (1-p)]^n \\
\end{eqnarray}
$$

**Poisson Distribution**

$$
\begin{eqnarray}
P(X = x | \lambda) &=& \frac{e^{-\lambda}\lambda^x}{x!}, \quad x = 0, 1, \dots \\
\mathrm{E}X &=& \lambda \\
\mathrm{Var}X &=& \lambda \\
\mathrm{M}_X(t) &=& e^{\lambda(e^\lambda-1)} \\
\end{eqnarray}
$$

**Negative Binomial Distribution**

$$
\begin{eqnarray}
P(X=x|r,p) &=& \binom{x-1}{r-1}p^r(1-p)^{x-r}, \quad x = r, r + 1, \dots \\
\mathrm{E}X &=& r\frac{1-p}{p} \\
\mathrm{Var}X &=& \frac{r(1-p)}{p^2} \\
\end{eqnarray}
$$


**Geometric Distribution**

$$
\begin{eqnarray}
P(X=x|p) &=& p(1-p)^{x-1}, \quad x = 1, 2, \dots \\
\mathrm{E}X &=& \frac{1}{p} \\
\mathrm{Var}X &=& \frac{1-p}{p^2} \\
\end{eqnarray}
$$

## 3.3 Continuous Distribution

**Uniform Distribution**

$$
\begin{eqnarray}
f(x|a,b) &=& 1/(b - a), \quad x \in [a, b] \\
\mathrm{E}X &=& (b+a)/2 \\
\mathrm{Var}X &=& (b-a)^2/12 \\
\end{eqnarray}
$$

**Gamma Distribution**

$$\Gamma(\alpha) = \int_0^{\infty} t^{\alpha-1}e^{-t}dt$$.

$$
\begin{eqnarray}
f(x|\alpha, \beta) &=& \frac{1}{\Gamma(\alpha)\beta^\alpha}x^{\alpha-1}e^{-x/\beta}, \quad 0 < x < \infty,\alpha > 0, \beta > 0\\
\mathrm{E}X &=& \alpha\beta\\
\mathrm{Var}X &=& \alpha\beta^2\\
\mathrm{M}_X(t) &=& (1-\beta t)^{-\alpha}\\
\end{eqnarray}
$$

**Normal Distribution**

$$
\begin{eqnarray}
f(x|\mu,\sigma) &=& \frac{1}{\sqrt{2\pi}}e^{-(x-\mu)^2/(2\sigma^2)}, \quad -\infty < x < \infty\\
\mathrm{E}X &=& \mu\\
\mathrm{Var}X &=& \sigma^2\\
\end{eqnarray}
$$

**Beta Distribution**

$$B(\alpha, \beta)= \int_0^1 x^{\alpha-1}(1-x)^{\beta-1}dx$$.

$$
\begin{eqnarray}
f(x|\alpha,\beta) &=& \frac{1}{B(\alpha,\beta)}x^{\alpha-1}(1-x)^{\beta-1}, \quad 0 < x < 1, \alpha > 0, \beta > 0\\
\mathrm{E}X &=& \frac{\alpha}{\alpha+\beta}\\
\mathrm{Var}X &=& \frac{\alpha \beta}{(\alpha + \beta)^2(\alpha + \beta + 1)}\\
\end{eqnarray}
$$

**Cauchy Distribution**

$$
\begin{eqnarray}
f(x|\theta) &=& \frac{1}{\pi}\frac{1}{1+(x-\theta)^2}, \quad -\infty < x < \infty, -\infty < \theta < \infty\\
\mathrm{E}|X| &=& \infty\\
\end{eqnarray}
$$

**Lognormal Distribution**

$$
\begin{eqnarray}
f(x|\mu,\sigma^2) &=& \frac{1}{\sqrt{2\pi}\sigma}\frac{1}{x}e^{-(\log{x}-\mu)^2/(2\sigma^2)}, \quad 0 < x < \infty, -\infty < \mu < \infty, \sigma > 0\\
\mathrm{E}X &=& e^{\mu + (\sigma^2/2)}\\
\mathrm{Var}X &=& e^{2(\mu+\sigma^2)}-e^{2\mu+\sigma^2}\\
\end{eqnarray}
$$

**Double Exponential Distribution**

$$
\begin{eqnarray}
f(x|\mu,\sigma) &=& \frac{1}{2\sigma}e^{-|x-\mu|/\sigma}, \quad -\infty < x < \infty, -\infty < \mu < \infty, \sigma > 0\\
\mathrm{E}X &=& \mu\\
\mathrm{Var}X &=& 2\sigma^2\\
\end{eqnarray}
$$

## 3.4 Exponential Families

A family of pdfs or pmfs is called an exponential family if it can be expressed as

$$
f(x|\theta) = h(x)c(\theta)\exp(\sum_{i=1}^k w_i(\theta)t_i(x)).
$$

## 3.5 Location and Scale Families

## 3.6 Inequalities and Identities

## 3.8 Miscellanea

# 4 Multiple Random Variables

## 4.1 Joint and Marginal Distributions

The marginal pmf

## 4.2 Conditional Distributions and Independence

## 4.3 Bivariate Transformations

## 4.4 Hierarchical Models and Mixture Distributions

## 4.5 Covariance and Correlation

$$\mathrm{E}X = \mu_X, \mathrm{E}Y = \mu_Y, \mathrm{Var}X = \sigma^2_X, \mathrm{Var}Y = \sigma^2_Y$$.

covariance: $$\mathrm{Cov}(X,Y) = \mathrm{E}((X - \mu_X)(Y - \mu_Y))$$

correlation: $$\rho_{XY} = \mathrm{Cov}(X,Y)/(\sigma_X \sigma_Y)$$

**Theorem 4.5.3** For any random variables $$X$$ and $$Y$$,

$$
  \mathrm{Cov}(X,Y) = \mathrm{E}XY - \mu_X \mu_Y.
$$

**Theorem 4.5.5** If $$X$$ and $$Y$$ are independent random variables, then $$\mathrm{Cov}(X,Y) = 0$$ and $$\rho_{XY} = 0$$.


**Theorem 4.5.6** If $$X$$ and $$Y$$ are any two random variables and $$a$$ and $$b$$ are any two constants, then

$$
  \mathrm{Var}(aX+bY)=a^2\mathrm{Var}X+b^2\mathrm{Var}Y+2ab\mathrm{Cov}(X,Y)
$$.

**Theorem 4.5.7** For any random variables $$X$$ and $$Y$$,

  * $$-1 \le \rho_{XY} \le 1$$.
  * $$\rho_{XY}^2 = 1$$ if and only if there exist numbers $$a \neq 0$$ and $$b$$ such that $$P(Y = aX + b) = 1$$. If $$\rho_{XY}=1$$, then $$a > 0$$, and if $$\rho_{XY} = -1$$, then $$a < 0$$.


## 4.6 Multivariate Distributions




## 4.7 Inequalities

### 4.7.1 Numerical Inequalities

**Lemma 4.7.1** Let a and b be any positive numbers, and let p and q be any positive numbers (necessarily greater than 1) satisfying

$$
  1/p + 1/q = 1.
$$

Then,

$$
  (1/p)a^p + (1/q)b^q \ge ab
$$
with equality if and only $$a^p = b^q$$.

**Theorem 4.7.2 (Holder's Inequality)** Let X and Y be any two random variables, and let p and q satisfy. Then

$$
  |\mathrm{E}XY| \le \mathrm{E}|XY| \le (\mathrm{E}|X|^p)^{1/p} (\mathrm{E}|Y|^q)^{1/q}.
$$

**Theorem 4.7.5 (Minkowski's Inequality)** Let X and Y be any two random variables. Then for $$1 \le p < \infty$$, 

$$
  [E|X+Y|^p]^{1/p} \le [E|X|^p]^{1/p} + [E|Y|^p]^{1/p}.
$$

### 4.7.2 Functional Inequalities

**Theorem 4.7.7 (Jensen's Inequality)** For any random variable X, if g(x) is a convex function, then

$$
  \mathrm{E}(X) \ge g(\mathrm{E}X).
$$

**Theorem 4.7.9 (Covariance Inequality)** Let $$X$$ be any random variable and $$g(x)$$ and $$h(x)$$ any functions such that $$\mathrm{E}g(X)$$, $$\mathrm{E}h(X)$$, and $$\mathrm{E}(g(X)h(X))$$ exist.

  * If $$g(x)$$ is a nondecreasing function and $$h(x)$$ is a nonincreasing function, then
    
    $$
    \mathrm{E}(g(X)h(X)) \le (\mathrm{E}g(X))(\mathrm{E}h(X)).
    $$
    
  * If $$g(x)$$ and $$h(x)$$ are either both nondecreasing or both nonincreasing, then
    
    $$
    \mathrm{E}(g(X)h(X)) \ge (\mathrm{E}g(X))(\mathrm{E}h(X)).
    $$

## 4.9 Miscellanea

### 4.9.1 The Exchange Paradox

### 4.9.2 More on the Arithmetic-Geometric-Harmonic Mean Inequalilty

### 4.9.3 The Borel Paradox





















