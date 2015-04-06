#The Design of Approximation Algorithms

[the website for this book](http://www.designofapproxalgs.com/)

#1 An introduction to approximation algorithms

**Definition 1.1:** An \alpha-approximation algorithm is ...

**Definition 1.2:** A polynomial-time approximation scheme (PTAS) is ...

**Theorem 1.3:** For any MAX SNP-hard problem, there does not exist a polynomial-time approximation scheme, unless P = NP.

An example: the maximum clique problem

#2 Greedy algorithm and local search

##2.1 Scheduling jobs with deadlines on a single machine

Assume that all due dates are negative, which implies that the optimal value is always positive. We shall give a 2-approximation algorithm for this special case.

##2.2 The k-center problem

A greedy 2-approximation algorithm.

There is no \alpha-approximation algorithm for the k-center problem for \alpha < 2 unless P = NP.

##2.3 Scheduling jobs on identical parallel machines

the local search algorithm and the greedy algorithm are 2-approximation.

the longest processing time rule is a 4/3-approximation algorithm.

##2.4 The traveling salesman problem

the double-tree algorithm is a 2-approximation algorithm.

the Christofides' algorithm is a 3/2-approximation algorithm.

##2.5 Maximizing float in bank accounts

##2.6 Finding minimum-degree spanning trees
