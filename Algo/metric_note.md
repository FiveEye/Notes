#Notes on Metric Embedding

[15-859(J): Algorithmic Applications of Metric Embeddings](http://www.cs.cmu.edu/~./anupamg/metrics/)

##Random tree embedding

Any n-point metric O(\log{n})-probabilistically embeds into a distribution D of trees; furthermore, samples from this distribution can be generated in polynomial time.

###8.5 Bartal's Theorem

**Theorem 9.1.2** Given a graph G = (V, E) with edge lengths, and a parameter \delta, there exists a procedure that deletes edges E' such that:
  1. Each connected component C in (V, E- E') has (weak) diameter smaller than \delta.
  2. $$Pr[\text{edge e is cut}] \le 4 \log{n} \times (d_e / \delta)$$.

###9.3 Graph Cutting Procedure II

**Algorithm** Cut-2(G, \delta)
  1. Pick a radius R uniformly at random from [\delta / 4, \delta / 2].
  2. Pick a random permutation \sigma \in S_n, which defines and order $$<_\sigma$$ on the vertices.
  3. For every vertex v_i, define a ball B_i = B(v_i, R).
  4. Assign each vertex to the "first" ball it lies in. Formally, define $$\hat{B_i} = B_i - \bigcup_{j <_\sigma i} B_j$$.
  5. Delete all edges in $$\partial B_i$$ for all i.
