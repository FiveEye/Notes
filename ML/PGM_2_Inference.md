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

**Incremental Updates** : 被观察到的变量不断增多,刷新概率. 比较暴力的方法就是每次redo the process from beginning.

这类查询很适合用Belief Update,技术角度讲,SP和BU保持的信息量一样的,而BU是更新单一变量的方法.

**Queries Outside a Clique** : 查询的变量不在同一个clique里面.

找到一个含有所有查询变量的子树,然后做VE.因为已经求出了$\beta$和$\u$,所以不是对整颗树做VE,可以加速.

**Multiple Queries** :

这个算法也很简单,对每一对相邻的$C_i$和$C_j$预处理$P(C_i,C_j)$,每次求解可以dp.

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
