# Kildall's correctness proof

dataflow solver 的**正确性**证明。

> 正确性和终止性（以及解是least fixpoint）是不同的。正确性不关注终止性。CompCert关注正确性，静态分析课程关注的是终止性。

devils in details.... 看起来数据流分析证明的直觉很容易理解... 但完整地去写这个证明，却有许多细节被考虑。

我关注的三个算法需要两个solver，都基本复用CompCert中的就好，改成block-based. 

## 正确性

正确性指一旦算法最终得到一个结果，那么这个分析结果满足一些性质

1. fixpoint solution: 分析结果中（也是迭代算法本身的不变量），每个前驱的Out与后继的In满足不等式
2. fixpoint entry: 分析结果中，In[enode]>evalue
3. fixpoint invariant: meet和transf保持的性质，若在bot上也成立，那么在分析结果上也成立

`fixpoint_nodeset` 与 `fixpoint_allnodes` 是类似 `fixpoint_solution` 的定理，区别只在于初始时加入 worklist 的结点（集）不同。（start_state）。



## Available Expression Analysis

> CompCert中只使用了基于extended basic block的Ave. 

是一个must analysis（调整一下格的方向就好了），forward analysis. 就是要