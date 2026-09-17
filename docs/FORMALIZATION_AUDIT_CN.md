# 全文形式化审计

## 已在 Lean 中闭合的核心
- 奖励 gap ≤ 1；
- successive weighted miss 的链式递推；
- proposal coverage lower bound 到指数 miss bound 的单调性；
- residual-optimal marginal sum 到 greedy gap progress；
- empirical-best clean event 的 `2r` 损失；
- clean/failure expectation averaging；
- greedy-gap one-step recursion；
- 显式 finite-time regret bound 的记账代数；
- sparse-label certification 的 deterministic inclusion；
- certification failure 两类错误项的 union-bound composition；
- Rademacher two-sided deviation 的代数组合；
- approximate ERM + candidate miss + certification + shift 的 Theorem 5 聚合；
- safety mixture 推出相对 prefix coverage 至少为 `lambda`；
- score-margin strict improvement 的最终代数；
- uniform effective-search identity；
- strong-transfer sum bound；
- factorized Frobenius constraints → nuclear-budget 的 scalar tail；
- trace-complexity bound → generalization bound 的聚合。

## 尚未冒充为端到端闭合的部分
1. **Martingale Hoeffding–Azuma**：
   Mathlib 已有 `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`
   和 `measure_sum_ge_le_of_hasCondSubgaussianMGF`。
   剩余工作是把论文的 bounded martingale-difference reward process
   精确封装到 Mathlib filtration / conditional-subGaussian 接口。
2. **Lemma 6 的一般 empirical Rademacher theorem**：
   论文直接引用标准学习理论结果，本工程已经证明其下游 ERM 逻辑。
3. **Theorem 6**：
   上传稿在 vector contraction 和 matrix Bernstein 两处引用仍显示 `[?]`。
   因此只依据当前稿件，不能诚实声称这两个最深分析原语已从文稿内部闭合。
4. **渐近 O / O~**：
   当前优先验证显式 finite-time inequalities；后续可用 Mathlib `Asymptotics.IsBigO`
   再封装渐近版本。

## 编号观察
补充材料中出现 Lemma 2/4（Hoeffding–Azuma）和 Lemma 3/7（Verification accuracy）
两套编号，数学内容是同一类结果的正文/扩展版本。
