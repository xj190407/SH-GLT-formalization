# 论文结果 → Lean 文件映射

| 论文结果 | Lean 文件 | 状态 |
|---|---|---|
| Proposition 2 Budget–coverage tradeoff | `Paper/PrefixCoverage.lean` | successive-miss 与 coverage→exp miss 已证 |
| Lemma 1 Transfer-enhanced greedy step | `Paper/GreedyProgress.lean` | residual-sum→gap 的关键收尾已证 |
| Lemma 2 / 4 Hoeffding–Azuma | `Paper/MathlibAzuma.lean` | Mathlib 标准定理已接入，MDS→接口封装待继续 |
| Lemma 3 / 7 Verification accuracy | `Paper/Verification.lean` | clean-event 2r + failure expectation 已证 |
| Theorem 1 / 3 Transfer-dependent regret | `Paper/Regret.lean` | 显式 finite-time regret bookkeeping 已证 |
| Corollaries 1–3 | `Paper/EffectiveSearch.lean` | uniform identity / strong-transfer sum 核心已证 |
| Proposition 4 Score-margin certificate | `Paper/ScoreMargin.lean` | safety support + strict-improvement algebra 已证 |
| Lemma 5 Sparse-label certification | `Paper/SparseCertification.lean` | deterministic inclusion + failure composition 已证 |
| Lemma 6 Uniform historical generalization | `Paper/Generalization.lean` | two-sided/ERM downstream 已证；一般 Rademacher theorem 外部 |
| Theorem 5 Candidate-miss bound | `Paper/Generalization.lean` | approximate ERM + transfer 聚合已证 |
| Theorem 6 Trace-norm complexity | `Paper/TraceNorm.lean` | aggregation 已证；vector contraction / matrix Bernstein 原语待补 |
