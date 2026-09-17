# SHGLT_Paper_Full_Lean

这是按上传的 `SH-GLT.pdf` 正文与补充材料重新整理的 Lean 4 + Mathlib 验证工程。

## ReasLab 导入
1. New Project
2. Import from ZIP
3. 上传 `SHGLT_Paper_Full_Lean_ReasLab.zip`
4. 选 Theorem Proving
5. 打开 `Main.lean`

首次编译建议按模块逐层加载：
`Model -> PrefixCoverage -> GreedyProgress -> Verification -> Regret -> SparseCertification -> Generalization -> ScoreMargin -> EffectiveSearch -> TraceNorm -> MathlibAzuma`

详细覆盖情况见 `docs/FORMALIZATION_AUDIT_CN.md`。
