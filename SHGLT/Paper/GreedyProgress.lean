import SHGLT.Paper.PrefixCoverage

namespace SHGLT.Paper

theorem progress_from_residual_sum
    (expectedZ residualSum gap c k : ℝ)
    (hk : 0 < k)
    (hc : 0 ≤ c)
    (hZ : expectedZ ≥ (c / k) * residualSum)
    (hGap : gap ≤ residualSum) :
    expectedZ ≥ (c / k) * gap := by
  have hcoef : 0 ≤ c / k :=
    div_nonneg hc (le_of_lt hk)
  have hscale :
      (c / k) * gap ≤ (c / k) * residualSum :=
    mul_le_mul_of_nonneg_left hGap hcoef
  linarith

theorem best_marginal_ge_gap_div
    (gap bestMarginal k : ℝ)
    (hk : 0 < k)
    (hgap : gap ≤ k * bestMarginal) :
    bestMarginal ≥ gap / k := by
  have h : gap / k ≤ bestMarginal := by
    exact (div_le_iff₀ hk).2 (by
      simpa [mul_comm] using hgap)
  exact h




end SHGLT.Paper
