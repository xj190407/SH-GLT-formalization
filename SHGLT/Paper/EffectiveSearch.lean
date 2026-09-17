import SHGLT.Paper.ScoreMargin

open scoped BigOperators

namespace SHGLT.Paper

noncomputable def effectiveSearch
    {k : ℕ}
    (chit : ℝ)
    (N chi : Fin k → ℝ) : ℝ :=
  (k : ℝ) +
  (chit / (k : ℝ)) *
    Finset.univ.sum (fun i => N i / chi i)

noncomputable def uniformSearch
    {k : ℕ}
    (N : Fin k → ℝ) : ℝ :=
  (k : ℝ) +
  (1 / (k : ℝ)) *
    Finset.univ.sum (fun i => N i)

theorem uniform_coverage_identity
    {k : ℕ}
    (N : Fin k → ℝ) :
    effectiveSearch (k := k) 1 N (fun _ => 1) =
      uniformSearch (k := k) N := by
  simp [effectiveSearch, uniformSearch]

theorem strong_transfer_sum_bound
    {k : ℕ}
    (N chi : Fin k → ℝ)
    (c0 : ℝ)
    (hstage : ∀ i, N i / chi i ≤ (k : ℝ) / c0) :
    Finset.univ.sum (fun i => N i / chi i) ≤
      (k : ℝ) * ((k : ℝ) / c0) := by
  calc
    Finset.univ.sum (fun i => N i / chi i)
        ≤ Finset.univ.sum (fun _ : Fin k => (k : ℝ) / c0) := by
          exact Finset.sum_le_sum (fun i _ => hstage i)
    _ = (k : ℝ) * ((k : ℝ) / c0) := by
          simp

end SHGLT.Paper
