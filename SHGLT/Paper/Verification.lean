import SHGLT.Paper.GreedyProgress

namespace SHGLT.Paper

universe u

theorem verification_clean_event
    {α : Type u}
    (C : Finset α)
    (v vhat : α → ℝ)
    (chosen star : α)
    (r : ℝ)
    (hChosenC : chosen ∈ C)
    (hStarC : star ∈ C)
    (hChosenEmp : ∀ e ∈ C, vhat chosen ≥ vhat e)
    (hAcc : ∀ e ∈ C, |vhat e - v e| ≤ r) :
    v chosen ≥ v star - 2 * r := by
  exact SHGLT.verification_accuracy
    C v vhat chosen star r hChosenC hStarC hChosenEmp hAcc

theorem verification_expected_penalty
    (selected Z r delta : ℝ)
    (hZ1 : Z ≤ 1)
    (hr : 0 ≤ r)
    (hdelta0 : 0 ≤ delta)
    (hsel :
      selected ≥ (1 - delta) * (Z - 2 * r)) :
    selected ≥ Z - 2 * r - delta := by
  have hdeltaZ : delta * Z ≤ delta := by
    calc
      delta * Z ≤ delta * 1 :=
        mul_le_mul_of_nonneg_left hZ1 hdelta0
      _ = delta := by ring
  have hrd : 0 ≤ 2 * r * delta := by positivity
  nlinarith [hsel, hdeltaZ, hrd]

theorem verification_union_bookkeeping
    (poolFail b p delta : ℝ)
    (hUnion : poolFail ≤ b * p)
    (hBudget : b * p ≤ delta) :
    poolFail ≤ delta := by
  exact le_trans hUnion hBudget

end SHGLT.Paper
