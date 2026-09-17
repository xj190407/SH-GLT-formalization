import SHGLT.Paper.Model

namespace SHGLT.Paper

theorem miss_chain_to_power
    (missProb : ℕ → ℝ)
    (rho : ℝ)
    (hrho1 : rho ≤ 1)
    (h0 : missProb 0 ≤ 1)
    (hstep :
      ∀ j, missProb (j + 1) ≤ missProb j * (1 - rho)) :
    ∀ L, missProb L ≤ (1 - rho) ^ L := by
  intro L
  induction L with
  | zero =>
      simpa using h0
  | succ L ih =>
      have hq : 0 ≤ 1 - rho := sub_nonneg.mpr hrho1
      calc
        missProb (Nat.succ L)
            ≤ missProb L * (1 - rho) := by
              simpa [Nat.succ_eq_add_one] using hstep L
        _ ≤ (1 - rho) ^ L * (1 - rho) :=
              mul_le_mul_of_nonneg_right ih hq
        _ = (1 - rho) ^ (Nat.succ L) := by
              rw [pow_succ]

theorem prefix_miss_from_coverage_lower_bound
    (missProb b rho rhoLower : ℝ)
    (hb : 0 ≤ b)
    (hrho : rhoLower ≤ rho)
    (hmiss : missProb ≤ Real.exp (-b * rho)) :
    missProb ≤ Real.exp (-b * rhoLower) := by
  calc
    missProb ≤ Real.exp (-b * rho) := hmiss
    _ ≤ Real.exp (-b * rhoLower) := by
      apply Real.exp_le_exp.mpr
      have hmul : b * rhoLower ≤ b * rho :=
        mul_le_mul_of_nonneg_left hrho hb
      linarith

theorem hit_from_miss_bound
    (hit miss bound : ℝ)
    (hlink : hit = 1 - miss)
    (hmiss : miss ≤ bound) :
    hit ≥ 1 - bound := by
  rw [hlink]
  linarith

end SHGLT.Paper
