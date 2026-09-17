import SHGLT.Paper.Verification

namespace SHGLT.Paper

theorem gap_step_from_gain
    (Dprev Dnext gain a err : ℝ)
    (hGain : gain ≥ a * Dprev - err)
    (hNext : Dnext = Dprev - gain) :
    Dnext ≤ (1 - a) * Dprev + err := by
  rw [hNext]
  nlinarith

theorem transfer_dependent_regret_finite
    (regret verifyCost exploitGap
      m Ntr LT T epsPow k r : ℝ)
    (hT : 0 < T)
    (hRegret :
      regret ≤ verifyCost + T * exploitGap)
    (hVerify :
      verifyCost ≤ m * Ntr * LT)
    (hExploit :
      exploitGap ≤ epsPow + 2 * k * r + 1 / T) :
    regret ≤
      m * Ntr * LT +
      T * epsPow +
      2 * k * T * r +
      1 := by
  have hT0 : 0 ≤ T := le_of_lt hT
  have hmul :
      T * exploitGap ≤
        T * (epsPow + 2 * k * r + 1 / T) :=
    mul_le_mul_of_nonneg_left hExploit hT0
  have hTne : T ≠ 0 := ne_of_gt hT
  calc
    regret ≤ verifyCost + T * exploitGap := hRegret
    _ ≤ m * Ntr * LT +
        T * (epsPow + 2 * k * r + 1 / T) := by
          exact add_le_add hVerify hmul
    _ = m * Ntr * LT +
        T * epsPow +
        2 * k * T * r +
        1 := by
          field_simp [hTne]
          ring

theorem absorb_approximation_term
    (T epsPow m Ntr : ℝ)
    (h : T * epsPow ≤ m * Ntr) :
    m * Ntr + T * epsPow ≤ 2 * (m * Ntr) := by
  linarith

end SHGLT.Paper
