import SHGLT.Paper.EffectiveSearch

namespace SHGLT.Paper

theorem factorized_capacity
    (Lambda normA normB normK : ℝ)
    (hLambda : 0 ≤ Lambda)
    (hB0 : 0 ≤ normB)
    (hA : normA ≤ Real.sqrt Lambda)
    (hB : normB ≤ Real.sqrt Lambda)
    (hSub : normK ≤ normA * normB) :
    normK ≤ Lambda := by
  exact SHGLT.factorized_nuclear_capacity
    Lambda normA normB normK hLambda hB0 hA hB hSub

theorem trace_complexity_to_generalization
    (rad complexityBound conf g : ℝ)
    (hRad : rad ≤ complexityBound)
    (hg : g = 2 * rad + conf) :
    g ≤ 2 * complexityBound + conf := by
  rw [hg]
  linarith

end SHGLT.Paper
