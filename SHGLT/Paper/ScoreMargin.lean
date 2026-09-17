import SHGLT.Paper.Generalization

namespace SHGLT.Paper

theorem safety_mixture_prefix_coverage
    (lam scale q u p : ℝ)
    (hlam0 : 0 ≤ lam)
    (hlam1 : lam ≤ 1)
    (hscale0 : 0 ≤ scale)
    (hq0 : 0 ≤ q)
    (hu : scale * u = 1)
    (hp : p = (1 - lam) * q + lam * u) :
    scale * p ≥ lam := by
  have hfirst :
      0 ≤ scale * ((1 - lam) * q) :=
    mul_nonneg hscale0
      (mul_nonneg (sub_nonneg.mpr hlam1) hq0)
  rw [hp]
  calc
    scale * ((1 - lam) * q + lam * u)
        = scale * ((1 - lam) * q) + lam * (scale * u) := by ring
    _ = scale * ((1 - lam) * q) + lam := by rw [hu]; ring
    _ ≥ lam := by linarith

theorem score_margin_strict_improvement
    (lam learned : ℝ)
    (hlam0 : 0 ≤ lam)
    (hlam1 : lam < 1)
    (hlearned : 1 < learned) :
    1 < lam + (1 - lam) * learned := by
  nlinarith

end SHGLT.Paper
