import SHGLT.Paper.SparseCertification

namespace SHGLT.Paper

theorem generalization_two_sided
    (L Lhat rad conf : ℝ)
    (hForward : L ≤ Lhat + 2 * rad + 3 * conf)
    (hReverse : Lhat ≤ L + 2 * rad + 3 * conf) :
    |L - Lhat| ≤ 2 * rad + 3 * conf := by
  exact SHGLT.two_sided_generalization
    L Lhat rad conf hForward hReverse

theorem finite_history_candidate_miss
    {k : ℕ}
    (hk : 0 < k)
    {Theta : Type*}
    (L Lhat : Fin k → Theta → ℝ)
    (g cert shift eta : Fin k → ℝ)
    (thetaHat thetaComp : Theta)
    (epsOpt Lstar : ℝ)
    (hGen :
      ∀ i theta, |L i theta - Lhat i theta| ≤ g i)
    (hERM :
      SHGLT.stageAvg (fun i => Lhat i thetaHat) ≤
      SHGLT.stageAvg (fun i => Lhat i thetaComp) + epsOpt)
    (hComp :
      SHGLT.stageAvg (fun i => L i thetaComp) ≤ Lstar)
    (hStage :
      ∀ i,
        eta i ≤ L i thetaHat + cert i + shift i) :
    SHGLT.stageAvg eta ≤
      Lstar + 2 * SHGLT.stageAvg g + epsOpt +
      SHGLT.stageAvg cert + SHGLT.stageAvg shift := by
  exact SHGLT.finite_history_candidate_miss_bound
    hk L Lhat g cert shift eta thetaHat thetaComp
    epsOpt Lstar hGen hERM hComp hStage

end SHGLT.Paper
