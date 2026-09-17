import SHGLT.Paper.Regret

namespace SHGLT.Paper

universe u

theorem sparse_label_certification
    {α : Type u}
    (C : Finset α)
    (base best eps0 epsTr zeta : ℝ)
    (v vhat : α → ℝ)
    (hCover :
      ∃ e0, e0 ∈ C ∧
        SHGLT.GlobalGood base best v eps0 e0)
    (hAcc :
      ∀ e ∈ C, |vhat e - v e| ≤ zeta) :
    ∀ e, SHGLT.LocalGood C vhat epsTr e →
      SHGLT.GlobalGood
        base best v (eps0 + epsTr + 2 * zeta) e := by
  exact SHGLT.sparse_label_certification
    C base best eps0 epsTr zeta v vhat hCover hAcc

theorem sparse_label_failure_bound
    (pFail pMiss pEst L rho mh zeta : ℝ)
    (hUnion : pFail ≤ pMiss + pEst)
    (hMiss : pMiss ≤ Real.exp (-L * rho))
    (hEst :
      pEst ≤ 2 * L * Real.exp (-2 * mh * zeta ^ 2)) :
    pFail ≤
      Real.exp (-L * rho) +
      2 * L * Real.exp (-2 * mh * zeta ^ 2) := by
  exact SHGLT.certification_failure_bound
    pFail pMiss pEst L rho mh zeta hUnion hMiss hEst

end SHGLT.Paper
