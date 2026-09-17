import Mathlib

/-!
# SH-GLT theory verification (Lean 4 + Mathlib)

This file formalizes the logical core of the lemmas/theorems in `glt.txt`,
with the algorithmic/statistical assumptions exposed explicitly.

Design principle:
* no proof-hole commands;
* no hidden axioms;
* deterministic inequalities are proved in Lean;
* standard external statistical results (Hoeffding and empirical
  Rademacher generalization) appear only as hypotheses at the point where
  the paper invokes them;
* asymptotic `O`, `Theta`, and `O~` notation is replaced by explicit
  pointwise inequalities/certificates.

The release implementation uses the same mathematical ingredients:
state-conditioned low-rank scores, a safety-mixture proposal, sparse
historical candidate sets, weighted sampling without replacement, and
fresh repeated full-bandit verification pulls.

Important edge conditions made explicit here:
  k > 0,
  nonempty candidate pools / positive repeat counts where a maximum or
  confidence radius is used,
  and k*T > 1 for the `log(kT)` favorable-transfer budget.
-/

open scoped BigOperators

namespace SHGLT

/-!
ReasLab compatibility fixes in this revision:
* do not use reserved token `λ` as an identifier;
* mark real-valued definitions using division/exp as `noncomputable`;
* avoid parser-sensitive `∑ i in ...` notation by using `Finset.sum`;
* make multiplication-by-one simplifications explicit in the greedy-step proof.
-/

/-! ## 1. Problem-level definitions -/

universe u

section ProblemModel

variable {α : Type u} [DecidableEq α]

/-- Marginal gain of adding arm `e` to state `S`. -/
def marginal (f : Finset α → ℝ) (S : Finset α) (e : α) : ℝ :=
  f (insert e S) - f S

/--
A compact abstraction of the task reward assumptions used by the paper.
`bounded` models `f(S) ∈ [0,1]`, inherited from bounded rewards.
-/
structure RewardModel (α : Type u) [DecidableEq α] where
  f : Finset α → ℝ
  normalized : f ∅ = 0
  bounded : ∀ S, 0 ≤ f S ∧ f S ≤ 1
  monotone : ∀ {A B : Finset α}, A ⊆ B → f A ≤ f B
  diminishing :
    ∀ {A B : Finset α} {e : α},
      A ⊆ B → e ∉ B →
      marginal f A e ≥ marginal f B e

end ProblemModel


/-! ## 2. Capacity and safety-mixture sanity checks -/

/--
The paper uses
  ||K||_* ≤ ||A||_F ||B||_F
and
  ||A||_F, ||B||_F ≤ sqrt Λ
to conclude ||K||_* ≤ Λ.

The matrix-specific submultiplicative inequality is passed in as `hSub`;
the remaining scalar argument is proved here.
-/
theorem factorized_nuclear_capacity
    (Λ normA normB normK : ℝ)
    (hΛ : 0 ≤ Λ)
    (hB0 : 0 ≤ normB)
    (hA : normA ≤ Real.sqrt Λ)
    (hB : normB ≤ Real.sqrt Λ)
    (hSub : normK ≤ normA * normB) :
    normK ≤ Λ := by
  have hprod :
      normA * normB ≤ Real.sqrt Λ * Real.sqrt Λ := by
    exact mul_le_mul hA hB hB0 (Real.sqrt_nonneg Λ)
  have hsqrt : Real.sqrt Λ * Real.sqrt Λ = Λ := by
    simpa [pow_two] using Real.sq_sqrt hΛ
  calc
    normK ≤ normA * normB := hSub
    _ ≤ Real.sqrt Λ * Real.sqrt Λ := hprod
    _ = Λ := hsqrt

/--
The uniform safety component gives every remaining arm positive mass
whenever `0 < λ < 1` and the number of remaining arms is positive.
-/
theorem safety_mixture_positive
    (lam q N : ℝ)
    (hlam0 : 0 < lam)
    (hlam1 : lam < 1)
    (hq : 0 ≤ q)
    (hN : 0 < N) :
    0 < (1 - lam) * q + lam / N := by
  have hfirst : 0 ≤ (1 - lam) * q :=
    mul_nonneg (sub_nonneg.mpr (le_of_lt hlam1)) hq
  have hsecond : 0 < lam / N := div_pos hlam0 hN
  linarith

/--
If `pLocal ≤ pGlobal`, then the exponential miss surrogate for the true
global-good set is no larger than that for the certified local-good set.
This is the monotonicity step used in the historical-to-test transfer.
-/
theorem hit_loss_monotone
    (b pLocal pGlobal : ℝ)
    (hb : 0 ≤ b)
    (hMass : pLocal ≤ pGlobal) :
    Real.exp (-b * pGlobal) ≤ Real.exp (-b * pLocal) := by
  apply Real.exp_le_exp.mpr
  have hnonneg : 0 ≤ b * (pGlobal - pLocal) :=
    mul_nonneg hb (sub_nonneg.mpr hMass)
  nlinarith


/-! ## 3. Sparse-label certification -/

section SparseCertification

variable {α : Type u}

/--
Equivalent "max-free" form of the empirical local-good condition:
`e` lies in the candidate pool and is within `epsTr` of every candidate's
empirical value.
-/
def LocalGood
    (C : Finset α) (vhat : α → ℝ) (epsTr : ℝ) (e : α) : Prop :=
  e ∈ C ∧ ∀ a ∈ C, vhat e ≥ vhat a - epsTr

/--
`GlobalGood base best v eps e` means the marginal of `e`,
`v e - base`, is within `eps` of the best remaining marginal `best`.
-/
def GlobalGood
    (base best : ℝ) (v : α → ℝ) (eps : ℝ) (e : α) : Prop :=
  best - (v e - base) ≤ eps

/--
Deterministic core of Lemma "Sparse-label certification".

If the candidate pool contains an `eps0`-globally-good arm, all empirical
candidate means are `zeta`-accurate, and `e` is empirically local-good,
then `e` is globally good at tolerance

  eps0 + epsTr + 2*zeta.

This is the key inclusion
  Ghat_local ⊆ G_global(eps_eff).
-/
theorem sparse_label_certification
    (C : Finset α)
    (base best eps0 epsTr zeta : ℝ)
    (v vhat : α → ℝ)
    (hCover :
      ∃ e0, e0 ∈ C ∧ GlobalGood base best v eps0 e0)
    (hAcc :
      ∀ e ∈ C, |vhat e - v e| ≤ zeta) :
    ∀ e, LocalGood C vhat epsTr e →
      GlobalGood base best v (eps0 + epsTr + 2 * zeta) e := by
  intro e he
  rcases hCover with ⟨e0, he0C, he0Good⟩
  rcases he with ⟨heC, heLocal⟩
  have hLocal0 : vhat e ≥ vhat e0 - epsTr :=
    heLocal e0 he0C
  have heAcc := abs_le.mp (hAcc e heC)
  have he0Acc := abs_le.mp (hAcc e0 he0C)
  dsimp [GlobalGood] at he0Good ⊢
  linarith

/--
Probability bookkeeping part of sparse-label certification.

`hMiss` is the weighted-without-replacement coverage bound.
`hEst` is the Hoeffding + union bound over the historical candidates.
`hUnion` is the failure-event union bound.

Lean then verifies the claimed certification-failure inequality exactly.
-/
theorem certification_failure_bound
    (pFail pMiss pEst L rho mh zeta : ℝ)
    (hUnion : pFail ≤ pMiss + pEst)
    (hMiss : pMiss ≤ Real.exp (-L * rho))
    (hEst :
      pEst ≤ 2 * L * Real.exp (-2 * mh * zeta ^ 2)) :
    pFail ≤
      Real.exp (-L * rho) +
      2 * L * Real.exp (-2 * mh * zeta ^ 2) := by
  calc
    pFail ≤ pMiss + pEst := hUnion
    _ ≤ Real.exp (-L * rho) +
        2 * L * Real.exp (-2 * mh * zeta ^ 2) :=
      add_le_add hMiss hEst

end SparseCertification


/-! ## 4. Uniform historical generalization: algebraic core -/

/--
The empirical Rademacher theorem is a standard external statistical result.
Once its two one-sided inequalities are available, the claimed absolute
two-sided deviation follows exactly.
-/
theorem two_sided_generalization
    (L Lhat rad conf : ℝ)
    (hForward : L ≤ Lhat + 2 * rad + 3 * conf)
    (hReverse : Lhat ≤ L + 2 * rad + 3 * conf) :
    |L - Lhat| ≤ 2 * rad + 3 * conf := by
  rw [abs_le]
  constructor <;> linarith


/-! ## 5. Finite-history ERM and candidate-miss transfer -/

section FiniteHistory

variable {k : ℕ}

/-- Average over `k` stages. Theorems using it assume `k > 0`. -/
noncomputable def stageAvg (x : Fin k → ℝ) : ℝ :=
  (∑ i, x i) / (k : ℝ)

theorem stageAvg_mono
    (hk : 0 < k)
    {x y : Fin k → ℝ}
    (hxy : ∀ i, x i ≤ y i) :
    stageAvg x ≤ stageAvg y := by
  have hsum : (∑ i, x i) ≤ ∑ i, y i := by
    exact Finset.sum_le_sum (fun i _ => hxy i)
  have hinv : 0 ≤ ((k : ℝ)⁻¹) := by positivity
  simpa [stageAvg, div_eq_mul_inv] using
    mul_le_mul_of_nonneg_right hsum hinv

theorem stageAvg_add
    (x y : Fin k → ℝ) :
    stageAvg (fun i => x i + y i) = stageAvg x + stageAvg y := by
  simp only [stageAvg, Finset.sum_add_distrib]
  ring

/--
Uniform generalization + approximate ERM imply population-risk transfer
against any fixed comparator.

If the infimum defining `L_r^*` is attained, choose that minimizer as
`thetaComp`. If not, use an arbitrary epsilon-optimal population comparator
and pass epsilon -> 0; the paper writes this step directly with `inf`.
-/
theorem erm_population_transfer_fixed_comparator
    (hk : 0 < k)
    {Theta : Type*}
    (L Lhat : Fin k → Theta → ℝ)
    (g : Fin k → ℝ)
    (thetaHat thetaComp : Theta)
    (epsOpt : ℝ)
    (hGen :
      ∀ i theta, |L i theta - Lhat i theta| ≤ g i)
    (hERM :
      stageAvg (fun i => Lhat i thetaHat) ≤
      stageAvg (fun i => Lhat i thetaComp) + epsOpt) :
    stageAvg (fun i => L i thetaHat) ≤
      stageAvg (fun i => L i thetaComp) +
      2 * stageAvg g + epsOpt := by
  have hHatPoint :
      ∀ i, L i thetaHat ≤ Lhat i thetaHat + g i := by
    intro i
    have h := (abs_le.mp (hGen i thetaHat)).2
    linarith
  have hCompPoint :
      ∀ i, Lhat i thetaComp ≤ L i thetaComp + g i := by
    intro i
    have h := (abs_le.mp (hGen i thetaComp)).1
    linarith
  have hHat :
      stageAvg (fun i => L i thetaHat) ≤
      stageAvg (fun i => Lhat i thetaHat) + stageAvg g := by
    calc
      stageAvg (fun i => L i thetaHat)
          ≤ stageAvg (fun i => Lhat i thetaHat + g i) :=
        stageAvg_mono hk hHatPoint
      _ = stageAvg (fun i => Lhat i thetaHat) + stageAvg g :=
        stageAvg_add _ _
  have hComp :
      stageAvg (fun i => Lhat i thetaComp) ≤
      stageAvg (fun i => L i thetaComp) + stageAvg g := by
    calc
      stageAvg (fun i => Lhat i thetaComp)
          ≤ stageAvg (fun i => L i thetaComp + g i) :=
        stageAvg_mono hk hCompPoint
      _ = stageAvg (fun i => L i thetaComp) + stageAvg g :=
        stageAvg_add _ _
  linarith

/--
Aggregate form of the stagewise candidate-miss transfer:
  eta_i ≤ L_i^h + cert_i + shift_i.
-/
theorem candidate_miss_aggregate
    (hk : 0 < k)
    (eta L cert shift : Fin k → ℝ)
    (hStage :
      ∀ i, eta i ≤ L i + cert i + shift i) :
    stageAvg eta ≤
      stageAvg L + stageAvg cert + stageAvg shift := by
  have h0 :
      stageAvg eta ≤
        stageAvg (fun i => (L i + cert i) + shift i) := by
    apply stageAvg_mono hk
    intro i
    simpa [add_assoc] using hStage i
  calc
    stageAvg eta
        ≤ stageAvg (fun i => (L i + cert i) + shift i) := h0
    _ = stageAvg (fun i => L i + cert i) + stageAvg shift :=
      stageAvg_add _ _
    _ = (stageAvg L + stageAvg cert) + stageAvg shift := by
      rw [stageAvg_add]
    _ = stageAvg L + stageAvg cert + stageAvg shift := by ring

/--
Lean version of the finite-history candidate-miss theorem, with the
population comparator made explicit.

`hComp` is the only extra formal side condition needed to avoid hiding
attainment of the `inf` in the paper notation.
-/
theorem finite_history_candidate_miss_bound
    (hk : 0 < k)
    {Theta : Type*}
    (L Lhat : Fin k → Theta → ℝ)
    (g cert shift eta : Fin k → ℝ)
    (thetaHat thetaComp : Theta)
    (epsOpt Lstar : ℝ)
    (hGen :
      ∀ i theta, |L i theta - Lhat i theta| ≤ g i)
    (hERM :
      stageAvg (fun i => Lhat i thetaHat) ≤
      stageAvg (fun i => Lhat i thetaComp) + epsOpt)
    (hComp :
      stageAvg (fun i => L i thetaComp) ≤ Lstar)
    (hStage :
      ∀ i,
        eta i ≤ L i thetaHat + cert i + shift i) :
    stageAvg eta ≤
      Lstar + 2 * stageAvg g + epsOpt +
      stageAvg cert + stageAvg shift := by
  have hPop :=
    erm_population_transfer_fixed_comparator
      (k := k) hk L Lhat g thetaHat thetaComp epsOpt hGen hERM
  have hAgg :=
    candidate_miss_aggregate
      (k := k) hk eta (fun i => L i thetaHat) cert shift hStage
  linarith

end FiniteHistory


/-! ## 6. Verification accuracy -/

section Verification

variable {α : Type u}

/--
Deterministic core of the verification lemma.

Uniform `xi`-accuracy of all fresh candidate empirical means plus empirical
maximization implies the chosen true value is within `2*xi` of the true
best candidate value.
-/
theorem verification_accuracy
    (C : Finset α)
    (v vhat : α → ℝ)
    (chosen star : α)
    (xi : ℝ)
    (hChosenC : chosen ∈ C)
    (hStarC : star ∈ C)
    (hChosenEmp :
      ∀ e ∈ C, vhat chosen ≥ vhat e)
    (hAcc :
      ∀ e ∈ C, |vhat e - v e| ≤ xi) :
    v chosen ≥ v star - 2 * xi := by
  have hc := abs_le.mp (hAcc chosen hChosenC)
  have hs := abs_le.mp (hAcc star hStarC)
  have hbest := hChosenEmp star hStarC
  linarith

/--
Same result written for marginal gains, where the common state value
`base = f(S)` cancels.
-/
theorem verification_marginal_accuracy
    (C : Finset α)
    (v vhat : α → ℝ)
    (base : ℝ)
    (chosen star : α)
    (xi : ℝ)
    (hChosenC : chosen ∈ C)
    (hStarC : star ∈ C)
    (hChosenEmp :
      ∀ e ∈ C, vhat chosen ≥ vhat e)
    (hAcc :
      ∀ e ∈ C, |vhat e - v e| ≤ xi) :
    v chosen - base ≥ (v star - base) - 2 * xi := by
  have h :=
    verification_accuracy
      C v vhat chosen star xi
      hChosenC hStarC hChosenEmp hAcc
  linarith

/--
Probability bookkeeping for the verification lemma.  `hHoeffdingUnion`
is precisely the Hoeffding + union-bound input from the paper.
-/
theorem verification_failure_probability
    (pFail b m xi delta : ℝ)
    (hHoeffdingUnion :
      pFail ≤ 2 * b * Real.exp (-2 * m * xi ^ 2))
    (hRadius :
      2 * b * Real.exp (-2 * m * xi ^ 2) ≤ delta) :
    pFail ≤ delta := by
  exact le_trans hHoeffdingUnion hRadius

end Verification


/-! ## 7. Greedy-recursion core -/

/--
The one-step recursion used in the main theorem.

`a` plays the role `1/k`, `failProb` is an upper bound on the union of
candidate-miss and verification-failure probabilities, and `err` is the
deterministic near-good/verification loss.

The assumption `Dprev ≤ 1` is important.  In the paper it follows from:
  f(S*) ≤ 1,
  f(S) ≥ 0,
hence `D = f(S*) - f(S) ≤ 1`.
-/
theorem greedy_step_from_failure_probability
    (a Dprev Dnext err failProb expectedGain : ℝ)
    (ha0 : 0 ≤ a)
    (hD1 : Dprev ≤ 1)
    (herr : 0 ≤ err)
    (hfail0 : 0 ≤ failProb)
    (hGain :
      expectedGain ≥
        (1 - failProb) * (a * Dprev - err))
    (hDnext :
      Dnext = Dprev - expectedGain) :
    Dnext ≤
      (1 - a) * Dprev + err + failProb * a := by
  have hqa0 : 0 ≤ failProb * a :=
    mul_nonneg hfail0 ha0
  have hqaD :
      (failProb * a) * Dprev ≤ failProb * a := by
    calc
      (failProb * a) * Dprev
          ≤ (failProb * a) * 1 :=
        mul_le_mul_of_nonneg_left hD1 hqa0
      _ = failProb * a := by ring
  have hscaledErr :
      (1 - failProb) * err ≤ err := by
    have hcoef : 1 - failProb ≤ 1 := by linarith
    calc
      (1 - failProb) * err
          ≤ 1 * err :=
        mul_le_mul_of_nonneg_right hcoef herr
      _ = err := by ring
  rw [hDnext]
  nlinarith [hGain, hqaD, hscaledErr]

/--
Unroll a contraction recursion while discarding geometric weights on the
nonnegative additive errors.  This is exactly the simplification used in
the paper before applying `(1 - 1/k)^k ≤ exp(-1)`.
-/
theorem recurrence_unroll_to
    (q : ℝ)
    (D err : ℕ → ℝ)
    (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) :
    ∀ K : ℕ,
      (∀ i < K, 0 ≤ err i) →
      (∀ i < K, D (i + 1) ≤ q * D i + err i) →
      D K ≤ q ^ K * D 0 + Finset.sum (Finset.range K) err := by
  intro K
  induction K with
  | zero =>
      intro _ _
      simp
  | succ K ih =>
      intro herr hrec
      have herrPrev : ∀ i < K, 0 ≤ err i := by
        intro i hi
        exact herr i (Nat.lt_trans hi (Nat.lt_succ_self K))
      have hrecPrev :
          ∀ i < K, D (i + 1) ≤ q * D i + err i := by
        intro i hi
        exact hrec i (Nat.lt_trans hi (Nat.lt_succ_self K))
      have hIH := ih herrPrev hrecPrev
      have hstep := hrec K (Nat.lt_succ_self K)
      have hmul :
          q * D K ≤
            q * (q ^ K * D 0 + Finset.sum (Finset.range K) err) :=
        mul_le_mul_of_nonneg_left hIH hq0
      have hsum0 :
          0 ≤ Finset.sum (Finset.range K) err := by
        exact Finset.sum_nonneg (by
          intro i hi
          exact herrPrev i (Finset.mem_range.mp hi))
      have hqsum :
          q * (Finset.sum (Finset.range K) err) ≤
            Finset.sum (Finset.range K) err := by
        have hprod :
            0 ≤ (1 - q) * (Finset.sum (Finset.range K) err) :=
          mul_nonneg (sub_nonneg.mpr hq1) hsum0
        nlinarith
      calc
        D (Nat.succ K)
            ≤ q * D K + err K := by
              simpa [Nat.succ_eq_add_one] using hstep
        _ ≤ q * (q ^ K * D 0 +
              Finset.sum (Finset.range K) err) + err K := by
              linarith
        _ ≤ q ^ (Nat.succ K) * D 0 +
              (Finset.sum (Finset.range K) err) + err K := by
              rw [pow_succ]
              nlinarith [hqsum]
        _ = q ^ (Nat.succ K) * D 0 +
              Finset.sum (Finset.range (Nat.succ K)) err := by
              rw [Finset.sum_range_succ]
              ring

/-- Greedy benchmark written as `1 - exp(-1)`, equal to `1 - 1/e`. -/
noncomputable def betaGreedy : ℝ := 1 - Real.exp (-1)

/--
Main near-greedy algebra.

The statistical analysis and stagewise greedy analysis need only establish
the recurrence and that the total additive error is at most `Gamma`.
Lean then proves the terminal `(1-1/e)` guarantee.
-/
theorem near_greedy_from_recursion
    (K : ℕ)
    (q opt final Gamma : ℝ)
    (D err : ℕ → ℝ)
    (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1)
    (hopt : 0 ≤ opt)
    (herr : ∀ i < K, 0 ≤ err i)
    (hrec : ∀ i < K, D (i + 1) ≤ q * D i + err i)
    (hD0 : D 0 = opt)
    (hFinal : final = opt - D K)
    (hGeom : q ^ K ≤ Real.exp (-1))
    (hErrSum :
      Finset.sum (Finset.range K) err ≤ Gamma) :
    final ≥ betaGreedy * opt - Gamma := by
  have hUnroll :=
    recurrence_unroll_to q D err hq0 hq1 K herr hrec
  rw [hD0] at hUnroll
  have hGeomMul :
      q ^ K * opt ≤ Real.exp (-1) * opt :=
    mul_le_mul_of_nonneg_right hGeom hopt
  have hDK :
      D K ≤ Real.exp (-1) * opt + Gamma := by
    linarith
  rw [hFinal]
  dsimp [betaGreedy]
  linarith

/--
The "in particular" approximation-ratio statement.
-/
theorem near_one_minus_e_from_terminal
    (opt final Gamma eps : ℝ)
    (hTerminal :
      final ≥ betaGreedy * opt - Gamma)
    (hGamma :
      Gamma ≤ eps * opt) :
    final ≥ (betaGreedy - eps) * opt := by
  dsimp [betaGreedy] at hTerminal ⊢
  nlinarith

/--
Regret bookkeeping after the terminal near-greedy bound.

`explorationGap` is the total expected beta-regret during verification.
`exploitGap` is the per-round expected beta-gap during exploitation.
-/
theorem regret_from_terminal_gap
    (T M explorationGap exploitGap Gamma regret : ℝ)
    (hRemaining : 0 ≤ T - M)
    (hExploration : explorationGap ≤ M)
    (hExploit : exploitGap ≤ Gamma)
    (hRegret :
      regret = explorationGap + (T - M) * exploitGap) :
    regret ≤ M + (T - M) * Gamma := by
  have hmul :
      (T - M) * exploitGap ≤ (T - M) * Gamma :=
    mul_le_mul_of_nonneg_left hExploit hRemaining
  rw [hRegret]
  linarith


/-! ## 8. Favorable-transfer candidate budget: exact exponential core -/

/--
If the candidate budget satisfies
  b * rho ≥ log(KT),
then the exponential candidate-miss bound is at most `1/(KT)`.

The paper's
  b = ceil(rho^{-1} log(KT))
ensures this in the non-capped case.  The capped case `b = N` is handled
separately by full inspection of all remaining arms.
-/
theorem exp_miss_from_log_budget
    (b rho KT : ℝ)
    (hKT : 0 < KT)
    (hBudget : Real.log KT ≤ b * rho) :
    Real.exp (-(b * rho)) ≤ 1 / KT := by
  calc
    Real.exp (-(b * rho))
        ≤ Real.exp (-Real.log KT) := by
          apply Real.exp_le_exp.mpr
          linarith
    _ = 1 / KT := by
      rw [Real.exp_neg, Real.exp_log hKT]
      simp [one_div]

/--
A compact exact certificate for the favorable-transfer rate calculation.
Instead of formalizing asymptotic `O~` syntax, provide explicit constants
`Cstage` and an explicit per-stage online cost bound; Lean verifies the
summation step.
-/
theorem favorable_transfer_sum
    {K : ℕ}
    (stageCost rhoTerm : Fin K → ℝ)
    (Cstage : ℝ)
    (hStage :
      ∀ i, stageCost i ≤ Cstage * rhoTerm i) :
    (∑ i, stageCost i) ≤
      Cstage * ∑ i, rhoTerm i := by
  calc
    (∑ i, stageCost i)
        ≤ ∑ i, Cstage * rhoTerm i := by
          exact Finset.sum_le_sum (fun i _ => hStage i)
    _ = Cstage * ∑ i, rhoTerm i := by
      rw [Finset.mul_sum]


end SHGLT
