import SHGLT.Core

open scoped BigOperators

namespace SHGLT.Paper

abbrev Arm (n : ℕ) := Fin n
abbrev State (n : ℕ) := Finset (Arm n)

def Feasible {n : ℕ} (k : ℕ) (S : State n) : Prop :=
  S.card ≤ k

structure RewardModel (n : ℕ) where
  f : State n → ℝ
  normalized : f ∅ = 0
  bounded : ∀ S, 0 ≤ f S ∧ f S ≤ 1
  monotone : ∀ {A B : State n}, A ⊆ B → f A ≤ f B
  submodular :
    ∀ {A B : State n} {e : Arm n},
      A ⊆ B → e ∉ B →
      f (insert e A) - f A ≥ f (insert e B) - f B

def marginal {n : ℕ}
    (M : RewardModel n) (S : State n) (e : Arm n) : ℝ :=
  M.f (insert e S) - M.f S

def optimalityGap {n : ℕ}
    (M : RewardModel n) (Sopt S : State n) : ℝ :=
  M.f Sopt - M.f S

theorem reward_gap_le_one {n : ℕ}
    (M : RewardModel n) (A B : State n) :
    M.f A - M.f B ≤ 1 := by
  have hA := (M.bounded A).2
  have hB := (M.bounded B).1
  linarith

theorem marginal_nonneg {n : ℕ}
    (M : RewardModel n) (S : State n) (e : Arm n) :
    0 ≤ marginal M S e := by
  dsimp [marginal]
  have hsub : S ⊆ insert e S := Finset.subset_insert e S
  exact sub_nonneg.mpr (M.monotone hsub)

noncomputable def beta : ℝ := 1 - Real.exp (-1)

end SHGLT.Paper
