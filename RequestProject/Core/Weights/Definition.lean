/-
# Sieve.Weights.Definition

Algebraic Selberg-type weights and associated quadratic forms.

Status: ProvedInProject (definitions and basic algebraic properties)
-/
import Mathlib

open Finset BigOperators

noncomputable section

/-! ## Selberg weight system -/

/-- A Selberg weight system: weights indexed by squarefree natural numbers
    with a multiplicative density function. -/
structure SelbergWeights where
  /-- The sieve level (support cutoff) -/
  D : ℕ
  /-- The weights λ_d -/
  lambda : ℕ → ℝ
  /-- The multiplicative density function -/
  f : ℕ → ℝ
  /-- λ_1 = 1 -/
  hlambda_one : lambda 1 = 1
  /-- Weights vanish above D -/
  hlambda_support : ∀ d, D < d → lambda d = 0
  /-- Weights vanish on non-squarefree -/
  hlambda_sqfree : ∀ d, ¬Squarefree d → lambda d = 0
  /-- f(1) = 1 -/
  hf_one : f 1 = 1
  /-- f is positive on squarefree numbers > 0 -/
  hf_pos : ∀ d, 0 < d → Squarefree d → f d > 0

namespace SelbergWeights

variable (W : SelbergWeights)

/-- The support of the weight system -/
def support : Finset ℕ :=
  (Finset.range (W.D + 1)).filter (fun d => W.lambda d ≠ 0)

/-- The quadratic form Q(λ) = Σ_{d,e ≤ D} λ_d λ_e / f(lcm(d,e)) -/
def quadForm : ℝ :=
  ∑ d ∈ Finset.range (W.D + 1), ∑ e ∈ Finset.range (W.D + 1),
    W.lambda d * W.lambda e / W.f (Nat.lcm d e)

/-- The linear form L(λ) = Σ_d λ_d / f(d) -/
def linForm : ℝ :=
  ∑ d ∈ Finset.range (W.D + 1), W.lambda d / W.f d

/-- The diagonal contribution -/
def diagTerm : ℝ :=
  ∑ d ∈ Finset.range (W.D + 1), W.lambda d ^ 2 / W.f d

/-- Diagonal term is nonneg when f is positive -/
lemma diagTerm_nonneg : 0 ≤ W.diagTerm := by
  apply Finset.sum_nonneg
  intro d _
  by_cases hd : W.lambda d = 0
  · simp [hd]
  · by_cases hsq : Squarefree d
    · by_cases hd0 : d = 0
      · subst hd0; simp at hsq
      · exact div_nonneg (sq_nonneg _) (le_of_lt (W.hf_pos d (Nat.pos_of_ne_zero hd0) hsq))
    · simp [W.hlambda_sqfree d hsq]

end SelbergWeights

end
