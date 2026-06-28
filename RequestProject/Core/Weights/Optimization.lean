/-
# Sieve.Weights.Optimization

Cauchy-Schwarz lower bound on the Selberg quadratic form:
  L(λ)² ≤ diagTerm(λ) · recipSum

And related optimization results.

Status: ProvedInProject
-/
import Mathlib
import RequestProject.Core.Weights.Definition

open Finset BigOperators

noncomputable section

namespace SelbergWeights

variable (W : SelbergWeights)

/-! ## The reciprocal sum V(D) -/

/-- The reciprocal sum V(D) = Σ_{d ≤ D, squarefree, d > 0} 1/f(d) -/
def recipSum : ℝ :=
  ∑ d ∈ Finset.range (W.D + 1), if Squarefree d ∧ 0 < d then 1 / W.f d else 0

/-- V(D) is positive (it contains at least the d=1 term) -/
lemma recipSum_pos (hD : 0 < W.D) : 0 < W.recipSum := by
  refine' lt_of_lt_of_le _ ( Finset.single_le_sum ( fun x hx ↦ _ ) ( by aesop : 1 ∈ Finset.range ( W.D + 1 ) ) ) <;> norm_num [ W.hf_one ]
  split_ifs <;> [ exact inv_nonneg.2 ( le_of_lt ( W.hf_pos x ( by linarith ) ( by tauto ) ) ) ; norm_num ]

/-! ## Cauchy-Schwarz bound: L² ≤ diagTerm · recipSum -/

/-
**Cauchy-Schwarz bound on the linear form**:
    L(λ)² ≤ diagTerm · V(D)

    This follows from Cauchy-Schwarz:
      (Σ_d λ_d / f(d))² = (Σ_d (λ_d / √f(d)) · (1/√f(d)))²
                         ≤ (Σ_d λ_d²/f(d)) · (Σ_d 1/f(d))
                         = diagTerm · V(D)
-/
theorem linForm_sq_le_diagTerm_mul_recipSum :
    W.linForm ^ 2 ≤ W.diagTerm * W.recipSum := by
  -- By Cauchy-Schwarz inequality, we know that for any vectors $v$ and $w$, we have $\left(\sum_{i=1}^n v_i w_i\right)^2 \leq \left(\sum_{i=1}^n v_i^2\right)\left(\sum_{i=1}^n w_i^2\right)$.
  have h_cauchy_schwarz : ∀ (u v : ℕ → ℝ), (∑ d ∈ Finset.range (W.D + 1), u d * v d)^2 ≤ (∑ d ∈ Finset.range (W.D + 1), u d^2) * (∑ d ∈ Finset.range (W.D + 1), v d^2) := by
    exact fun u v => sum_mul_sq_le_sq_mul_sq (range (W.D + 1)) u v;
  convert h_cauchy_schwarz ( fun d => if Squarefree d ∧ 0 < d then W.lambda d / Real.sqrt ( W.f d ) else 0 ) ( fun d => if Squarefree d ∧ 0 < d then 1 / Real.sqrt ( W.f d ) else 0 ) using 3 <;> norm_num;
  · refine' Finset.sum_congr rfl fun x hx => _;
    by_cases hx' : Squarefree x ∧ 0 < x <;> simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ];
    · exact Or.inl ( by rw [ ← mul_inv, Real.mul_self_sqrt ( le_of_lt ( W.hf_pos x hx'.2 hx'.1 ) ) ] );
    · by_cases hx'' : Squarefree x <;> simp_all +decide [ ne_of_gt ];
      exact Or.inl <| W.hlambda_sqfree x hx'';
  · refine' Finset.sum_congr rfl fun x hx => _ ; split_ifs <;> simp_all +decide [ div_pow, Real.sq_sqrt ( le_of_lt ( W.hf_pos _ _ _ ) ) ];
    exact Or.inl ( W.hlambda_sqfree x <| by aesop );
  · refine' Finset.sum_congr rfl fun x hx => _;
    by_cases h : Squarefree x ∧ 0 < x <;> simp +decide [ h, Real.sq_sqrt ( le_of_lt ( W.hf_pos x _ _ ) ) ]

/-! ## Diagonal term bounds -/

/-
The quadratic form dominates the diagonal when off-diagonal terms are nonneg.
    This holds e.g. when f is submultiplicative on lcm.
-/
theorem diagTerm_le_quadForm
    (h_offdiag : ∀ d ∈ Finset.range (W.D + 1), ∀ e ∈ Finset.range (W.D + 1),
      d ≠ e → 0 ≤ W.lambda d * W.lambda e / W.f (Nat.lcm d e)) :
    W.diagTerm ≤ W.quadForm := by
  rw [diagTerm, quadForm]
  apply Finset.sum_le_sum
  intro d hd
  rw [← Finset.add_sum_erase _ _ hd, Nat.lcm_self]
  rw [show W.lambda d * W.lambda d / W.f d = W.lambda d ^ 2 / W.f d from by ring]
  apply le_add_of_nonneg_right
  apply Finset.sum_nonneg
  intro e he
  exact h_offdiag d hd e (Finset.mem_of_mem_erase he) (Finset.ne_of_mem_erase he).symm

end SelbergWeights

end