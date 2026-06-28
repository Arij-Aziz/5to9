/-
# Sieve.Weights.QuadFormStability

Stability of the Selberg quadratic form under perturbation of the
multiplicative density function.

If two Selberg weight systems share the same weights λ but use different
density functions f, g whose values at squarefree d differ by at most
  ε · ω(d) · M^(ω(d)−1),
then the quadratic forms Q_f and Q_g are close, controlled by the
perturbation parameter ε.
-/
import Mathlib
import RequestProject.Core.Weights.Definition
import RequestProject.Core.KineticPropagation

open Finset BigOperators Nat

noncomputable section

/-! ## Step 1: Difference of reciprocals -/

/-- Algebraic bound: |1/a - 1/b| ≤ |a - b| / (a * b) for positive reals. -/
lemma inv_diff_bound (a b ε : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : |a - b| ≤ ε) :
    |1/a - 1/b| ≤ ε / (a * b) := by
  rw [div_sub_div _ _ (ne_of_gt ha) (ne_of_gt hb)]
  rw [abs_div, abs_of_pos (mul_pos ha hb)]
  gcongr
  simp only [one_mul, mul_one]
  linarith [abs_sub_comm a b]

/-! ## Step 2: LCM perturbation bound -/

/-
Bound on the perturbation of a single quadratic form term λ_d λ_e / f(lcm(d,e)).
-/
lemma quadForm_term_diff (f g : ℕ → ℝ) (lam : ℕ → ℝ) (d e : ℕ)
    (hf_pos : 0 < f (Nat.lcm d e)) (hg_pos : 0 < g (Nat.lcm d e))
    (K : ℝ) (hK : 0 ≤ K)
    (h_kinetic : |f (Nat.lcm d e) - g (Nat.lcm d e)| ≤ K) :
    |lam d * lam e / f (Nat.lcm d e) - lam d * lam e / g (Nat.lcm d e)|
      ≤ |lam d| * |lam e| * K / (f (Nat.lcm d e) * g (Nat.lcm d e)) := by
  have key := mul_le_mul_of_nonneg_left
    (inv_diff_bound (f (Nat.lcm d e)) (g (Nat.lcm d e)) K hf_pos hg_pos h_kinetic)
    (mul_nonneg (abs_nonneg (lam d)) (abs_nonneg (lam e)))
  calc |lam d * lam e / f (Nat.lcm d e) - lam d * lam e / g (Nat.lcm d e)|
      = |lam d| * |lam e| * |1 / f (Nat.lcm d e) - 1 / g (Nat.lcm d e)| := by
        rw [← abs_mul, ← abs_mul]; congr 1; ring
    _ ≤ |lam d| * |lam e| * (K / (f (Nat.lcm d e) * g (Nat.lcm d e))) := key
    _ = |lam d| * |lam e| * K / (f (Nat.lcm d e) * g (Nat.lcm d e)) := by ring

/-! ## Step 3: Per-term bound for the main theorem -/

/-- Squarefree lcm when both factors are squarefree. -/
lemma Nat.Squarefree.lcm {d e : ℕ} (hd : Squarefree d) (he : Squarefree e) :
    Squarefree (Nat.lcm d e) := by
  simp_all +decide [squarefree_iff_prime_squarefree]
  intro x hx; by_contra h; simp_all +decide [← sq, Nat.lcm_dvd_iff]
  rw [← Nat.factorization_le_iff_dvd] at h <;>
    simp_all +decide [← Nat.prime_iff, Nat.factorization_pow]
  · rw [Nat.factorization_lcm] at h <;> simp_all +decide [← Nat.prime_iff]
    · cases h <;>
        [exact hd x hx (Nat.dvd_trans (pow_dvd_pow _ ‹_›) (Nat.ordProj_dvd _ _));
         exact he x hx (Nat.dvd_trans (pow_dvd_pow _ ‹_›) (Nat.ordProj_dvd _ _))]
    · rintro rfl; simp_all +decide [Nat.factorization]
    · rintro rfl; simp_all +decide [Nat.factorization]
  · exact hx.ne_zero
  · constructor <;> rintro rfl <;> simp_all +decide [← Nat.prime_iff]

/-
Each term in the quadratic form difference is bounded.
-/
lemma quadForm_term_bound
    (W_f W_g : SelbergWeights)
    (hlambda : W_f.lambda = W_g.lambda)
    (ε : ℝ) (hε : 0 ≤ ε) (M : ℝ) (hM : 0 ≤ M)
    (hkin : ∀ d, Squarefree d →
        |W_f.f d - W_g.f d| ≤ ε * d.primeFactors.card * M ^ (d.primeFactors.card - 1))
    (d e : ℕ) (hd : d ∈ Finset.range (W_f.D + 1)) (he : e ∈ Finset.range (W_f.D + 1)) :
    |W_f.lambda d * W_f.lambda e / W_f.f (Nat.lcm d e) -
     W_f.lambda d * W_f.lambda e / W_g.f (Nat.lcm d e)| ≤
      ε * (|W_f.lambda d| * |W_f.lambda e| *
        (Nat.lcm d e).primeFactors.card * M ^ ((Nat.lcm d e).primeFactors.card - 1) /
        (W_f.f (Nat.lcm d e) * W_g.f (Nat.lcm d e))) := by
  by_cases hld : W_f.lambda d = 0
  · simp [hld]
  by_cases hle : W_f.lambda e = 0
  · simp [hle]
  have hdsq : Squarefree d := by by_contra h; exact hld (W_f.hlambda_sqfree d h)
  have hesq : Squarefree e := by by_contra h; exact hle (W_f.hlambda_sqfree e h)
  have hLsq : Squarefree (Nat.lcm d e) := Nat.Squarefree.lcm hdsq hesq
  have hLpos : 0 < Nat.lcm d e :=
    Nat.lcm_pos (Nat.pos_of_ne_zero hdsq.ne_zero) (Nat.pos_of_ne_zero hesq.ne_zero)
  have hf : 0 < W_f.f (Nat.lcm d e) := W_f.hf_pos _ hLpos hLsq
  have hg : 0 < W_g.f (Nat.lcm d e) := W_g.hf_pos _ hLpos hLsq
  refine (quadForm_term_diff W_f.f W_g.f W_f.lambda d e hf hg _ (by positivity)
    (hkin (Nat.lcm d e) hLsq)).trans_eq ?_
  ring

/-! ## Step 4: Main stability theorem -/

/-
The Selberg quadratic form is stable under perturbation of the density function.
    If two weight systems share the same weights λ and sieve level D, and the density
    functions f, g satisfy a kinetic propagation bound, then the quadratic forms are close.
-/
theorem quadForm_kinetic_stability
    (W_f W_g : SelbergWeights)
    (hD : W_f.D = W_g.D)
    (hlambda : W_f.lambda = W_g.lambda)
    (ε : ℝ) (hε : 0 ≤ ε) (M : ℝ) (hM : 0 ≤ M)
    (hkin : ∀ d, Squarefree d →
        |W_f.f d - W_g.f d| ≤ ε * d.primeFactors.card * M ^ (d.primeFactors.card - 1))
:
    |W_f.quadForm - W_g.quadForm| ≤
      ε * ∑ d ∈ Finset.range (W_f.D + 1), ∑ e ∈ Finset.range (W_f.D + 1),
        |W_f.lambda d| * |W_f.lambda e| *
        (Nat.lcm d e).primeFactors.card * M ^ ((Nat.lcm d e).primeFactors.card - 1) /
        (W_f.f (Nat.lcm d e) * W_g.f (Nat.lcm d e)) := by
  have hqf : W_f.quadForm
      = ∑ d ∈ Finset.range (W_f.D + 1), ∑ e ∈ Finset.range (W_f.D + 1),
          W_f.lambda d * W_f.lambda e / W_f.f (Nat.lcm d e) := rfl
  have hqg : W_g.quadForm
      = ∑ d ∈ Finset.range (W_f.D + 1), ∑ e ∈ Finset.range (W_f.D + 1),
          W_f.lambda d * W_f.lambda e / W_g.f (Nat.lcm d e) := by
    unfold SelbergWeights.quadForm; rw [hD, hlambda]
  rw [hqf, hqg, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun d hd => ?_))
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun e he => ?_))
  exact quadForm_term_bound W_f W_g hlambda ε hε M hM hkin d e hd he

end
