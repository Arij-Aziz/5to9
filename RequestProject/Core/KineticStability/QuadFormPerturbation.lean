/-
# Sieve.KineticStability.QuadFormPerturbation

Stability of the multi-prime quadratic form Q(λ) under weight perturbation.

## Main results

* `multiPrimeQuadForm_perturbation` — |Q(λ) - Q(μ)| ≤ 2C · Σ_{d,e} δ_d / lcm(d,e)
    when |λ_d|, |μ_d| ≤ C and |λ_d - μ_d| ≤ δ_d for all squarefree d | P.

This connects the kinetic propagation machinery (Phase 2: `prod_perturb`)
to the multi-prime quadratic form. The algebraic engine is the identity
  |λ_d λ_e - μ_d μ_e| ≤ C · |λ_d - μ_d| + C · |λ_e - μ_e|
which is exactly `prod_perturb` from KineticPropagation.lean.

Status: ProvedInProject
-/
import Mathlib
import RequestProject.Core.KineticPropagation
import RequestProject.Core.MultiPrime.L2Identity

open Finset BigOperators

noncomputable section

/-
If λ and μ differ by at most δ_d at each squarefree d | P,
    and both are bounded by C on sqfDivisors P, then their quadratic forms
    differ by a controlled amount.

    The bound uses `prod_perturb`: |λ_d λ_e - μ_d μ_e| ≤ C(δ_d + δ_e).
-/
theorem multiPrimeQuadForm_perturbation
    (P : ℕ) (hP : Squarefree P)
    (lambda mu : ℕ → ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (delta : ℕ → ℝ) (_hdelta : ∀ d, 0 ≤ delta d)
    (hlam_bound : ∀ d ∈ sqfDivisors P, |lambda d| ≤ C)
    (hmu_bound  : ∀ d ∈ sqfDivisors P, |mu d| ≤ C)
    (hpert      : ∀ d ∈ sqfDivisors P, |lambda d - mu d| ≤ delta d) :
    |multiPrimeQuadForm P lambda - multiPrimeQuadForm P mu| ≤
      2 * C * ∑ d ∈ sqfDivisors P, ∑ e ∈ sqfDivisors P,
          delta d / (Nat.lcm d e : ℝ) := by
  -- Apply the triangle inequality to the double sum.
  have h_triangle : |multiPrimeQuadForm P lambda - multiPrimeQuadForm P mu| ≤ ∑ d ∈ sqfDivisors P, ∑ e ∈ sqfDivisors P, |lambda d * lambda e - mu d * mu e| / (Nat.lcm d e : ℝ) := by
    -- By definition of multiPrimeQuadForm, we can write the difference as a double sum.
    have h_diff : multiPrimeQuadForm P lambda - multiPrimeQuadForm P mu = ∑ d ∈ sqfDivisors P, ∑ e ∈ sqfDivisors P, (lambda d * lambda e - mu d * mu e) / (Nat.lcm d e : ℝ) := by
      unfold multiPrimeQuadForm; simp +decide [ sub_div ] ;
    exact h_diff.symm ▸ le_trans ( Finset.abs_sum_le_sum_abs _ _ ) ( Finset.sum_le_sum fun i hi => Finset.abs_sum_le_sum_abs _ _ |> le_trans <| Finset.sum_le_sum fun j hj => by rw [ abs_div, abs_of_nonneg ( by positivity : ( 0 : ℝ ) ≤ Nat.lcm i j ) ] );
  -- Apply the perturbation bound to each term in the double sum.
  have h_perturbation : ∀ d e : ℕ, d ∈ sqfDivisors P → e ∈ sqfDivisors P → |lambda d * lambda e - mu d * mu e| ≤ C * (delta d + delta e) := by
    intros d e hd he;
    exact abs_le.mpr ⟨ by nlinarith only [ abs_le.mp ( hlam_bound d hd ), abs_le.mp ( hmu_bound d hd ), abs_le.mp ( hlam_bound e he ), abs_le.mp ( hmu_bound e he ), abs_le.mp ( hpert d hd ), abs_le.mp ( hpert e he ) ], by nlinarith only [ abs_le.mp ( hlam_bound d hd ), abs_le.mp ( hmu_bound d hd ), abs_le.mp ( hlam_bound e he ), abs_le.mp ( hmu_bound e he ), abs_le.mp ( hpert d hd ), abs_le.mp ( hpert e he ) ] ⟩;
  -- Split the sum into two parts: one with delta_d and one with delta_e.
  have h_split_sum : ∑ d ∈ sqfDivisors P, ∑ e ∈ sqfDivisors P, C * (delta d + delta e) / (Nat.lcm d e : ℝ) = 2 * C * ∑ d ∈ sqfDivisors P, ∑ e ∈ sqfDivisors P, delta d / (Nat.lcm d e : ℝ) := by
    simp +decide [ Finset.mul_sum _ _ _, Finset.sum_add_distrib, mul_add, add_div, mul_div_assoc, two_mul ];
    simp +decide only [add_mul, mul_div_assoc, sum_add_distrib];
    exact congrArg₂ ( · + · ) rfl ( Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [ Nat.lcm_comm ] ) );
  exact h_triangle.trans ( h_split_sum ▸ Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => by gcongr ; exact h_perturbation i j hi hj )

end