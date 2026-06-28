/-
# Sieve.MultiPrime.GeneralWeightConnection

General-weight versions of the Selberg upper bound and mass–energy results.

## Correction note

The quadratic form `multiPrimeQuadForm P λ = Σ_{d,e} λ_d λ_e / lcm(d,e)` does not
depend on the sieve density `g`; its minimum over `λ` with `λ₁ = 1` is the fixed
number `1 / V(1/·, P, D)` corresponding to the natural density `g(d) = 1/d`.
Accordingly the value of the optimal-weight majorant is `(P·m) / V(1/·, P, D)`,
**not** `(P·m) / V(g, P, D)` as previously stated. The statements below have been
corrected to use `V(1/·, P, D)`. The `SieveDensity g P D` bundle is retained for
interface compatibility (it is no longer load-bearing for these results).

Source: Iwaniec–Kowalski Theorem 6.4; Ford Theorem 4.1 p.44.
Status: Proved (modulo optimalWeight_quadForm_eq)
-/
import Mathlib
import RequestProject.Core.MultiPrime.OptimalWeights
import RequestProject.Core.MultiPrime.MoebiusWeights
import RequestProject.Core.MultiPrime.FourierRatio
import RequestProject.Core.MassEnergyTradeoff.SharpBounds
import RequestProject.Core.MultiPrime.RemainderBound
import RequestProject.Core.MultiPrime.SelbergUpperBound

open Finset BigOperators

noncomputable section

/-- Bundle of assumptions for a general multiplicative sieve density function g
    on squarefree divisors of P, with sieve level D. -/
structure SieveDensity (g : ℕ → ℝ) (P D : ℕ) : Prop where
  hP        : Squarefree P
  hP_pos    : 0 < P
  hD        : 1 ≤ D
  hg1       : g 1 = 1
  hh_nonneg : ∀ d ∈ sqfDivisors P, 0 ≤ hFunction g d
  hg_range  : ∀ p ∈ Nat.primeFactors P, 0 < g p ∧ g p < 1
  hg_mult   : ∀ d e : ℕ, Squarefree d → Squarefree e → Nat.Coprime d e →
                d ∣ P → e ∣ P → g (d * e) = g d * g e

/-
The double error sum at optimal weights is bounded by the selbergRemainderBound.
-/
lemma double_error_le_selbergRemainderBound
    (P D : ℕ) (g : ℕ → ℝ) (remainder : ℕ → ℝ) :
    ∑ d ∈ sqfDivisors P, ∑ e ∈ sqfDivisors P,
      selbergOptimalWeights g P D d *
      selbergOptimalWeights g P D e *
      remainder (Nat.lcm d e) ≤
    selbergRemainderBound P D g remainder := by
  refine' le_of_abs_le _;
  refine' le_trans ( Finset.abs_sum_le_sum_abs _ _ ) ( le_trans ( Finset.sum_le_sum fun i hi => Finset.abs_sum_le_sum_abs _ _ ) _ );
  rw [ ← Finset.sum_subset ( show ( sqfDivisors P ).filter ( · ≤ D ) ⊆ sqfDivisors P from Finset.filter_subset _ _ ) ];
  · refine' Finset.sum_le_sum fun x hx => _;
    rw [ ← Finset.sum_subset ( show ( sqfDivisors P ).filter ( · ≤ D ) ⊆ sqfDivisors P from Finset.filter_subset _ _ ) ];
    · norm_num [ abs_mul ];
    · intro e _ he; rw [ selbergOptimalWeights_zero g P D e he ]; simp;
  · intro d _ hd; simp [ selbergOptimalWeights_zero g P D d hd ]

/-
Mass of the multi-prime Selberg majorant at optimal weights equals
    (P*m) / V(1/·, P, D).
-/
theorem selberg_mass_eq_general
    (P m : ℕ) (hm : 0 < m)
    (g : ℕ → ℝ) (D : ℕ)
    (sd : SieveDensity g P D)
    (hlam_one : selbergOptimalWeights g P D 1 = 1) :
    (multiPrimeMajorant (P * m) P (selbergOptimalWeights g P D)
      (sd.hP_pos.ne') hlam_one).mass =
    (P * m : ℝ) / V_function (fun n => (1 : ℝ) / n) P D := by
  have h := multiPrime_mass_eq_quadForm P m sd.hP sd.hP_pos hm (selbergOptimalWeights g P D) hlam_one
  rw [h, optimalWeight_quadForm_eq P D g sd.hP sd.hP_pos sd.hD]; ring

/-
L² lower bound at optimal weights.
-/
theorem selberg_l2_lower_bound_general
    (P m : ℕ) (hm : 0 < m)
    (g : ℕ → ℝ) (D : ℕ)
    (sd : SieveDensity g P D)
    (hlam_one : selbergOptimalWeights g P D 1 = 1) :
    let M := multiPrimeMajorant (P * m) P (selbergOptimalWeights g P D)
               (sd.hP_pos.ne') hlam_one
    M.l2NormSq ≥ M.targetMass ^ 4 *
      V_function (fun n => (1 : ℝ) / n) P D ^ 2 / (P * m : ℝ) ^ 3 := by
  convert selberg_l2_lower_bound P m sd.hP sd.hP_pos hm ( selbergOptimalWeights g P D ) hlam_one _ using 1;
  · rw [ optimalWeight_quadForm_eq P D g sd.hP sd.hP_pos sd.hD, one_div_pow ];
    field_simp;
  · rw [ optimalWeight_quadForm_eq P D g sd.hP sd.hP_pos sd.hD ];
    exact one_div_pos.mpr ( V_inv_pos sd.hP_pos.ne' sd.hD )

/-
Selberg upper bound at optimal weights with remainder.
-/
theorem selberg_upper_bound_general
    (P m : ℕ) (hm : 0 < m)
    (g : ℕ → ℝ) (D : ℕ)
    (sd : SieveDensity g P D)
    (hlam_one : selbergOptimalWeights g P D 1 = 1)
    (remainder : ℕ → ℝ)
    (hr : ∀ d ∈ sqfDivisors P, ∀ e ∈ sqfDivisors P,
          (((Finset.range (P * m)).filter
            (fun a => Nat.lcm d e ∣ a)).card : ℝ) =
          (P * m : ℝ) / Nat.lcm d e + remainder (Nat.lcm d e)) :
    ((Finset.range (P * m)).filter (fun a => Nat.Coprime a P)).card ≤
      (P * m : ℝ) / V_function (fun n => (1 : ℝ) / n) P D +
      selbergRemainderBound P D g remainder := by
  refine le_trans ( siftedCount_le_quadraticMajorantSum P m sd.hP_pos ( selbergOptimalWeights g P D ) hlam_one ) ?_;
  rw [ quadraticMajorantSum_eq_mainTerm_plus_errorTerm P m sd.hP sd.hP_pos hm ( selbergOptimalWeights g P D ) remainder ];
  · rw [ optimalWeight_quadForm_eq P D g sd.hP sd.hP_pos sd.hD ];
    exact add_le_add ( by ring_nf; norm_num ) ( double_error_le_selbergRemainderBound P D g remainder );
  · exact fun d e hd he => hr d hd e he

/-- Unified connection: mass formula and L² lower bound at optimal weights. -/
theorem selberg_unified_connection_general
    (P m : ℕ) (hm : 0 < m)
    (g : ℕ → ℝ) (D : ℕ)
    (sd : SieveDensity g P D)
    (hlam_one : selbergOptimalWeights g P D 1 = 1) :
    let M := multiPrimeMajorant (P * m) P (selbergOptimalWeights g P D)
               (sd.hP_pos.ne') hlam_one
    M.mass = (P * m : ℝ) / V_function (fun n => (1 : ℝ) / n) P D
    ∧
    M.l2NormSq ≥ M.targetMass ^ 4 *
      V_function (fun n => (1 : ℝ) / n) P D ^ 2 / (P * m : ℝ) ^ 3 :=
  ⟨selberg_mass_eq_general P m hm g D sd hlam_one,
   selberg_l2_lower_bound_general P m hm g D sd hlam_one⟩

end
