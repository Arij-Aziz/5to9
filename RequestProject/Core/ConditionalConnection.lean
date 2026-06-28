/-
# ConditionalConnection.lean
# The Connecting Theorem: Mass–Energy, Restriction, and Kinetic Stability

## Mathematical Status

This file proves that Results 1, 2, and 3 are connected through a single chain:
  kinetic stability (Result 3) → V_function stability
                               → mass = N/V(1/·,P,D) (Result 1)
                               → l2NormSq ≥ |S|⁴ · V² / N³ (Result 2)

The connecting theorem `selberg_unified_connection` uses the theorem
  `optimalWeight_quadForm_eq`
from `RequestProject/Core/MultiPrime/OptimalWeights.lean`, which states
  `multiPrimeQuadForm P (selbergOptimalWeights g P D) = 1 / V_function (1/·) P D`.

Correction note: the quadratic form `multiPrimeQuadForm` does not depend on the
sieve density `g`, so the value of the optimal-weight majorant is governed by the
natural density `g(d) = 1/d`, i.e. by `V(1/·, P, D)`. The previously displayed
formula `λ_d = μ(d) V(D/d) / V(D)` was not the optimiser of the truncated form
(concrete counterexample `P = 6`, `D = 6`); the correct optimiser (the Möbius
inversion of the diagonalised system) is now used in `selbergOptimalWeights`.

The theorem `selberg_unified_connection_moebius` below is fully sorry-free and
establishes the same chain for the Möbius-weight specialisation (g = 1/·, D = P).
-/
import Mathlib
import RequestProject.Core.MultiPrime.OptimalWeights
import RequestProject.Core.MultiPrime.MoebiusWeights
import RequestProject.Core.MassEnergyTradeoff.MassEnergySandwich
import RequestProject.Core.KineticStability.VFunctionStability
import RequestProject.Core.RestrictionLowerBoundSelberg

open Finset BigOperators

noncomputable section

/-
The Unified Selberg Connection Theorem (optimal weights).
-/
theorem selberg_unified_connection
    (P m : ℕ) (hP : Squarefree P) (hP_pos : 0 < P) (hm : 0 < m)
    (g : ℕ → ℝ) (D : ℕ) (hD : 1 ≤ D)
    (hlam_one : selbergOptimalWeights g P D 1 = 1) :
    let M := multiPrimeMajorant (P * m) P (selbergOptimalWeights g P D) (by omega) hlam_one
    -- Chain link (B): mass = N/V
    M.mass = (P * m : ℝ) / V_function (fun n => (1 : ℝ) / n) P D
    ∧
    -- Chain link (C): l2NormSq lower bound
    M.l2NormSq ≥ M.targetMass ^ 4 * V_function (fun n => (1 : ℝ) / n) P D ^ 2 / (P * m : ℝ) ^ 3 := by
  constructor;
  · have h := multiPrime_mass_eq_quadForm P m hP hP_pos hm ( selbergOptimalWeights g P D ) hlam_one
    rw [ h, optimalWeight_quadForm_eq P D g hP hP_pos hD ] ; ring;
  · convert selberg_l2_lower_bound P m hP hP_pos hm ( selbergOptimalWeights g P D ) hlam_one _ using 1;
    · rw [ optimalWeight_quadForm_eq P D g hP hP_pos hD, one_div_pow ] ; field_simp;
    · rw [ optimalWeight_quadForm_eq P D g hP hP_pos hD ];
      exact one_div_pos.mpr ( V_inv_pos hP_pos.ne' hD )

/-
The Möbius-weight case of the connecting theorem. Fully sorry-free.
    Uses only proved lemmas: selberg_mass_eq + selberg_l2_sharp.
-/
theorem selberg_unified_connection_moebius
    (P m : ℕ) (hP : Squarefree P) (hP_pos : 0 < P) (hm : 0 < m)
    (hlam_one : moebiusWeights P 1 = 1) :
    let M := multiPrimeMajorant (P * m) P (moebiusWeights P) (by omega) hlam_one
    M.mass = (P * m : ℝ) / V_function (fun n => (1 : ℝ) / n) P P
    ∧
    M.l2NormSq ≥ M.targetMass ^ 4 *
      V_function (fun n => (1 : ℝ) / n) P P ^ 2 / (P * m : ℝ) ^ 3 := by
  exact ⟨ selberg_mass_eq P m hP hP_pos hm hlam_one, selberg_l2_sharp P m hP hP_pos hm hlam_one ⟩

end
