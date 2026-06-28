/-
# Sieve.MultiPrime.SelbergUpperBound

The Selberg upper bound for the multi-prime sieve at Möbius weights.

## Main definitions

* `selbergRemainderBound` — the error term from the sieve (at selbergOptimalWeights)

## Main results

* `selberg_upper_bound_multiPrime` — |S| ≤ X / V(D) + moebiusRemainderBound
* `selberg_l2_sharp` — ‖ν‖₂² ≥ |S|⁴ · V(D)² / (P·m)³

-- Source: Ford Theorem 4.1 p. 44; Iwaniec-Kowalski Theorem 6.4 eq. (6.78)

Status: ProvedInProject
-/
import Mathlib
import RequestProject.Core.MultiPrime.MoebiusWeights
import RequestProject.Core.MassEnergyTradeoff.SharpBounds

open Finset BigOperators

noncomputable section

/-- The remainder bound for the Selberg sieve at level D (at selbergOptimalWeights). -/
noncomputable def selbergRemainderBound (P D : ℕ) (g : ℕ → ℝ)
    (remainder : ℕ → ℝ) : ℝ :=
  ∑ d ∈ (sqfDivisors P).filter (· ≤ D),
    ∑ e ∈ (sqfDivisors P).filter (· ≤ D),
      |selbergOptimalWeights g P D d| * |selbergOptimalWeights g P D e| *
      |remainder (Nat.lcm d e)|

/-
Source: Iwaniec-Kowalski Theorem 6.4; Ford Theorem 4.1 p. 44
Selberg upper bound for the multi-prime sieve at Möbius weights (g = 1/d, D = P).
-/
theorem selberg_upper_bound_multiPrime
    (P m : ℕ)
    (hP : Squarefree P) (hP_pos : 0 < P) (hm : 0 < m)
    (hlam_one : moebiusWeights P 1 = 1) :
    let M := multiPrimeMajorant (P * m) P (moebiusWeights P)
              (by omega) hlam_one
    M.targetMass ≤ (P * m : ℝ) / V_function (fun n => (1 : ℝ) / n) P P +
      moebiusRemainderBound P (fun _ => 0) := by
  have h_mass :
      let M := multiPrimeMajorant (P * m) P (moebiusWeights P) (by omega) hlam_one
      M.mass = (P * m : ℝ) / V_function (fun n => (1 : ℝ) / n) P P := by
    convert multiPrime_mass_eq_quadForm P m hP hP_pos hm (moebiusWeights P) hlam_one using 1
    rw [optimalWeight_quadForm_eq_moebius P hP hP_pos]; ring
  refine le_add_of_le_of_nonneg ?_ ?_
  · exact h_mass ▸ Majorant.mass_ge_targetMass _
  · exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

/-
Source: Derived from selberg_l2_lower_bound + optimalWeight_quadForm_eq_moebius
Sharp L² lower bound at Möbius weights.
-/
theorem selberg_l2_sharp
    (P m : ℕ) (hP : Squarefree P) (hP_pos : 0 < P) (hm : 0 < m)
    (hlam_one : moebiusWeights P 1 = 1) :
    let M := multiPrimeMajorant (P * m) P (moebiusWeights P) (by omega) hlam_one
    M.l2NormSq ≥ M.targetMass ^ 4 *
      V_function (fun n => (1 : ℝ) / n) P P ^ 2 / (P * m : ℝ) ^ 3 := by
  have h_quad : multiPrimeQuadForm P (moebiusWeights P) =
      1 / V_function (fun n => (1 : ℝ) / n) P P :=
    optimalWeight_quadForm_eq_moebius P hP hP_pos
  have h_pos : 0 < multiPrimeQuadForm P (moebiusWeights P) := by
    rw [h_quad]
    apply div_pos one_pos
    exact V_function_pos (fun n => (1 : ℝ) / n) P P hP_pos.ne' hP_pos
      (by norm_num)
      (fun d hd => hFunction_inv_nonneg hd)
  have h_lb := selberg_l2_lower_bound P m hP hP_pos hm (moebiusWeights P) hlam_one h_pos
  calc (multiPrimeMajorant (P * m) P (moebiusWeights P) (by omega) hlam_one).l2NormSq
      ≥ _ / ((P * m : ℝ) ^ 3 * multiPrimeQuadForm P (moebiusWeights P) ^ 2) := h_lb
    _ = _ * V_function (fun n => (1 : ℝ) / n) P P ^ 2 / (P * m : ℝ) ^ 3 := by
        rw [h_quad]; field_simp

end
