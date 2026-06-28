/-
# MassEnergySandwich.lean
# Result 1: Sharp Mass–Energy Tradeoff for the Möbius-weight Selberg Majorant

## Mathematical Statement

For the Möbius-weight Selberg majorant:
- Mass is exactly N/V(P)
- L² energy is bounded below by |S|⁴ · V(P)² / N³

The lower bound `selberg_l2_sharp` is already proved; this file packages it
with the mass formula into a single sandwich theorem.

Does NOT use `optimalWeight_quadForm_eq` (the sorry).

Status: ProvedInProject
-/
import Mathlib
import RequestProject.Core.MultiPrime.MoebiusWeights
import RequestProject.Core.MassEnergyTradeoff.SharpBounds
import RequestProject.Core.MultiPrime.SelbergUpperBound

open Finset BigOperators

noncomputable section

/-
Mass formula for the Möbius-weight majorant.
    mass(ν) = (P*m) * Q(moebiusWeights P) = (P*m) / V(P).
    Source: multiPrime_mass_eq_quadForm + optimalWeight_quadForm_eq_moebius (proved).
-/
theorem selberg_mass_eq
    (P m : ℕ) (hP : Squarefree P) (hP_pos : 0 < P) (hm : 0 < m)
    (hlam_one : moebiusWeights P 1 = 1) :
    (multiPrimeMajorant (P * m) P (moebiusWeights P) (by omega) hlam_one).mass =
    (P * m : ℝ) / V_function (fun n => (1 : ℝ) / n) P P := by
  have := @optimalWeight_quadForm_eq_moebius P hP hP_pos;
  rw [ multiPrime_mass_eq_quadForm ] <;> aesop

/-- Sharp mass–energy lower bound for the Möbius-weight Selberg majorant.
    Packages selberg_l2_sharp (already proved) with the mass formula.
    Does NOT use optimalWeight_quadForm_eq (the sorry). -/
theorem selberg_mass_energy_sandwich
    (P m : ℕ) (hP : Squarefree P) (hP_pos : 0 < P) (hm : 0 < m)
    (hlam_one : moebiusWeights P 1 = 1) :
    let M := multiPrimeMajorant (P * m) P (moebiusWeights P) (by omega) hlam_one
    M.mass = (P * m : ℝ) / V_function (fun n => (1 : ℝ) / n) P P
    ∧
    M.l2NormSq ≥ M.targetMass ^ 4 *
      V_function (fun n => (1 : ℝ) / n) P P ^ 2 / (P * m : ℝ) ^ 3 := by
  exact ⟨selberg_mass_eq P m hP hP_pos hm hlam_one,
         selberg_l2_sharp P m hP hP_pos hm hlam_one⟩

end