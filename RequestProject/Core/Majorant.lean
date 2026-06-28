/-
# Sieve.Majorant

Abstract majorant interface: domination, normalization, and basic properties.

A majorant is a nonneg function that dominates the indicator of the sifted set
and satisfies useful analytic properties (bounded mass, Fourier decay, etc).

Status: ProvedInProject (definitions and basic lemmas)
-/
import Mathlib

open Finset BigOperators

noncomputable section

/-! ## Abstract majorant -/

/-- An abstract majorant for a target indicator function on a finite set. -/
structure Majorant (N : ℕ) where
  /-- The majorant function ν : {0,...,N-1} → ℝ -/
  nu : Fin N → ℝ
  /-- The target indicator function -/
  target : Fin N → ℝ
  /-- Nonnegativity of the majorant -/
  nu_nonneg : ∀ x, 0 ≤ nu x
  /-- Nonnegativity of the target -/
  target_nonneg : ∀ x, 0 ≤ target x
  /-- Target is an indicator (values in {0, 1}) -/
  target_indicator : ∀ x, target x = 0 ∨ target x = 1
  /-- Domination: ν ≥ target pointwise -/
  domination : ∀ x, target x ≤ nu x

namespace Majorant

variable {N : ℕ} (M : Majorant N)

/-- The mass (L¹ norm) of the majorant -/
def mass : ℝ := ∑ x : Fin N, M.nu x

/-- The mass of the target -/
def targetMass : ℝ := ∑ x : Fin N, M.target x

/-- Mass is nonneg -/
lemma mass_nonneg : 0 ≤ M.mass :=
  Finset.sum_nonneg (fun x _ => M.nu_nonneg x)

/-- Target mass is nonneg -/
lemma targetMass_nonneg : 0 ≤ M.targetMass :=
  Finset.sum_nonneg (fun x _ => M.target_nonneg x)

/-- Domination implies mass domination -/
lemma mass_ge_targetMass : M.targetMass ≤ M.mass := by
  apply Finset.sum_le_sum
  intro x _
  exact M.domination x

/-- The L² norm squared of the majorant -/
def l2NormSq : ℝ := ∑ x : Fin N, M.nu x ^ 2

/-- L² norm squared is nonneg -/
lemma l2NormSq_nonneg : 0 ≤ M.l2NormSq :=
  Finset.sum_nonneg (fun x _ => sq_nonneg _)

/-- The normalized mass ratio: mass / N -/
def normalizedMass : ℝ := M.mass / N

/-- The density of the target -/
def targetDensity : ℝ := M.targetMass / N

/-- Normalized mass ≥ target density -/
lemma normalizedMass_ge_targetDensity (hN : (0 : ℝ) < N) :
    M.targetDensity ≤ M.normalizedMass := by
  unfold normalizedMass targetDensity
  exact div_le_div_of_nonneg_right M.mass_ge_targetMass (le_of_lt hN)

end Majorant

/-! ## Benchmark interface -/

/-- A benchmark comparison between two majorants for the same target. -/
structure MajorantComparison (N : ℕ) where
  /-- The reference (classical) majorant -/
  classical : Majorant N
  /-- The new (improved) majorant -/
  improved : Majorant N
  /-- Same target -/
  same_target : classical.target = improved.target

namespace MajorantComparison

variable {N : ℕ} (C : MajorantComparison N)

/-- Mass improvement: the improved majorant has smaller mass -/
def massImprovement : Prop := C.improved.mass < C.classical.mass

/-- L² improvement -/
def l2Improvement : Prop := C.improved.l2NormSq < C.classical.l2NormSq

end MajorantComparison

end
