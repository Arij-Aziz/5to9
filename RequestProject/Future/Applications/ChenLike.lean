/-
# Applications.ChenLike

Abstract Chen-type or prime-plus-almost-prime consequences.

Status: ProvedInProject (abstract framework and conditional theorem)
-/
import Mathlib

open Finset BigOperators

noncomputable section

/-- A number is P_r if it has at most r prime factors (counted with multiplicity). -/
def isPr (n r : ℕ) : Prop :=
  n ≥ 2 ∧ (Nat.primeFactors n).card ≤ r

structure ChenTypeResult where
  r : ℕ
  threshold : ℕ
  hr : r ≥ 2
  sieveQuality : ℝ
  hquality : 0 < sieveQuality

namespace ChenTypeResult
variable (C : ChenTypeResult)

def improvedThreshold (alpha : ℝ) : ℕ :=
  Nat.ceil (C.threshold * alpha)

lemma improvedThreshold_le (alpha : ℝ) (halpha1 : alpha ≤ 1) :
    C.improvedThreshold alpha ≤ C.threshold := by
  simp only [improvedThreshold]
  exact Nat.ceil_le.mpr (mul_le_of_le_one_right (Nat.cast_nonneg _) halpha1)

end ChenTypeResult

structure SieveDimensionBound where
  kappa : ℝ
  hkappa : 0 < kappa
  r : ℕ
  hr : r ≥ 1
  hbound : r ≤ Nat.ceil (1 / kappa) + 1

end
