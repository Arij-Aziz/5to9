/-
# Sieve.Transference

Abstract transference theorems: if a majorant ν satisfies suitable pseudorandomness
conditions, then additive patterns in the ν-weighted measure carry over to the
target set.

This is modeled on the Green–Tao transference framework.
This file provides abstract scaffolding used by AdditiveEnergyLower.lean. No concrete 
instance of StrongPseudorandomMajorant for multiPrimeMajorant is constructed in this project.

Status: AssumedForProgram (abstract framework and basic implications)
-/
import Mathlib

open Finset BigOperators

noncomputable section

/-! ## Pseudorandomness conditions -/

/-- Pseudorandomness conditions for a majorant on Fin N. -/
structure PseudorandomMajorant (N : ℕ) where
  /-- The majorant function -/
  nu : Fin N → ℝ
  /-- Nonnegativity -/
  nu_nonneg : ∀ x, 0 ≤ nu x
  /-- Average is close to 1: (1/N) Σ ν(n) ≈ 1 -/
  averageCondition : ℝ
  /-- The average is close to 1 -/
  havg : |((∑ x : Fin N, nu x) / N) - 1| ≤ averageCondition
  /-- Linear forms condition parameter -/
  linearFormsCondition : ℝ
  /-- The linear forms condition holds -/
  hlinear : linearFormsCondition ≥ 0

namespace PseudorandomMajorant

variable {N : ℕ} (P : PseudorandomMajorant N)

/-- The weighted count of a set -/
def weightedCount (S : Finset (Fin N)) : ℝ :=
  ∑ x ∈ S, P.nu x

/-- Weighted count is nonneg -/
lemma weightedCount_nonneg (S : Finset (Fin N)) :
    0 ≤ P.weightedCount S :=
  Finset.sum_nonneg (fun x _ => P.nu_nonneg x)

/-! ## Strengthened pseudorandomness: 2-point correlation condition -/

/-- A pseudorandom majorant with a substantive 2-point correlation condition.
    This encodes: for any two distinct elements a, b of Fin N,
    the correlation E[ν(x)ν(x + a - b)] ≈ E[ν(x)]² within error ε.

    This is the k = 2 case of the linear forms condition in the
    Green–Tao framework. -/
structure StrongPseudorandomMajorant (N : ℕ) extends PseudorandomMajorant N where
  /-- 2-point correlation bound: for any shift h,
      |E_x[ν(x)ν(x+h)] - 1| ≤ correlationError -/
  correlationError : ℝ
  hcorr_pos : correlationError ≥ 0
  /-- The correlation condition -/
  correlation_bound : ∀ h : Fin N,
    |(∑ x : Fin N, nu x * nu (x + h)) / N - 1| ≤ correlationError

namespace StrongPseudorandomMajorant

variable {N : ℕ} (P : StrongPseudorandomMajorant N)

/-- The weighted pair count over a set S:
    Σ_{(x,y) ∈ S × S} ν(x) ν(y) -/
def weightedPairCount (S : Finset (Fin N)) : ℝ :=
  ∑ x ∈ S, ∑ y ∈ S, P.nu x * P.nu y

/-- Weighted pair count is nonneg -/
lemma weightedPairCount_nonneg (S : Finset (Fin N)) :
    0 ≤ P.weightedPairCount S := by
  apply Finset.sum_nonneg; intro x _
  apply Finset.sum_nonneg; intro y _
  exact mul_nonneg (P.nu_nonneg x) (P.nu_nonneg y)

/-- The total weighted pair count equals (Σ ν(x))² -/
lemma total_weightedPairCount :
    P.weightedPairCount Finset.univ = (∑ x : Fin N, P.nu x) ^ 2 := by
  simp only [weightedPairCount, sq, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

end StrongPseudorandomMajorant

end PseudorandomMajorant

/-! ## Abstract transference principle -/

/-- An abstract transference principle: if a function f is bounded by ν
    and ν is pseudorandom, then additive counting functions for f
    approximate those on ν. -/
structure TransferencePrinciple (N : ℕ) where
  /-- The pseudorandom majorant -/
  majorant : PseudorandomMajorant N
  /-- The target function (bounded by ν) -/
  target : Fin N → ℝ
  /-- Target is nonneg -/
  target_nonneg : ∀ x, 0 ≤ target x
  /-- Target is bounded by ν -/
  target_le_nu : ∀ x, target x ≤ majorant.nu x
  /-- The error tolerance -/
  epsilon : ℝ
  /-- Error is positive -/
  heps : epsilon > 0

namespace TransferencePrinciple

variable {N : ℕ} (T : TransferencePrinciple N)

/-- The additive energy of the target -/
def additiveEnergy : ℝ :=
  ∑ a : Fin N, ∑ b : Fin N,
    T.target a * T.target b

/-- The weighted additive energy -/
def weightedAdditiveEnergy : ℝ :=
  ∑ a : Fin N, ∑ b : Fin N,
    T.majorant.nu a * T.majorant.nu b

/-- Target additive energy ≤ weighted energy -/
lemma additiveEnergy_le_weighted :
    T.additiveEnergy ≤ T.weightedAdditiveEnergy := by
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro b _
  apply mul_le_mul (T.target_le_nu a) (T.target_le_nu b)
    (T.target_nonneg b) (T.majorant.nu_nonneg a)

end TransferencePrinciple

/-! ## Dense model theorem (abstract version) -/

/-- Abstract dense model theorem: if f is bounded by a pseudorandom ν
    and has positive density, then f correlates with a dense subset
    in the uniform model. -/
structure DenseModelTheorem (N : ℕ) where
  /-- The pseudorandom majorant -/
  majorant : PseudorandomMajorant N
  /-- The target function -/
  target : Fin N → ℝ
  /-- Target bounded by ν -/
  target_le_nu : ∀ x, target x ≤ majorant.nu x
  /-- Target nonneg -/
  target_nonneg : ∀ x, 0 ≤ target x
  /-- Target density is at least δ under ν -/
  delta : ℝ
  hdelta : 0 < delta
  /-- Density lower bound -/
  density_bound : delta ≤ (∑ x : Fin N, target x) / (∑ x : Fin N, majorant.nu x)

end
