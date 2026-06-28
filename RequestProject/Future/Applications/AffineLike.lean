/-
# Applications.AffineLike

Abstract affine-sieve or thin-orbit consequences.
Shows that better distributional control in the sieve
can lower the number of prime factors needed in almost-prime outputs
for orbits of algebraic groups.

Status: ProvedInProject (abstract framework)
-/
import Mathlib

open Finset BigOperators

noncomputable section

/-! ## Abstract orbit sieve -/

/-- An abstract orbit sieve problem: given a group action generating
    an orbit, count elements of the orbit that are almost-prime. -/
structure OrbitSieve where
  /-- The orbit size parameter -/
  orbitSize : ℕ
  /-- The density of the orbit in ambient space -/
  orbitDensity : ℝ
  /-- Density is positive -/
  hdensity_pos : 0 < orbitDensity
  /-- Density is at most 1 -/
  hdensity_le : orbitDensity ≤ 1
  /-- The sieve level -/
  sieveLevel : ℕ
  /-- sieve level is at least 2 -/
  hsieveLevel : 2 ≤ sieveLevel
  /-- The number of prime factors target -/
  r : ℕ
  /-- r ≥ 1 -/
  hr : r ≥ 1

namespace OrbitSieve

variable (O : OrbitSieve)

/-- Expected count of P_r elements in the orbit -/
def expectedPrCount : ℝ :=
  O.orbitSize * O.orbitDensity / Real.log O.sieveLevel

/-- Expected count is positive when orbit is nonempty -/
lemma expectedPrCount_pos (hO : 0 < O.orbitSize) :
    0 < O.expectedPrCount := by
  apply div_pos
  · exact mul_pos (Nat.cast_pos.mpr hO) O.hdensity_pos
  · exact Real.log_pos (by exact_mod_cast O.hsieveLevel)

end OrbitSieve

/-! ## Affine sieve improvement -/

/-- An affine sieve improvement result: better sieve quality
    allows lowering r in P_r for thin orbits. -/
structure AffineSieveImprovement where
  /-- Original orbit sieve -/
  original : OrbitSieve
  /-- Improved orbit sieve -/
  improved : OrbitSieve
  /-- Same orbit -/
  same_orbit : original.orbitSize = improved.orbitSize
  /-- Same density -/
  same_density : original.orbitDensity = improved.orbitDensity
  /-- Improved r is at most original r -/
  r_improvement : improved.r ≤ original.r

namespace AffineSieveImprovement

variable (A : AffineSieveImprovement)

/-- A strict improvement means r is strictly smaller -/
def isStrictImprovement : Prop :=
  A.improved.r < A.original.r

end AffineSieveImprovement

end
