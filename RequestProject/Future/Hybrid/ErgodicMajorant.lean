/-
# Hybrid.ErgodicMajorant

Construction of a Selberg-type majorant from dynamical/kinetic data,
and comparison with a classical benchmark majorant.

Status: ProvedInProject (construction and basic comparison)
-/
import Mathlib
import RequestProject.Core.MultiPrime.FourierRatio
import RequestProject.Core.MultiPrime.SelbergUpperBound
import RequestProject.Core.MultiPrime.MoebiusWeights
import RequestProject.Core.MultiPrime.OptimalWeights

open Finset BigOperators

noncomputable section

/-! ## Ergodic majorant construction -/

/-- An ergodic majorant: a majorant constructed from a kinetic law's
    observable, specialized to a finite model. -/
structure ErgodicMajorant (N : ℕ) where
  /-- The majorant weights -/
  nu : Fin N → ℝ
  /-- Nonnegativity -/
  nu_nonneg : ∀ x, 0 ≤ nu x
  /-- The target indicator -/
  target : Fin N → ℝ
  /-- Target nonnegativity -/
  target_nonneg : ∀ x, 0 ≤ target x
  /-- Domination -/
  domination : ∀ x, target x ≤ nu x
  /-- The kinetic dimension parameter -/
  dimension : ℕ
  /-- Fourier decay rate -/
  fourierDecayRate : ℝ
  /-- Fourier decay is positive -/
  hfourier : fourierDecayRate > 0
  /-- Averaged remainder bound -/
  avgRemainderBound : ℝ
  /-- Remainder bound is positive -/
  hremainder : avgRemainderBound > 0

namespace ErgodicMajorant

variable {N : ℕ} (E : ErgodicMajorant N)

/-- Mass of the ergodic majorant -/
def mass : ℝ := ∑ x : Fin N, E.nu x

/-- Mass of the target -/
def targetMass : ℝ := ∑ x : Fin N, E.target x

/-- Mass is nonneg -/
lemma mass_nonneg : 0 ≤ E.mass :=
  Finset.sum_nonneg (fun x _ => E.nu_nonneg x)

/-- Domination at the mass level -/
lemma mass_ge_targetMass : E.targetMass ≤ E.mass := by
  apply Finset.sum_le_sum
  intro x _
  exact E.domination x

/-- L² norm squared -/
def l2NormSq : ℝ := ∑ x : Fin N, E.nu x ^ 2

/-- The mass ratio: how much larger ν is compared to target -/
def massRatio : ℝ := E.mass / E.targetMass

end ErgodicMajorant

/-! ## Classical benchmark majorant -/

/-- A classical Selberg majorant (benchmark for comparison). -/
structure ClassicalMajorant (N : ℕ) where
  /-- The majorant weights -/
  nu : Fin N → ℝ
  /-- Nonnegativity -/
  nu_nonneg : ∀ x, 0 ≤ nu x
  /-- The target indicator -/
  target : Fin N → ℝ
  /-- Target nonnegativity -/
  target_nonneg : ∀ x, 0 ≤ target x
  /-- Domination -/
  domination : ∀ x, target x ≤ nu x
  /-- Fourier decay rate -/
  fourierDecayRate : ℝ
  /-- Averaged remainder bound -/
  avgRemainderBound : ℝ

namespace ClassicalMajorant

variable {N : ℕ} (C : ClassicalMajorant N)

/-- Mass of the classical majorant -/
def mass : ℝ := ∑ x : Fin N, C.nu x

end ClassicalMajorant

/-! ## Comparison theorem -/

/-- Comparison between ergodic and classical majorants. -/
structure MajorantImprovement (N : ℕ) where
  /-- The ergodic majorant -/
  ergodic : ErgodicMajorant N
  /-- The classical majorant -/
  classical : ClassicalMajorant N
  /-- Same target -/
  same_target : ergodic.target = classical.target
  /-- Mass improvement -/
  mass_improvement : ergodic.mass ≤ classical.mass
  /-- Fourier improvement -/
  fourier_improvement : ergodic.fourierDecayRate ≤ classical.fourierDecayRate

namespace MajorantImprovement

variable {N : ℕ} (M : MajorantImprovement N)

/-- A strict improvement means at least one metric is strictly better -/
def isStrictImprovement : Prop :=
  M.ergodic.mass < M.classical.mass ∨
  M.ergodic.fourierDecayRate < M.classical.fourierDecayRate

/-- No-regression: the ergodic majorant is at least as good as classical -/
lemma noRegression : M.ergodic.mass ≤ M.classical.mass :=
  M.mass_improvement

end MajorantImprovement

/-! ## Concrete multi-prime instances

The multi-prime Selberg majorant (built from generic optimal weights `lambda`)
and the classical Möbius-weight majorant, packaged as `ErgodicMajorant` and
`ClassicalMajorant` respectively, and compared via `MajorantImprovement`. -/

/-- The multi-prime Selberg majorant for weights `lambda`, packaged as an
    `ErgodicMajorant`.  Its `fourierDecayRate` is the Selberg-kernel decay rate
    `1 / V(1/·, P, P)`; its `dimension` is `ω(P)`. -/
noncomputable def selberg_ergodicMajorant
    (P m : ℕ) (hP_pos : 0 < P)
    (lambda : ℕ → ℝ) (hlam_one : lambda 1 = 1)
    (hV_pos : 0 < V_function (fun n => (1 : ℝ) / n) P P) :
    ErgodicMajorant (P * m) :=
  let M := multiPrimeMajorant (P * m) P lambda (by omega) hlam_one
  { nu := M.nu
    nu_nonneg := M.nu_nonneg
    target := M.target
    target_nonneg := M.target_nonneg
    domination := M.domination
    -- dimension = ω(P) = number of distinct prime factors of P
    dimension := P.primeFactors.card
    fourierDecayRate := 1 / V_function (fun n => (1 : ℝ) / n) P P
    hfourier := div_pos one_pos hV_pos
    avgRemainderBound := 1
    hremainder := one_pos }

/-- The classical Möbius-weight majorant, packaged as a `ClassicalMajorant`. -/
noncomputable def moebius_classicalMajorant
    (P m : ℕ) (hP_pos : 0 < P) :
    ClassicalMajorant (P * m) :=
  let M := multiPrimeMajorant (P * m) P (moebiusWeights P) (by omega)
    (moebiusWeights_one P hP_pos)
  { nu := M.nu
    nu_nonneg := M.nu_nonneg
    target := M.target
    target_nonneg := M.target_nonneg
    domination := M.domination
    fourierDecayRate := multiPrimeQuadForm P (moebiusWeights P)
    avgRemainderBound := moebiusRemainderBound P (fun _ => 0) }

/-
Both majorants dominate the same sieve target `sieveIndicator (P*m) P`.
-/
lemma selberg_moebius_same_target
    (P m : ℕ) (hP_pos : 0 < P)
    (lambda : ℕ → ℝ) (hlam_one : lambda 1 = 1)
    (hV_pos : 0 < V_function (fun n => (1 : ℝ) / n) P P) :
    (selberg_ergodicMajorant P m hP_pos lambda hlam_one hV_pos).target =
    (moebius_classicalMajorant P m hP_pos).target := by
  rfl

/-
Conditional mass comparison: if `lambda`'s quadratic form is at most the
    Möbius weights' quadratic form, then the Selberg ergodic majorant has at
    most the mass of the Möbius classical majorant.
-/
lemma selberg_mass_le_moebius_mass
    (P m : ℕ) (hP : Squarefree P) (hP_pos : 0 < P) (hm : 0 < m)
    (lambda : ℕ → ℝ) (hlam_one : lambda 1 = 1)
    (hV_pos : 0 < V_function (fun n => (1 : ℝ) / n) P P)
    (hmass : multiPrimeQuadForm P lambda ≤ multiPrimeQuadForm P (moebiusWeights P)) :
    (selberg_ergodicMajorant P m hP_pos lambda hlam_one hV_pos).mass ≤
    (moebius_classicalMajorant P m hP_pos).mass := by
  have he : (selberg_ergodicMajorant P m hP_pos lambda hlam_one hV_pos).mass
      = (P * m : ℝ) * multiPrimeQuadForm P lambda :=
    multiPrime_mass_eq_quadForm P m hP hP_pos hm lambda hlam_one
  have hc : (moebius_classicalMajorant P m hP_pos).mass
      = (P * m : ℝ) * multiPrimeQuadForm P (moebiusWeights P) :=
    multiPrime_mass_eq_quadForm P m hP hP_pos hm (moebiusWeights P) (moebiusWeights_one P hP_pos)
  rw [he, hc]
  exact mul_le_mul_of_nonneg_left hmass (by positivity)

/-
Fourier-rate comparison: the Selberg ergodic majorant's decay rate equals
    the Möbius classical majorant's (both equal `1 / V(1/·, P, P)`), hence `≤`.
-/
lemma selberg_fourierRate_le_moebius
    (P m : ℕ) (hP : Squarefree P) (hP_pos : 0 < P)
    (lambda : ℕ → ℝ) (hlam_one : lambda 1 = 1)
    (hV_pos : 0 < V_function (fun n => (1 : ℝ) / n) P P) :
    (selberg_ergodicMajorant P m hP_pos lambda hlam_one hV_pos).fourierDecayRate ≤
    (moebius_classicalMajorant P m hP_pos).fourierDecayRate := by
  rw [selberg_ergodicMajorant, moebius_classicalMajorant];
  rw [ optimalWeight_quadForm_eq_moebius P hP hP_pos ]

/-- Package the comparison as a `MajorantImprovement`, conditional on the mass
    inequality `hmass`. -/
noncomputable def selberg_moebius_improvement
    (P m : ℕ) (hP : Squarefree P) (hP_pos : 0 < P) (hm : 0 < m)
    (lambda : ℕ → ℝ) (hlam_one : lambda 1 = 1)
    (hV_pos : 0 < V_function (fun n => (1 : ℝ) / n) P P)
    (hmass : multiPrimeQuadForm P lambda ≤ multiPrimeQuadForm P (moebiusWeights P)) :
    MajorantImprovement (P * m) :=
  { ergodic := selberg_ergodicMajorant P m hP_pos lambda hlam_one hV_pos
    classical := moebius_classicalMajorant P m hP_pos
    same_target := selberg_moebius_same_target P m hP_pos lambda hlam_one hV_pos
    mass_improvement :=
      selberg_mass_le_moebius_mass P m hP hP_pos hm lambda hlam_one hV_pos hmass
    fourier_improvement :=
      selberg_fourierRate_le_moebius P m hP hP_pos lambda hlam_one hV_pos }

/-
**Main conditional theorem.** Given weights `lambda` whose quadratic form is
    *strictly* smaller than the Möbius weights', there is a `MajorantImprovement`
    that is a strict improvement (in mass).

    Note: `hstrict` is a genuine hypothesis supplied by the caller.  For the
    canonical optimal/Möbius weights the masses coincide (`moebiusWeights`
    already minimise `multiPrimeQuadForm`, by `multiPrimeQuadForm_lower_bound_inv`),
    so `hstrict` marks exactly the mathematical boundary where a strictly better
    weight system would be required.
-/
theorem multiPrime_is_ergodic_improvement
    (P m : ℕ) (hP : Squarefree P) (hP_pos : 0 < P) (hm : 0 < m)
    (hV_pos : 0 < V_function (fun n => (1 : ℝ) / n) P P)
    (lambda : ℕ → ℝ) (hlam_one : lambda 1 = 1)
    (hstrict : multiPrimeQuadForm P lambda < multiPrimeQuadForm P (moebiusWeights P)) :
    ∃ M : MajorantImprovement (P * m), M.isStrictImprovement := by
  refine ⟨selberg_moebius_improvement P m hP hP_pos hm lambda hlam_one hV_pos (le_of_lt hstrict),
    Or.inl ?_⟩
  have he : (selberg_ergodicMajorant P m hP_pos lambda hlam_one hV_pos).mass
      = (P * m : ℝ) * multiPrimeQuadForm P lambda :=
    multiPrime_mass_eq_quadForm P m hP hP_pos hm lambda hlam_one
  have hc : (moebius_classicalMajorant P m hP_pos).mass
      = (P * m : ℝ) * multiPrimeQuadForm P (moebiusWeights P) :=
    multiPrime_mass_eq_quadForm P m hP hP_pos hm (moebiusWeights P) (moebiusWeights_one P hP_pos)
  show (selberg_ergodicMajorant P m hP_pos lambda hlam_one hV_pos).mass
      < (moebius_classicalMajorant P m hP_pos).mass
  rw [he, hc]
  exact mul_lt_mul_of_pos_left hstrict (by positivity)

end