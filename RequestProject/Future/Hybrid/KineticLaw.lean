/-
# Hybrid.KineticLaw

Abstract mesoscopic interface: the kinetic law summarizes how local congruence
exclusions propagate into averaged statistical structure. The interface is
dimension-sensitive and exposes the quantitative outputs needed downstream.

Status: ProvedInProject (interface definition and basic properties)
-/
import Mathlib
import RequestProject.Core.MultiPrime.OptimalWeights
import RequestProject.Core.MultiPrime.MoebiusWeights
import RequestProject.Core.MultiPrime.GeneralWeightConnection

open MeasureTheory Finset BigOperators

noncomputable section

/-! ## Kinetic law interface -/

/-- A kinetic law: the mesoscopic interface between microscopic congruence
    exclusions and macroscopic sieve bounds. -/
structure KineticLaw where
  /-- The state space -/
  State : Type
  /-- The effective dimension of the sieve problem -/
  dimension : ℕ
  /-- Measurable space structure -/
  measurableSpace : MeasurableSpace State
  /-- Measure on the state space -/
  measure : @Measure State measurableSpace
  /-- Observable function: the "density" or "weight" at each state -/
  observable : State → ℝ
  /-- Admissibility predicate -/
  admissible : State → Prop
  /-- The observable dominates the indicator of admissible states -/
  dominatesIndicator : ∀ x, admissible x → 1 ≤ observable x
  /-- Normalization bound: ∫ observable dμ ≤ C · dim^k for some controlled constant -/
  normalizationConstant : ℝ
  normalizationBound : normalizationConstant > 0
  /-- Fourier decay parameter -/
  fourierDecayRate : ℝ
  fourierDecayPositive : fourierDecayRate > 0
  /-- Averaged remainder parameter -/
  avgRemainderBound : ℝ
  avgRemainderPositive : avgRemainderBound > 0

namespace KineticLaw

variable (K : KineticLaw)

/-- The dimension-scaled normalization: C · dim^α -/
def scaledNormalization (alpha : ℝ) : ℝ :=
  K.normalizationConstant * (K.dimension : ℝ) ^ alpha

/-- The effective density parameter: inverse of normalization -/
def effectiveDensity : ℝ :=
  1 / K.normalizationConstant

/-- Effective density is positive -/
lemma effectiveDensity_pos : 0 < K.effectiveDensity := by
  exact div_pos one_pos K.normalizationBound

/-- A kinetic law is said to be an improvement over a benchmark
    if its Fourier decay rate is strictly better. -/
def improvesOver (benchmark : KineticLaw) : Prop :=
  K.fourierDecayRate < benchmark.fourierDecayRate ∧
  K.dimension = benchmark.dimension

end KineticLaw

/-! ## Dimension-dependent bounds -/

/-- A dimension-scaling law: how a quantity grows with the dimension parameter. -/
structure DimensionScaling where
  /-- The base constant -/
  baseConstant : ℝ
  /-- The exponent -/
  exponent : ℝ
  /-- Base constant is positive -/
  hbase : baseConstant > 0
  /-- Exponent is nonneg -/
  hexp : exponent ≥ 0

namespace DimensionScaling

variable (D : DimensionScaling)

/-- Evaluate the scaling at a given dimension -/
def eval (dim : ℕ) : ℝ :=
  D.baseConstant * (dim : ℝ) ^ D.exponent

/-- The scaling is positive at any positive dimension -/
lemma eval_pos (dim : ℕ) (hdim : 0 < dim) : 0 < D.eval dim := by
  apply mul_pos D.hbase
  apply Real.rpow_pos_of_pos (Nat.cast_pos.mpr hdim)

end DimensionScaling

/-! ## Kinetic equilibrium -/

/-- A kinetic equilibrium: a state where the mesoscopic law is in a
    "steady state" that minimizes some functional. -/
structure KineticEquilibrium extends KineticLaw where
  /-- The free energy functional being minimized -/
  freeEnergy : ℝ
  /-- The equilibrium minimizes among all kinetic laws with the same dimension -/
  isMinimal : ∀ K' : KineticLaw, K'.dimension = dimension →
    freeEnergy ≤ K'.normalizationConstant * K'.fourierDecayRate

/-! ## The Selberg sieve as a concrete kinetic law

Given a `SieveDensity g P D` bundle, the Selberg sieve realizes a concrete
`KineticLaw`: the state space is `ℕ` (squarefree divisors of `P`), the dimension
is `ω(P) = P.primeFactors.card`, the measure is the counting measure, and the
normalization constant is `1 / V(D)` (the reciprocal of the Selberg `V`-sum).

The `observable` is taken to be the indicator of admissible states (so the
`dominatesIndicator` field holds on the nose); the quantitative content lives in
the normalization constant and in `selberg_effectiveDensity_eq_V`. -/

/-- The Selberg sieve, packaged as a `KineticLaw`. -/
noncomputable def selberg_kinetic_law
    (g : ℕ → ℝ) (P D : ℕ) (sd : SieveDensity g P D) :
    KineticLaw where
  State := ℕ
  dimension := P.primeFactors.card
  measurableSpace := inferInstance
  measure := MeasureTheory.Measure.count
  observable := fun d => if d ∈ sqfDivisors P ∧ d ≤ D then 1 else 0
  admissible := fun d => d ∈ sqfDivisors P ∧ d ≤ D
  dominatesIndicator := by
    intro d hd; rw [if_pos hd]
  normalizationConstant := 1 / V_function g P D
  normalizationBound :=
    div_pos one_pos (V_function_pos g P D sd.hP_pos.ne' sd.hD sd.hg1 sd.hh_nonneg)
  fourierDecayRate := V_function g P D
  fourierDecayPositive := V_function_pos g P D sd.hP_pos.ne' sd.hD sd.hg1 sd.hh_nonneg
  avgRemainderBound := 1
  avgRemainderPositive := one_pos

/-
The effective density of the Selberg kinetic law equals the `V`-sum `V(D)`.
-/
lemma selberg_effectiveDensity_eq_V
    (g : ℕ → ℝ) (P D : ℕ) (sd : SieveDensity g P D) :
    (selberg_kinetic_law g P D sd).effectiveDensity = V_function g P D := by
  simp only [KineticLaw.effectiveDensity, selberg_kinetic_law, one_div_one_div]

/-- The Selberg kinetic law is a `KineticEquilibrium` (with the conservative
    free energy `0`, which is a valid lower bound for every kinetic law). -/
noncomputable def selberg_is_equilibrium
    (g : ℕ → ℝ) (P D : ℕ) (sd : SieveDensity g P D) :
    KineticEquilibrium where
  toKineticLaw := selberg_kinetic_law g P D sd
  freeEnergy := 0
  isMinimal := by
    intro K' _
    exact le_of_lt (mul_pos K'.normalizationBound K'.fourierDecayPositive)

end