/-
# Assumptions Registry

Every theorem and major definition is labeled as one of:
- `ImportedFromMathlib`: uses existing Mathlib infrastructure
- `ProvedInProject`: proved within this project
- `AssumedForProgram`: assumed as a hypothesis for the research program

This file serves as the central registry for tracking proof status.
-/

/-! ## Status tracking -/

/-- Proof status of a statement in the project. -/
inductive ProofStatus where
  | ImportedFromMathlib : ProofStatus
  | ProvedInProject : ProofStatus
  | AssumedForProgram : ProofStatus
  | ScaffoldedNotProved : ProofStatus
  deriving Repr, DecidableEq, BEq

/-! ## Registry entries -/

/-- A registry entry recording the status of a statement. -/
structure RegistryEntry where
  /-- Name of the statement -/
  name : String
  /-- Module where it lives -/
  module : String
  /-- Proof status -/
  status : ProofStatus
  /-- Brief description -/
  description : String

/-- The project assumptions registry. -/
def assumptionsRegistry : List RegistryEntry := [
  -- Sieve.Basic
  { name := "SieveData"
    module := "Sieve.Basic"
    status := .ProvedInProject
    description := "Classical sieve data structure" },
  { name := "SieveData.local_density_decomp"
    module := "Sieve.Basic"
    status := .ProvedInProject
    description := "Local density decomposition |A_d| = X/f(d) + R_d" },
  { name := "squarefreeDivisors"
    module := "Sieve.Basic"
    status := .ProvedInProject
    description := "Squarefree divisor API" },
  { name := "UpperBoundSieve"
    module := "Sieve.Basic"
    status := .ProvedInProject
    description := "Abstract upper-bound sieve framework" },

  -- Sieve.Weights
  { name := "SelbergWeights"
    module := "Sieve.Weights.Definition"
    status := .ProvedInProject
    description := "Selberg weight system definition" },
  { name := "SelbergWeights.diagTerm_nonneg"
    module := "Sieve.Weights.Definition"
    status := .ProvedInProject
    description := "Diagonal term nonnegativity" },

  -- Sieve.Weights.UpperBound
  { name := "sieveWeight_coprime_eq"
    module := "Sieve.Weights.UpperBound"
    status := .ProvedInProject
    description := "Sieve weight for coprime elements equals λ_1" },
  { name := "siftedSet_card_le_quadraticSum"
    module := "Sieve.Weights.UpperBound"
    status := .ProvedInProject
    description := "Selberg upper bound: |siftedSet| ≤ Q_A(λ)" },
  { name := "weighted_remainder_bound"
    module := "Sieve.Weights.UpperBound"
    status := .ProvedInProject
    description := "Error bound: Σ λ_d R_d ≤ Σ |λ_d| |R_d|" },

  -- Sieve.Weights.Optimization
  { name := "SelbergWeights.linForm_sq_le_diagTerm_mul_recipSum"
    module := "Sieve.Weights.Optimization"
    status := .ProvedInProject
    description := "Cauchy-Schwarz: L(λ)² ≤ diagTerm · V(D)" },
  { name := "SelbergWeights.diagTerm_le_quadForm"
    module := "Sieve.Weights.Optimization"
    status := .ProvedInProject
    description := "Q(λ) ≥ diagTerm when off-diagonal terms nonneg" },
  { name := "SelbergWeights.recipSum_pos"
    module := "Sieve.Weights.Optimization"
    status := .ProvedInProject
    description := "Reciprocal sum V(D) > 0" },

  -- Sieve.Majorant
  { name := "Majorant"
    module := "Sieve.Majorant"
    status := .ProvedInProject
    description := "Abstract majorant interface" },
  { name := "Majorant.mass_ge_targetMass"
    module := "Sieve.Majorant"
    status := .ProvedInProject
    description := "Mass domination from pointwise domination" },

  -- Sieve.MajorantComparison
  { name := "toyComparison_massImprovement"
    module := "Sieve.MajorantComparison"
    status := .ProvedInProject
    description := "Toy mass improvement: indicator vs constant majorant" },
  { name := "exists_mass_improvement"
    module := "Sieve.MajorantComparison"
    status := .ProvedInProject
    description := "Existence of a MajorantComparison with massImprovement" },

  -- Sieve.SelbergComparison
  { name := "selbergComparison_massImprovement"
    module := "Sieve.SelbergComparison"
    status := .ProvedInProject
    description := "Main theorem: sieve-shaped majorant has strictly smaller mass than constant baseline" },
  { name := "sieveMajorant_not_target"
    module := "Sieve.SelbergComparison"
    status := .ProvedInProject
    description := "The sieve majorant is NOT the target indicator (genuinely sieve-shaped)" },
  { name := "card_multiplesInFin"
    module := "Sieve.SelbergComparison"
    status := .ProvedInProject
    description := "Number of multiples of d in Fin(d*m) equals m" },
  { name := "sieveMajorant_mass"
    module := "Sieve.SelbergComparison"
    status := .ProvedInProject
    description := "Mass of sieve majorant = d*m - m/2" },
  { name := "sieveMajorant_targetMass"
    module := "Sieve.SelbergComparison"
    status := .ProvedInProject
    description := "targetMass of Selberg sieve majorant = d*m - m" },

  -- Sieve.Fourier
  { name := "dft'"
    module := "Sieve.Fourier"
    status := .ProvedInProject
    description := "Discrete Fourier transform definition" },
  { name := "parseval'"
    module := "Sieve.Fourier"
    status := .ProvedInProject
    description := "Parseval's theorem for DFT" },

  -- Sieve.Transference (strengthened)
  { name := "StrongPseudorandomMajorant"
    module := "Sieve.Transference"
    status := .AssumedForProgram
    description := "Pseudorandom majorant with 2-point correlation condition" },
  { name := "StrongPseudorandomMajorant.total_weightedPairCount"
    module := "Sieve.Transference"
    status := .AssumedForProgram
    description := "Total weighted pair count = (Σ ν)²" },

  -- Sieve.FourierRatio (Parseval-based proof)
  { name := "mass_sq_le_N_mul_l2NormSq_via_parseval"
    module := "Sieve.FourierRatio"
    status := .ProvedInProject
    description := "Parseval-based proof: mass² ≤ N · l2NormSq via dft_zero_eq_sum' and parseval'" },

  -- Sieve.Weights.FourierConnection
  { name := "card_multiples_of_dvd"
    module := "Sieve.Weights.FourierConnection"
    status := .ProvedInProject
    description := "Number of multiples of d in Fin N equals N/d when d ∣ N" },
  { name := "card_joint_multiples"
    module := "Sieve.Weights.FourierConnection"
    status := .ProvedInProject
    description := "Joint divisibility count equals lcm divisibility count" },
  { name := "sieveMajorant_l2NormSq"
    module := "Sieve.Weights.FourierConnection"
    status := .ProvedInProject
    description := "L² norm of sieve majorant = d*m - 3m/4 (direct computation)" },
  { name := "sieveBaseline_l2NormSq"
    module := "Sieve.Weights.FourierConnection"
    status := .ProvedInProject
    description := "L² norm of constant baseline = d*m" },
  { name := "sieveMajorant_l2_improvement"
    module := "Sieve.Weights.FourierConnection"
    status := .ProvedInProject
    description := "L² improvement: sieve majorant has strictly smaller L² norm than constant baseline" },
  { name := "sieveMajorant_l2NormSq_eq_selbergForm"
    module := "Sieve.Weights.FourierConnection"
    status := .ProvedInProject
    description := "L² norm / N = 1 - 3/(4d) = Selberg quadratic form Q(λ) at λ₁=1, λ_d=-1/2" },
  { name := "selbergComparison_dual_improvement"
    module := "Sieve.Weights.FourierConnection"
    status := .ProvedInProject
    description := "Selberg sieve achieves simultaneous mass AND L² improvement over constant baseline" },
  { name := "selberg_concrete_restriction_bound"
    module := "Sieve.Weights.FourierConnection"
    status := .ProvedInProject
    description := "Explicit Fourier restriction lower bound for Selberg majorant in terms of (d, m)" },

  -- Sieve.RestrictionLowerBound
  { name := "fin_cauchy_schwarz"
    module := "Sieve.RestrictionLowerBound"
    status := .ProvedInProject
    description := "Generic Cauchy-Schwarz: (Σ f)² ≤ N · Σ f²" },
  { name := "restriction_lower_bound"
    module := "Sieve.RestrictionLowerBound"
    status := .ProvedInProject
    description := "Restriction lower bound: mass² · l2NormSq ≥ targetMass⁴ / N" },
  { name := "restriction_lower_bound_zero_mode"
    module := "Sieve.RestrictionLowerBound"
    status := .ProvedInProject
    description := "Fourier reformulation of restriction lower bound via Parseval" },
  { name := "additiveEnergy_lower_bound"
    module := "Sieve.RestrictionLowerBound"
    status := .ProvedInProject
    description := "Additive energy lower bound: E(f) ≥ (Σ f²)² / N for nonneg f" },
  { name := "sieve_additive_energy_lower"
    module := "Sieve.RestrictionLowerBound"
    status := .ProvedInProject
    description := "Sieve additive energy: E(ν) ≥ targetMass⁴ / N³" },

  -- Sieve.SelbergRestriction (Section E)
  { name := "sieveMajorant_l2NormSq_explicit"
    module := "Sieve.SelbergRestriction"
    status := .ProvedInProject
    description := "Exact L² norm (alternate form): ‖ν‖₂² = m/4 + (d*m - m)" },
  { name := "sieveMajorant_l2NormSq_eq_selbergForm_explicit"
    module := "Sieve.SelbergRestriction"
    status := .ProvedInProject
    description := "L² norm = N · (1 - 3/(4d)), the Selberg quadratic form identity (alternate form)" },
  { name := "selberg_restriction_lower_bound_explicit"
    module := "Sieve.SelbergRestriction"
    status := .ProvedInProject
    description := "End-to-end restriction lower bound in (d,m): mass² · ‖ν‖₂² ≥ (d*m-m)⁴/(d*m)" },
  { name := "selberg_additive_energy_explicit"
    module := "Sieve.SelbergRestriction"
    status := .ProvedInProject
    description := "Additive energy lower bound in (d,m): E(ν) ≥ (d*m-m)⁴/(d*m)³" },

  -- Sieve.KineticPropagation
  { name := "SievePerturbation"
    module := "Sieve.KineticPropagation"
    status := .ProvedInProject
    description := "Perturbation object for two sieves with different density functions" },
  { name := "prod_perturb"
    module := "Sieve.KineticPropagation"
    status := .ProvedInProject
    description := "Product perturbation lemma: |ac - bd| ≤ |a||c-d| + |d||a-b|" },
  { name := "finset_prod_perturb"
    module := "Sieve.KineticPropagation"
    status := .ProvedInProject
    description := "Finset product perturbation: |∏f - ∏g| ≤ ε·|S|·M^(|S|-1)" },
  { name := "perturbation_propagates"
    module := "Sieve.KineticPropagation"
    status := .ProvedInProject
    description := "Core Kinetic Propagation Theorem: Lipschitz bound on f(d) for squarefree d" },
  { name := "eulerProduct_stability"
    module := "Sieve.KineticPropagation"
    status := .ProvedInProject
    description := "Euler product stability under prime-level perturbation" },
  { name := "xlogx_lipschitz"
    module := "Sieve.KineticPropagation"
    status := .ProvedInProject
    description := "Lipschitz bound for x·log(x): |a·log(a) - b·log(b)| ≤ (1+|log a|+|log b|)·|a-b|" },
  { name := "sieveHFunctional"
    module := "Sieve.KineticPropagation"
    status := .ProvedInProject
    description := "Arithmetic H-functional (Boltzmann analogue)" },
  { name := "sieveH_stable"
    module := "Sieve.KineticPropagation"
    status := .ProvedInProject
    description := "H-functional stability under perturbation" },
  { name := "sieveState_densityFactor_compat"
    module := "Sieve.KineticPropagation"
    status := .ProvedInProject
    description := "Bridge lemma: SieveState compatibility implies density factor bound" },

  -- Core.MassEnergyTradeoff.SharpBounds
  { name := "selberg_l2_lower_bound"
    module := "Core.MassEnergyTradeoff.SharpBounds"
    status := .ProvedInProject
    description := "‖ν‖₂² ≥ |S|⁴ / (N³ · Q(λ)²) — sharp mass-energy tradeoff" },

  -- Core.CorrelationBound.AdditiveEnergyLower
  { name := "correlation_additive_energy_lower"
    module := "Core.CorrelationBound.AdditiveEnergyLower"
    status := .ProvedInProject
    description := "E(ν) ≥ N³(1 − 2ε − 4δ) — correlation-enhanced additive energy lower bound" },
  { name := "additiveEnergy_eq_sum_correlationSq"
    module := "Core.CorrelationBound.AdditiveEnergyLower"
    status := .ProvedInProject
    description := "E(ν) = Σ_h (correlationSum ν h)²" },
  { name := "correlationSum_total_eq_sq"
    module := "Core.CorrelationBound.AdditiveEnergyLower"
    status := .ProvedInProject
    description := "Σ_h g(h) = (Σ ν)²" },
  { name := "sum_sq_ge_sq_div"
    module := "Core.CorrelationBound.AdditiveEnergyLower"
    status := .ProvedInProject
    description := "Cauchy-Schwarz: Σ g(h)² ≥ (Σ g(h))² / N" },

  -- Core.MultiPrime.FourierRatioSharp
  { name := "sieveMass_eq_quadForm"
    module := "Core.MultiPrime.FourierRatioSharp"
    status := .ProvedInProject
    description := "Mass of Selberg majorant = N · Q(λ)" },
  { name := "parseval_real"
    module := "Core.MultiPrime.FourierRatioSharp"
    status := .ProvedInProject
    description := "Parseval for real-valued functions: Σ ‖ν̂(ξ)‖² = N · Σ ν(x)²" },
  { name := "sharp_fourier_ratio_lower_bound"
    module := "Core.MultiPrime.FourierRatioSharp"
    status := .ProvedInProject
    description := "∃ ξ ≠ 0, ‖ν̂(ξ)‖² ≥ (N·Σν² − mass²)/(N−1) — novel Fourier ratio lower bound" },

  -- Core.MultiPrime.OptimalWeights
  { name := "optimalWeight_quadForm_eq"
    module := "Core.MultiPrime.OptimalWeights"
    status := .ProvedInProject
    description := "Q(λ_opt) = 1/V(1/·,P,D) via Selberg diagonalisation + Möbius inversion" },

  -- Core.MultiPrime.MoebiusWeights
  { name := "optimalWeight_quadForm_eq_moebius"
    module := "Core.MultiPrime.MoebiusWeights"
    status := .ProvedInProject
    description := "Q(μ) = 1/V(1/·, P, P) at Möbius weights" },
  { name := "moebiusWeights_one"
    module := "Core.MultiPrime.MoebiusWeights"
    status := .ProvedInProject
    description := "moebiusWeights P 1 = 1" },
  { name := "multiPrimeQuadForm_lower_bound'"
    module := "Core.MultiPrime.MoebiusWeights"
    status := .ProvedInProject
    description := "Q(λ) ≥ φ(P)/P when λ₁ = 1 and supp ⊆ sqfDivisors P" },

  -- Core.MultiPrime.SelbergWeightCorrelation
  { name := "selbergWeight_correlation_coprime_bound"
    module := "Core.MultiPrime.SelbergWeightCorrelation"
    status := .ProvedInProject
    description := "Coprime-shift correlation ≤ (P*m)*Q(λ)" },
  { name := "selbergWeight_autocorrelation_eq"
    module := "Core.MultiPrime.SelbergWeightCorrelation"
    status := .ProvedInProject
    description := "h=0 autocorrelation = (P*m)*Q(λ)" },

  -- Core.KineticStability.QuadFormPerturbation
  { name := "multiPrimeQuadForm_perturbation"
    module := "Core.KineticStability.QuadFormPerturbation"
    status := .ProvedInProject
    description := "|Q(λ) − Q(μ)| ≤ 2C Σ δ_d / lcm(d,e) — quadratic form perturbation" },

  -- Dynamics (Future — scaffolded, not proved)
  { name := "CompatibleSystem"
    module := "Dynamics.ProfiniteState"
    status := .ScaffoldedNotProved
    description := "Compatible system of residues (profinite element)" },
  { name := "AdmissibleSet.complement_density"
    module := "Dynamics.SieveState"
    status := .ScaffoldedNotProved
    description := "Complement density + density = 1" },
  { name := "orbit_avg_eq_space_avg"
    module := "Dynamics.Spectrum"
    status := .ScaffoldedNotProved
    description := "Orbit average = space average for full orbit" },

  -- Hybrid (Future — scaffolded, not proved)
  { name := "KineticLaw"
    module := "Hybrid.KineticLaw"
    status := .ScaffoldedNotProved
    description := "Mesoscopic kinetic law interface" },
  { name := "ErgodicMajorant"
    module := "Hybrid.ErgodicMajorant"
    status := .ScaffoldedNotProved
    description := "Majorant constructed from kinetic data" },
  { name := "MajorantImprovement.noRegression"
    module := "Hybrid.ErgodicMajorant"
    status := .ScaffoldedNotProved
    description := "No-regression theorem" },

  -- Models (Future — scaffolded, not proved)
  { name := "CyclicSieve"
    module := "Models.CyclicToy"
    status := .ScaffoldedNotProved
    description := "Cyclic toy sieve model" },
  { name := "RandomSieveModel"
    module := "Models.RandomSieve"
    status := .ScaffoldedNotProved
    description := "Random sieve model" },
  { name := "FunctionFieldSieveData"
    module := "Models.FunctionField"
    status := .ScaffoldedNotProved
    description := "Function-field sieve data" },

  -- Applications (Future — scaffolded, not proved)
  { name := "FunctionFieldSieveResult.strict_improvement"
    module := "Applications.FunctionFieldSieve"
    status := .AssumedForProgram
    description := "Strict improvement theorem (conditional on structure hypotheses)" },
  { name := "APTransference.fAPCount_le_nuAPCount"
    module := "Applications.TransferenceLike"
    status := .ScaffoldedNotProved
    description := "AP count domination (proved from pointwise domination)" },
  { name := "ChenTypeResult.improvedThreshold_le"
    module := "Applications.ChenLike"
    status := .AssumedForProgram
    description := "Threshold improvement (conditional on structure hypotheses)" }
]
