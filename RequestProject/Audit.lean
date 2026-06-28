-- Audit.lean: axiom footprint for all main theorems.
-- Expected for each: [propext, Classical.choice, Quot.sound]
-- Any 'sorry' invalidates the proof chain.

import RequestProject.Core.SelbergComparison
import RequestProject.Core.KineticPropagation
import RequestProject.Core.RestrictionLowerBound
import RequestProject.Core.Weights.FourierConnection
import RequestProject.Core.SelbergRestriction
import RequestProject.Core.Weights.QuadFormStability
import RequestProject.Core.Weights.UpperBound
import RequestProject.Core.MultiPrime.Setup
import RequestProject.Core.MultiPrime.JointCount
import RequestProject.Core.MultiPrime.L2Identity
import RequestProject.Core.MultiPrime.FourierRatio
import RequestProject.Core.MassEnergyTradeoff.SharpBounds
import RequestProject.Core.CorrelationBound.AdditiveEnergyLower
import RequestProject.Core.KineticStability.QuadFormPerturbation
import RequestProject.Core.MultiPrime.FourierRatioSharp
import RequestProject.Core.MultiPrime.SelbergCorrelation
import RequestProject.Core.MultiPrime.MoebiusWeights
import RequestProject.Core.MultiPrime.SelbergWeightCorrelation
import RequestProject.Core.MultiPrime.SelbergUpperBound
import RequestProject.Core.MultiPrime.RemainderBound
import RequestProject.Core.MultiPrime.SelbergCorrelationBoundDisproved
import RequestProject.Core.MultiPrime.GeneralWeightConnection

-- ── Multi-prime extension ────────────────────────────────────────────────────
#print axioms selbergNu_dominates
#print axioms card_joint_multiples_of_lcm
#print axioms l2NormSq_multiPrime_eq_quadForm
#print axioms multiPrime_mass_eq_quadForm
#print axioms multiPrime_quadForm_lower_bound
#print axioms multiPrime_restriction_lower_bound

-- ── Extension 1: Sharp Mass-Energy Tradeoff ─────────────────────────────────
#print axioms selberg_l2_lower_bound

-- ── Extension 2: Correlation-Enhanced Additive Energy Lower Bound ───────────
#print axioms correlationSum_total_eq_sq
#print axioms sum_sq_ge_sq_div
#print axioms correlation_sum_approx_N
#print axioms mass_approx_N
#print axioms additiveEnergy_eq_sum_correlationSq

-- ── Extension: Abstract pseudorandom bound (not instantiated for multiPrimeMajorant) ───────────
#print axioms correlation_additive_energy_lower

-- ── Extension 3: Quadratic Form Perturbation ────────────────────────────────
#print axioms multiPrimeQuadForm_perturbation

-- ── Extension 4: Sharp Fourier Ratio Lower Bound (novel) ───────────────────
#print axioms sieveMass_eq_quadForm
#print axioms real_l2NormSq_eq
#print axioms parseval_real
#print axioms fourier_zero_norm_sq
#print axioms nonzero_fourier_sum_eq
#print axioms exists_ge_of_sum_ge
#print axioms sharp_fourier_ratio_lower_bound

-- ── Extension 5: Correlation Definitions ─────────────────────────────────
#print axioms correlationBound_nonneg
#print axioms selbergNu_autocorrelation_eq_l2

-- ── MoebiusWeights ──────────────────────────────────────────────────────────
#print axioms moebiusWeights_one
#print axioms moebius_quadForm_eq
#print axioms multiPrimeQuadForm_lower_bound'
#print axioms optimalWeight_quadForm_eq_moebius
#print axioms multiPrimeQuadForm_lower_bound_inv

-- ── Selberg Upper Bound (corrected) ─────────────────────────────────────────
#print axioms selberg_upper_bound_multiPrime
#print axioms selberg_l2_sharp

-- ── Coprime-shift correlation (Gap 4 resolution) ────────────────────────────
#print axioms selbergWeight_correlation_coprime_bound
#print axioms selbergWeight_autocorrelation_eq
#print axioms coprimePairsQuadForm_le_multiPrimeQuadForm

-- ── Remainder bound completion ───────────────────────────────────────────────
#print axioms selbergNu_eq_sieveWeight_sq
#print axioms finRange_Ad_lcm_card
#print axioms quadraticMajorantSum_eq_mainTerm_plus_errorTerm
#print axioms double_error_le_moebiusRemainderBound
#print axioms siftedCount_le_quadraticMajorantSum
#print axioms selberg_upper_bound_complete

-- ── Correlation Bound Disproof ────────────────────────────────────────────────
#print axioms selbergNu_correlation_bound_is_false

-- ── General Weight Connection (now unconditional) ────────────────────────────

-- sorry-free
#print axioms double_error_le_selbergRemainderBound
-- Expected: [propext, Classical.choice, Quot.sound]

-- now sorry-free: optimalWeight_quadForm_eq is fully proved
#print axioms optimalWeight_quadForm_eq
#print axioms selberg_mass_eq_general
#print axioms selberg_l2_lower_bound_general
#print axioms selberg_upper_bound_general
#print axioms selberg_unified_connection_general
-- Expected: [propext, Classical.choice, Quot.sound]
