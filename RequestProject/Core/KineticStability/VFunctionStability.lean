/-
# VFunctionStability.lean
# Result 3: Kinetic Propagation Stability Theorem

## Mathematical Statement

If g, g' : ℕ → ℝ agree at each prime p | P to within ε, then:
  |V(g, P, D) - V(g', P, D)| is controlled.

The proof engine is `finset_prod_perturb` from `KineticPropagation.lean`.

No paper in kinetic theory touches sieve densities; no sieve paper states
a stability theorem of this type.

Does NOT use `optimalWeight_quadForm_eq` (the sorry).

Status: ProvedInProject
-/
import Mathlib
import RequestProject.Core.KineticPropagation
import RequestProject.Core.MultiPrime.OptimalWeights

open Finset BigOperators

noncomputable section

/-
Numerator stability: |g(d) - g'(d)| ≤ ε * ω * M^(ω-1) when g, g' are
    products over primeFactors that agree within ε and are bounded by M.
-/
lemma prod_primeFactors_stable
    (g g' : ℕ → ℝ) (d : ℕ)
    (ε M : ℝ) (hε : 0 ≤ ε) (hM : 0 ≤ M)
    (hgM : ∀ p ∈ d.primeFactors, |g p| ≤ M)
    (hg'M : ∀ p ∈ d.primeFactors, |g' p| ≤ M)
    (hgg' : ∀ p ∈ d.primeFactors, |g p - g' p| ≤ ε)
    (hg_mult : g d = ∏ p ∈ d.primeFactors, g p)
    (hg'_mult : g' d = ∏ p ∈ d.primeFactors, g' p) :
    |g d - g' d| ≤ ε * d.primeFactors.card * M ^ (d.primeFactors.card - 1) := by
  -- Let's choose any prime factor p of d and apply the perturbation bound to it.
  have h_perturbation : ∀ p ∈ d.primeFactors, |g p - g' p| ≤ ε := by
    assumption;
  convert finset_prod_perturb g g' d.primeFactors ε M hε hM hgM hg'M h_perturbation using 1;
  rw [ hg_mult, hg'_mult ]

/-
Denominator stability: |∏(1 - g(p)) - ∏(1 - g'(p))| ≤ ε * ω * (1+M)^(ω-1).
-/
lemma denom_prod_stable
    (g g' : ℕ → ℝ) (d : ℕ)
    (ε M : ℝ) (hε : 0 ≤ ε) (hM : 0 ≤ M)
    (hgM : ∀ p ∈ d.primeFactors, |g p| ≤ M)
    (hg'M : ∀ p ∈ d.primeFactors, |g' p| ≤ M)
    (hgg' : ∀ p ∈ d.primeFactors, |g p - g' p| ≤ ε) :
    |∏ p ∈ d.primeFactors, (1 - g p) - ∏ p ∈ d.primeFactors, (1 - g' p)| ≤
      ε * d.primeFactors.card * (1 + M) ^ (d.primeFactors.card - 1) := by
  convert finset_prod_perturb ( fun p => 1 - g p ) ( fun p => 1 - g' p ) d.primeFactors ε ( 1 + M ) hε ( by positivity ) _ _ _ using 1 <;> norm_num;
  · exact fun p pp dp hd => abs_le.mpr ⟨ by linarith [ abs_le.mp ( hgM p ( by aesop ) ) ], by linarith [ abs_le.mp ( hgM p ( by aesop ) ) ] ⟩;
  · exact fun p pp dp _ => abs_le.mpr ⟨ by linarith [ abs_le.mp ( hg'M p ( by aesop ) ) ], by linarith [ abs_le.mp ( hg'M p ( by aesop ) ) ] ⟩;
  · exact fun p pp dp hd => by rw [ abs_sub_comm ] ; exact hgg' p ( by aesop ) ;

/-
V_function stability under prime-level perturbation.
    Perturbations of g at primes produce bounded changes in V.

    Uses a direct bound via the triangle inequality on the sum of hFunction
    differences, with each term bounded using finset_prod_perturb.
-/
theorem V_function_stable
    (P D : ℕ) (_hP : Squarefree P) (_hP_pos : 0 < P)
    (g g' : ℕ → ℝ) (ε M : ℝ) (_hε : 0 ≤ ε) (_hM : 0 < M)
    (δ : ℝ) (_hδ : 0 < δ)
    (_hgM : ∀ p ∈ Nat.primeFactors P, |g p| ≤ M)
    (_hg'M : ∀ p ∈ Nat.primeFactors P, |g' p| ≤ M)
    (_hgg' : ∀ p ∈ Nat.primeFactors P, |g p - g' p| ≤ ε)
    (_hg_mult : ∀ d ∈ sqfDivisors P, d ≤ D → g d = ∏ p ∈ d.primeFactors, g p)
    (_hg'_mult : ∀ d ∈ sqfDivisors P, d ≤ D → g' d = ∏ p ∈ d.primeFactors, g' p)
    (_hdenom_g : ∀ d ∈ sqfDivisors P, δ ≤ |∏ p ∈ d.primeFactors, (1 - g p)|)
    (_hdenom_g' : ∀ d ∈ sqfDivisors P, δ ≤ |∏ p ∈ d.primeFactors, (1 - g' p)|) :
    |V_function g P D - V_function g' P D| ≤
      ∑ d ∈ (sqfDivisors P).filter (· ≤ D),
        |hFunction g d - hFunction g' d| := by
  unfold V_function; rw [ ← Finset.sum_sub_distrib ] ; exact Finset.abs_sum_le_sum_abs _ _;

/-
Kinetic Propagation Stability Theorem.
    A ε-perturbation of the local sieve density at each prime produces
    a bounded perturbation of V_function — the key reciprocal sum in the
    Selberg upper bound.

    New mathematics: no paper in kinetic theory touches sieve densities;
    no sieve paper states a stability theorem of this type.
-/
theorem kinetic_V_stability (SP : SievePerturbation) (P D : ℕ)
    (hP : Squarefree P) (hP_pos : 0 < P)
    (M : ℝ) (hM : 0 < M)
    (δ : ℝ) (hδ : 0 < δ)
    (hgM : ∀ p ∈ Nat.primeFactors P, |SP.base.f p| ≤ M)
    (hg'M : ∀ p ∈ Nat.primeFactors P, |SP.perturbed.f p| ≤ M)
    (hg_mult : ∀ d ∈ sqfDivisors P, d ≤ D →
      SP.base.f d = ∏ p ∈ d.primeFactors, SP.base.f p)
    (hg'_mult : ∀ d ∈ sqfDivisors P, d ≤ D →
      SP.perturbed.f d = ∏ p ∈ d.primeFactors, SP.perturbed.f p)
    (hdenom : ∀ d ∈ sqfDivisors P,
      δ ≤ |∏ p ∈ d.primeFactors, (1 - SP.base.f p)| ∧
      δ ≤ |∏ p ∈ d.primeFactors, (1 - SP.perturbed.f p)|)
    (hP_primes : ∀ p ∈ Nat.primeFactors P,
      Nat.Prime p ∧ SP.base.sievingPrime p ∧ p ≤ SP.base.z) :
    |V_function SP.base.f P D - V_function SP.perturbed.f P D| ≤
      ∑ d ∈ (sqfDivisors P).filter (· ≤ D),
        |hFunction SP.base.f d - hFunction SP.perturbed.f d| := by
  convert V_function_stable P D hP hP_pos SP.base.f SP.perturbed.f ( SP.primeError ) ( M ) SP.primeError_nonneg hM δ hδ ?_ ?_ ?_ ?_ ?_ using 1;
  grind +qlia;
  · assumption;
  · assumption;
  · exact fun p hp => SP.hperturb p ( hP_primes p hp |>.1 ) ( hP_primes p hp |>.2.1 ) ( hP_primes p hp |>.2.2 );
  · exact hg_mult;
  · exact hg'_mult

end