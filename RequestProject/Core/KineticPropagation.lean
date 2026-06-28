/-
# Sieve.KineticPropagation

The Kinetic Propagation Theorem for sieve densities.

If two multiplicative sieve density functions f, g agree to within ε at each prime,
then their values at squarefree composites d = p₁ · ... · pₖ differ by at most
  ε · k · M^(k-1)
where M bounds max(f(pᵢ), g(pᵢ)) and k = ω(d).

This is a Lipschitz propagation bound: perturbations grow at most linearly
in the number of prime factors, controlled by the maximum local density.

The file also establishes:
- Euler product stability under perturbation
- The arithmetic H-functional (Boltzmann analogue) and its stability
-/
import Mathlib
import RequestProject.Core.Basic

open Finset BigOperators Nat

noncomputable section

/-! ## Phase 1: The Perturbation Object -/

/-- Two sieve data with the same structure but different local density functions.
    This captures the setup for the Kinetic Propagation Theorem. -/
structure SievePerturbation where
  base : SieveData
  perturbed : SieveData
  /-- Same sifting set -/
  same_A : base.A = perturbed.A
  /-- Same normalization -/
  same_X : base.X = perturbed.X
  /-- Same sieving primes -/
  same_sievingPrime : base.sievingPrime = perturbed.sievingPrime
  /-- Same sieving level -/
  same_z : base.z = perturbed.z
  /-- Perturbation bound at primes -/
  primeError : ℝ
  primeError_nonneg : 0 ≤ primeError
  /-- The density functions agree to within primeError at each sieving prime -/
  hperturb : ∀ p : ℕ, p.Prime → base.sievingPrime p → p ≤ base.z →
    |base.f p - perturbed.f p| ≤ primeError

/-! ## Phase 2: Product Perturbation Lemma -/

/-
The algebraic engine: |a*c - b*d| ≤ |a|*|c - d| + |d|*|a - b|.
    This is the key algebraic identity a*c - b*d = a*(c-d) + d*(a-b)
    followed by the triangle inequality.
-/
lemma prod_perturb (a b c d : ℝ) :
    |a * c - b * d| ≤ |a| * |c - d| + |d| * |a - b| := by
  rw [ ← abs_mul, ← abs_mul ];
  cases abs_cases ( a * c - b * d ) <;> cases abs_cases ( a * ( c - d ) ) <;> cases abs_cases ( d * ( a - b ) ) <;> linarith

/-! ## Phase 3: Propagation on finite products -/

/-
Perturbation bound for a product of values over a finset.
    If |f(p) - g(p)| ≤ ε for all p ∈ S, and both f, g are bounded by M on S,
    then |∏ p ∈ S, f(p) - ∏ p ∈ S, g(p)| ≤ ε · |S| · M^(|S| - 1).
-/
lemma finset_prod_perturb (f g : ℕ → ℝ) (S : Finset ℕ) (ε M : ℝ)
    (hε : 0 ≤ ε) (hM : 0 ≤ M)
    (hfM : ∀ p ∈ S, |f p| ≤ M) (hgM : ∀ p ∈ S, |g p| ≤ M)
    (hfg : ∀ p ∈ S, |f p - g p| ≤ ε) :
    |∏ p ∈ S, f p - ∏ p ∈ S, g p| ≤ ε * S.card * M ^ (S.card - 1) := by
  induction' S using Finset.induction with p S hpS ih;
  · norm_num;
  · simp_all +decide [ Finset.prod_insert hpS ];
    -- Apply the induction hypothesis to bound the difference of the products.
    have h_ind : |∏ p ∈ S, f p| ≤ M ^ S.card ∧ |∏ p ∈ S, g p| ≤ M ^ S.card := by
      exact ⟨ by rw [ Finset.abs_prod ] ; exact le_trans ( Finset.prod_le_prod ( fun _ _ => abs_nonneg _ ) fun _ _ => hfM.2 _ ‹_› ) ( by norm_num ), by rw [ Finset.abs_prod ] ; exact le_trans ( Finset.prod_le_prod ( fun _ _ => abs_nonneg _ ) fun _ _ => hgM.2 _ ‹_› ) ( by norm_num ) ⟩;
    refine' le_trans ( prod_perturb _ _ _ _ ) _;
    refine le_trans ( add_le_add ( mul_le_mul hfM.1 ih ( by positivity ) ( by positivity ) ) ( mul_le_mul h_ind.2 hfg.1 ( by positivity ) ( by positivity ) ) ) ?_;
    cases S using Finset.induction <;> simp_all +decide [ pow_succ' ] ; ring_nf ; norm_num

/-
Perturbation bound for multiplicative sieve densities at squarefree d.
    This is the core of the Kinetic Propagation Theorem:
    perturbations in f(p) propagate to f(d) with at most linear growth in ω(d).
-/
theorem perturbation_propagates (P : SievePerturbation)
    (M : ℝ) (hM : 0 ≤ M)
    (hfM : ∀ p : ℕ, p.Prime → P.base.sievingPrime p → p ≤ P.base.z → |P.base.f p| ≤ M)
    (hgM : ∀ p : ℕ, p.Prime → P.base.sievingPrime p → p ≤ P.base.z → |P.perturbed.f p| ≤ M)
    (d : ℕ) (hd : Squarefree d)
    (hd_primes : ∀ p ∈ d.primeFactors, p.Prime ∧ P.base.sievingPrime p ∧ p ≤ P.base.z) :
    |P.base.f d - P.perturbed.f d| ≤
      P.primeError * d.primeFactors.card * M ^ (d.primeFactors.card - 1) := by
  by_contra h_contra;
  have h_base : P.base.f d = ∏ p ∈ d.primeFactors, P.base.f p := by
    have h_base : ∀ {S : Finset ℕ}, (∀ p ∈ S, Nat.Prime p) → (∀ p ∈ S, P.base.sievingPrime p) → P.base.f (∏ p ∈ S, p) = ∏ p ∈ S, P.base.f p := by
      intros S hS_prime hS_sieving
      induction' S using Finset.induction with p S hpS ih;
      · simpa using P.base.hf_one;
      · rw [ Finset.prod_insert hpS, P.base.hf_mult ];
        · rw [ Finset.prod_insert hpS, ih ( fun q hq => hS_prime q ( Finset.mem_insert_of_mem hq ) ) ( fun q hq => hS_sieving q ( Finset.mem_insert_of_mem hq ) ) ];
        · exact Nat.prime_iff.mp ( hS_prime p ( Finset.mem_insert_self _ _ ) ) |> fun h => h.squarefree;
        · have h_prod_squarefree : ∀ {S : Finset ℕ}, (∀ p ∈ S, Nat.Prime p) → Squarefree (∏ p ∈ S, p) := by
            intros S hS_prime; induction S using Finset.induction <;> simp_all +decide [ Nat.squarefree_mul_iff ] ;
            exact ⟨ Nat.Coprime.prod_right fun q hq => hS_prime.1.coprime_iff_not_dvd.mpr fun hq' => by have := Nat.prime_dvd_prime_iff_eq hS_prime.1 ( hS_prime.2 q hq ) ; aesop, hS_prime.1.squarefree ⟩;
          exact h_prod_squarefree fun q hq => hS_prime q <| Finset.mem_insert_of_mem hq;
        · exact Nat.Coprime.prod_right fun q hq => by have := Nat.coprime_primes ( hS_prime p ( Finset.mem_insert_self p S ) ) ( hS_prime q ( Finset.mem_insert_of_mem hq ) ) ; aesop;
    rw [ ← h_base ( fun p hp => hd_primes p hp |>.1 ) ( fun p hp => hd_primes p hp |>.2.1 ), Nat.prod_primeFactors_of_squarefree hd ]
  have h_perturbed : P.perturbed.f d = ∏ p ∈ d.primeFactors, P.perturbed.f p := by
    have h_perturbed : ∀ {S : Finset ℕ}, (∀ p ∈ S, Nat.Prime p ∧ P.perturbed.sievingPrime p ∧ p ≤ P.perturbed.z) → P.perturbed.f (∏ p ∈ S, p) = ∏ p ∈ S, P.perturbed.f p := by
      intros S hS; induction' S using Finset.induction with p S hS ih; simp_all +decide [ Finset.prod_insert, Nat.Prime.ne_zero ] ;
      · exact P.perturbed.hf_one;
      · rw [ Finset.prod_insert ‹p ∉ S›, P.perturbed.hf_mult ];
        · rw [ Finset.prod_insert ‹p ∉ S›, ih fun q hq => hS q <| Finset.mem_insert_of_mem hq ];
        · exact Nat.prime_iff.mp ( hS p ( Finset.mem_insert_self _ _ ) |>.1 ) |> fun h => h.squarefree;
        · have h_squarefree : ∀ {S : Finset ℕ}, (∀ p ∈ S, Nat.Prime p) → Squarefree (∏ p ∈ S, p) := by
            intros S hS; induction S using Finset.induction <;> simp_all +decide [ Nat.squarefree_mul_iff ] ;
            exact ⟨ Nat.Coprime.prod_right fun q hq => hS.1.coprime_iff_not_dvd.mpr fun hq' => by have := Nat.prime_dvd_prime_iff_eq hS.1 ( hS.2 q hq ) ; aesop, hS.1.squarefree ⟩;
          exact h_squarefree fun q hq => hS q ( Finset.mem_insert_of_mem hq ) |>.1;
        · exact Nat.Coprime.prod_right fun q hq => by have := Nat.coprime_primes ( hS p ( Finset.mem_insert_self _ _ ) |>.1 ) ( hS q ( Finset.mem_insert_of_mem hq ) |>.1 ) ; aesop;
    convert h_perturbed _;
    · rw [ Nat.prod_primeFactors_of_squarefree hd ];
    · have := P.same_sievingPrime; have := P.same_z; aesop;
  refine' h_contra ( h_base.symm ▸ h_perturbed.symm ▸ _ );
  convert finset_prod_perturb ( fun p => P.base.f p ) ( fun p => P.perturbed.f p ) ( d.primeFactors ) P.primeError M P.primeError_nonneg hM ( fun p hp => hfM p ( hd_primes p hp |>.1 ) ( hd_primes p hp |>.2.1 ) ( hd_primes p hp |>.2.2 ) ) ( fun p hp => hgM p ( hd_primes p hp |>.1 ) ( hd_primes p hp |>.2.1 ) ( hd_primes p hp |>.2.2 ) ) ( fun p hp => P.hperturb p ( hd_primes p hp |>.1 ) ( hd_primes p hp |>.2.1 ) ( hd_primes p hp |>.2.2 ) ) using 1

/-! ## Phase 4: Euler Product Stability -/

/-- The reciprocal sum (partial Euler product) for a sieve. -/
def recipSum (sd : SieveData) (D : Finset ℕ) : ℝ :=
  ∑ d ∈ D, 1 / sd.f d

/-
Euler product stability: the reciprocal sums of two perturbed sieves
    are close, controlled by the prime-level perturbation.
-/
theorem eulerProduct_stability (P : SievePerturbation)
    (M : ℝ) (hM : 0 ≤ M)
    (hfM : ∀ p : ℕ, p.Prime → P.base.sievingPrime p → p ≤ P.base.z → |P.base.f p| ≤ M)
    (hgM : ∀ p : ℕ, p.Prime → P.base.sievingPrime p → p ≤ P.base.z → |P.perturbed.f p| ≤ M)
    (D : Finset ℕ)
    (hD : ∀ d ∈ D, Squarefree d)
    (hD_primes : ∀ d ∈ D, ∀ p ∈ d.primeFactors, p.Prime ∧ P.base.sievingPrime p ∧ p ≤ P.base.z)
    (hfg_lower : ∀ d ∈ D, 0 < P.base.f d ∧ 0 < P.perturbed.f d) :
    |recipSum P.base D - recipSum P.perturbed D| ≤
      ∑ d ∈ D, P.primeError * d.primeFactors.card * M ^ (d.primeFactors.card - 1) /
        (P.base.f d * P.perturbed.f d) := by
  have h_kinetic : ∀ d ∈ D, |1 / P.base.f d - 1 / P.perturbed.f d| ≤ (P.primeError * d.primeFactors.card * M^(d.primeFactors.card - 1)) / (P.base.f d * P.perturbed.f d) := by
    intro d hd; rw [ div_sub_div ] <;> try linarith [ hfg_lower d hd ] ;
    rw [ abs_div, abs_of_nonneg ( mul_nonneg ( le_of_lt ( hfg_lower d hd |>.1 ) ) ( le_of_lt ( hfg_lower d hd |>.2 ) ) ) ] ; gcongr ; ring_nf ;
    · nlinarith [ hfg_lower d hd ];
    · convert perturbation_propagates P M hM hfM hgM d ( hD d hd ) ( hD_primes d hd ) using 1
      · rfl
      · rw [ one_mul, mul_one, abs_sub_comm ]
  exact le_trans ( by rw [ recipSum, recipSum ] ; rw [ ← Finset.sum_sub_distrib ] ) ( Finset.abs_sum_le_sum_abs _ _ |> le_trans <| Finset.sum_le_sum h_kinetic )

/-! ## Phase 5: H-functional and Stability -/

/-- The arithmetic H-functional, the direct analogue of Boltzmann's H = ∫ f log f.
    Sums f(d)/d · log(f(d)/d) over squarefree divisors. -/
def sieveHFunctional (sd : SieveData) (D : Finset ℕ) : ℝ :=
  ∑ d ∈ D, (sd.f d / d) * Real.log (sd.f d / d)

/-
For positive reals, |a·log(a) - b·log(b)| ≤ (1 + |log(a)| + |log(b)|) · |a - b|.
    This follows from the mean value theorem on h(x) = x·log(x) with h'(x) = 1 + log(x).
-/
lemma xlogx_lipschitz (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    |a * Real.log a - b * Real.log b| ≤ (1 + |Real.log a| + |Real.log b|) * |a - b| := by
  -- By the mean value theorem, there exists some $c$ between $a$ and $b$ such that $f(a) - f(b) = f'(c)(a - b)$.
  have h_mean_value : ∀ {a b : ℝ}, 0 < a → 0 < b → a ≠ b → ∃ c ∈ Set.Ioo (min a b) (max a b), a * Real.log a - b * Real.log b = (1 + Real.log c) * (a - b) := by
    intros a b ha hb hab;
    cases' lt_or_gt_of_ne hab with h h <;> have := exists_deriv_eq_slope ( f := fun x => x * Real.log x ) h <;> simp_all +decide [ mul_comm ];
    · exact this ( ContinuousOn.mul continuousOn_id <| ContinuousOn.log continuousOn_id <| by intro x hx; linarith [ hx.1 ] ) ( DifferentiableOn.mul differentiableOn_id <| DifferentiableOn.log differentiableOn_id <| by intro x hx; linarith [ hx.1 ] ) |> fun ⟨ c, hc₁, hc₂ ⟩ => ⟨ c, ⟨ Or.inl hc₁.1, Or.inr hc₁.2 ⟩, by norm_num [ show c ≠ 0 by linarith ] at hc₂; rw [ eq_div_iff ] at hc₂ <;> linarith ⟩;
    · exact this ( ContinuousOn.mul continuousOn_id <| ContinuousOn.log continuousOn_id <| by intro x hx; linarith [ hx.1 ] ) ( DifferentiableOn.mul differentiableOn_id <| DifferentiableOn.log differentiableOn_id <| by intro x hx; linarith [ hx.1 ] ) |> fun ⟨ c, hc₁, hc₂ ⟩ => ⟨ c, ⟨ Or.inr hc₁.1, Or.inl hc₁.2 ⟩, by rw [ eq_div_iff ] at hc₂ <;> norm_num [ show c ≠ 0 by linarith ] at * <;> linarith ⟩;
  by_cases hab : a = b <;> simp_all +decide [ abs_mul ];
  obtain ⟨ c, hc₁, hc₂ ⟩ := h_mean_value ha hb hab ; rw [ hc₂, abs_mul ] ; gcongr;
  cases hc₁.1 <;> cases hc₁.2 <;> first | linarith | simp_all +decide [ abs_le ];
  · constructor <;> cases abs_cases ( Real.log a ) <;> cases abs_cases ( Real.log b ) <;> linarith [ Real.log_le_log ( by linarith ) ( by linarith : a ≤ c ), Real.log_le_log ( by linarith ) ( by linarith : c ≤ b ) ];
  · constructor <;> cases abs_cases ( Real.log a ) <;> cases abs_cases ( Real.log b ) <;> linarith [ Real.log_le_log ( by linarith ) ( by linarith : b ≤ c ), Real.log_le_log ( by linarith ) ( by linarith : c ≤ a ) ]

/-
The H-functional is stable under perturbation: if f and g agree at primes
    to within ε, then their H-functionals differ by a controlled amount.
-/
theorem sieveH_stable (P : SievePerturbation)
    (M : ℝ) (hM : 0 < M)
    (hfM : ∀ p : ℕ, p.Prime → P.base.sievingPrime p → p ≤ P.base.z → |P.base.f p| ≤ M)
    (hgM : ∀ p : ℕ, p.Prime → P.base.sievingPrime p → p ≤ P.base.z → |P.perturbed.f p| ≤ M)
    (D : Finset ℕ)
    (hD : ∀ d ∈ D, Squarefree d)
    (hD_primes : ∀ d ∈ D, ∀ p ∈ d.primeFactors, p.Prime ∧ P.base.sievingPrime p ∧ p ≤ P.base.z)
    (hfg_lower : ∀ d ∈ D, 0 < P.base.f d ∧ 0 < P.perturbed.f d)
    (C : ℝ) (hC : C = ∑ d ∈ D,
      (1 + |Real.log (P.base.f d / d)| + |Real.log (P.perturbed.f d / d)|) *
      (d.primeFactors.card * M ^ (d.primeFactors.card - 1) / (d : ℝ))) :
    |sieveHFunctional P.base D - sieveHFunctional P.perturbed D| ≤
      P.primeError * C := by
  rw [ hC, mul_comm, Finset.sum_mul ];
  refine' le_trans _ ( Finset.sum_le_sum _ );
  rotate_left;
  use fun d => |(P.base.f d / d) * Real.log (P.base.f d / d) - (P.perturbed.f d / d) * Real.log (P.perturbed.f d / d)|;
  · intro d hd;
    refine' le_trans ( xlogx_lipschitz _ _ _ _ ) _;
    · exact div_pos ( hfg_lower d hd |>.1 ) ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by specialize hD d hd; aesop ) ) );
    · exact div_pos ( hfg_lower d hd |>.2 ) ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by specialize hD d hd; aesop ) ) );
    · rw [ mul_assoc ];
      gcongr;
      convert mul_le_mul_of_nonneg_right ( perturbation_propagates P M hM.le hfM hgM d ( hD d hd ) ( hD_primes d hd ) ) ( inv_nonneg.mpr ( Nat.cast_nonneg d ) ) using 1 ; ring_nf;
      · rw [ show P.base.f d * ( d : ℝ ) ⁻¹ - ( d : ℝ ) ⁻¹ * P.perturbed.f d = ( d : ℝ ) ⁻¹ * ( P.base.f d - P.perturbed.f d ) by ring, abs_mul, abs_of_nonneg ( by positivity ) ];
      · ring;
  · exact le_trans ( by rw [ sieveHFunctional, sieveHFunctional, ← Finset.sum_sub_distrib ] ) ( Finset.abs_sum_le_sum_abs _ _ )

end
