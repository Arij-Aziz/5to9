/-
# Sieve.Weights.UpperBound

The fundamental upper bound inequality of the Selberg sieve.

We define the sieve weight w(n) = Σ_{d | gcd(n,P), d ∈ D} λ_d
and the quadratic sum Q_A(λ) = Σ_{n ∈ A} w(n)²,
then prove:
  1. |siftedSet| ≤ Q_A(λ) (the key majorization)
  2. Σ_d λ_d R_d ≤ Σ_d |λ_d| |R_d| (error bound)

Status: ProvedInProject
-/
import Mathlib
import RequestProject.Core.Basic

open Finset BigOperators Nat

noncomputable section

/-! ## The sieve weight -/

/-- The sieve weight at element n: the sum of λ_d over d ∈ D dividing gcd(n, P).
    This is the standard Selberg weight that counts the contribution of
    arithmetic progressions modulo primes dividing P. -/
def sieveWeight (lambda : ℕ → ℝ) (D : Finset ℕ) (n P : ℕ) : ℝ :=
  ∑ d ∈ D.filter (· ∣ Nat.gcd n P), lambda d

/-- The quadratic majorant sum: Σ_{n ∈ A} (sieveWeight λ D n P)². -/
def quadraticMajorantSum (lambda : ℕ → ℝ) (D : Finset ℕ) (A : Finset ℕ) (P : ℕ) : ℝ :=
  ∑ n ∈ A, (sieveWeight lambda D n P) ^ 2

/-- The quadratic majorant sum is nonneg (sum of squares). -/
lemma quadraticMajorantSum_nonneg (lambda : ℕ → ℝ) (D : Finset ℕ) (A : Finset ℕ) (P : ℕ) :
    0 ≤ quadraticMajorantSum lambda D A P :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-! ## Key lemma: coprime elements have weight = λ_1 -/

/-
For elements coprime to P, the sieve weight is exactly λ_1.
    If gcd(n, P) = 1, the only d dividing gcd(n, P) is 1.
    So the weight sum reduces to λ_1 (provided 1 ∈ D).
-/
lemma sieveWeight_coprime_eq (lambda : ℕ → ℝ) (D : Finset ℕ) (n P : ℕ)
    (hD : 1 ∈ D)
    (h_coprime : Nat.Coprime n P) :
    sieveWeight lambda D n P = lambda 1 := by
  unfold sieveWeight;
  rw [ Finset.sum_eq_single 1 ] <;> aesop

/-
**Selberg's key inequality**: the sifted set count is bounded by the
    quadratic majorant sum.

    For n in the sifted set (coprime to P), sieveWeight(n) = λ_1 = 1,
    so sieveWeight(n)² = 1. For all other n ∈ A, sieveWeight(n)² ≥ 0.
    Summing gives |siftedSet| ≤ Q_A(λ).
-/
theorem siftedSet_card_le_quadraticSum
    (S : SieveData) (lambda : ℕ → ℝ) (D : Finset ℕ)
    (hlambda_one : lambda 1 = 1)
    (hD : 1 ∈ D) :
    (S.siftedSet.card : ℝ) ≤ quadraticMajorantSum lambda D S.A S.P := by
  -- For n in the sifted set (coprime to P), sieveWeight(n) = lambda 1 = 1, so sieveWeight(n)² = 1.
  have h_sifted : ∀ n ∈ S.siftedSet, (sieveWeight lambda D n S.P) ^ 2 = 1 := by
    intro n hn; rw [ sieveWeight_coprime_eq _ _ _ _ hD ( Finset.mem_filter.mp hn |>.2 ) ] ; aesop;
  rw [quadraticMajorantSum]
  calc (S.siftedSet.card : ℝ)
      = ∑ n ∈ S.siftedSet, (sieveWeight lambda D n S.P) ^ 2 := by
        rw [Finset.sum_congr rfl h_sifted]; simp
    _ ≤ ∑ n ∈ S.A, (sieveWeight lambda D n S.P) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => sq_nonneg _)

/-! ## Error separation -/

/-- Bound on a linear weighted sum using absolute values:
    Σ_d λ_d · R_d ≤ Σ_d |λ_d| · |R_d| -/
theorem weighted_remainder_bound (lambda remainder : ℕ → ℝ) (D : Finset ℕ) :
    ∑ d ∈ D, lambda d * remainder d ≤ ∑ d ∈ D, |lambda d| * |remainder d| := by
  exact Finset.sum_le_sum fun i _ => by rw [← abs_mul]; exact le_abs_self _

end