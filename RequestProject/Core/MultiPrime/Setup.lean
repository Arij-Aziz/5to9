/-
# Sieve.MultiPrime.Setup

Multi-prime sieve setting: squarefree divisors,
the multi-prime Selberg majorant, and domination.

## Main definitions

* `sqfDivisors` — squarefree divisors of a natural number
* `selbergNu` — the multi-prime Selberg majorant ν(x) = (Σ_{d | gcd(x,P)} λ_d)²
* `sieveIndicator` — the sieve indicator 1_{gcd(x,P)=1}

## Main results

* `selbergNu_nonneg` — the majorant is nonneg (it's a square)
* `selbergNu_dominates` — ν dominates the sieve indicator when λ₁ = 1

Status: ProvedInProject
-/
import Mathlib
import RequestProject.Core.Basic

open Finset BigOperators Nat

noncomputable section

/-- Squarefree divisors of P. Uses `squarefreeDivisors` from Basic.lean. -/
def sqfDivisors (P : ℕ) : Finset ℕ := squarefreeDivisors P

lemma mem_sqfDivisors {P d : ℕ} :
    d ∈ sqfDivisors P ↔ d ∣ P ∧ P ≠ 0 ∧ Squarefree d := by
  exact mem_squarefreeDivisors

lemma one_mem_sqfDivisors {P : ℕ} (hP : P ≠ 0) :
    1 ∈ sqfDivisors P := by
  exact one_mem_squarefreeDivisors hP

/-- The multi-prime Selberg majorant:
    ν(x) = (Σ_{d ∈ sqfDivisors P, d | gcd(x,P)} λ_d)² -/
def selbergNu (N P : ℕ) (lambda : ℕ → ℝ) (x : Fin N) : ℝ :=
  (∑ d ∈ (sqfDivisors P).filter (fun d => d ∣ Nat.gcd x.val P), lambda d) ^ 2

/-- The sieve indicator: 1 if gcd(x, P) = 1, else 0. -/
def sieveIndicator (N P : ℕ) (x : Fin N) : ℝ :=
  if Nat.Coprime x.val P then 1 else 0

lemma selbergNu_nonneg (N P : ℕ) (lambda : ℕ → ℝ) (x : Fin N) :
    0 ≤ selbergNu N P lambda x :=
  sq_nonneg _

lemma sieveIndicator_nonneg (N P : ℕ) (x : Fin N) :
    0 ≤ sieveIndicator N P x := by
  unfold sieveIndicator; split <;> norm_num

lemma sieveIndicator_indicator (N P : ℕ) (x : Fin N) :
    sieveIndicator N P x = 0 ∨ sieveIndicator N P x = 1 := by
  unfold sieveIndicator; split <;> simp

/-- When gcd(x,P) = 1, the only squarefree divisor of P dividing gcd(x,P) is 1. -/
lemma filter_sqfDivisors_coprime {P : ℕ} (hP : P ≠ 0) {x : ℕ} (hcop : Nat.Coprime x P) :
    (sqfDivisors P).filter (fun d => d ∣ Nat.gcd x P) = {1} := by
  ext d
  simp only [Finset.mem_filter, mem_sqfDivisors, Finset.mem_singleton]
  constructor
  · intro ⟨⟨hdP, _, _⟩, hdg⟩
    have : d ∣ 1 := by
      rw [Nat.Coprime] at hcop
      rw [hcop] at hdg
      exact hdg
    exact Nat.eq_one_of_dvd_one this
  · intro h
    subst h
    exact ⟨⟨one_dvd P, hP, squarefree_one⟩, one_dvd _⟩

/-- The multi-prime Selberg majorant dominates the sieve indicator when λ₁ = 1. -/
theorem selbergNu_dominates (N P : ℕ) (lambda : ℕ → ℝ)
    (hP : P ≠ 0)
    (hlambda_one : lambda 1 = 1) :
    ∀ x : Fin N, sieveIndicator N P x ≤ selbergNu N P lambda x := by
  intro x
  unfold sieveIndicator selbergNu
  split
  · rename_i hcop
    have hfilt : (sqfDivisors P).filter (fun d => d ∣ Nat.gcd x.val P) = {1} := by
      ext d; constructor
      · intro h
        rw [Finset.mem_filter] at h
        rcases h with ⟨hd_mem, hd_gcd⟩
        have hd_one : d = 1 := by
          have h_dvd_one : d ∣ 1 := by
            rw [← Nat.Coprime.gcd_eq_one hcop]
            exact hd_gcd
          exact Nat.eq_one_of_dvd_one h_dvd_one
        subst hd_one; simp
      · intro h
        rw [Finset.mem_singleton.mp h]
        refine Finset.mem_filter.mpr ⟨?_, ?_⟩
        · simp [sqfDivisors, squarefreeDivisors, hP]
        · simp
    rw [hfilt]; simp [hlambda_one]
  · exact sq_nonneg _

end
