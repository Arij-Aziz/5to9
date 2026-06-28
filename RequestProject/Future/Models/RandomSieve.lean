/-
# Models.RandomSieve

Random or independently deleted residue-class models for testing
sieve-state architecture.

Status: ProvedInProject (definitions and deterministic properties)
-/
import Mathlib

open Finset BigOperators

noncomputable section

structure RandomSieveModel where
  moduli : Finset ℕ
  hprime : ∀ m ∈ moduli, Nat.Prime m
  deletionProb : ℕ → ℝ
  hprob_nonneg : ∀ m ∈ moduli, 0 ≤ deletionProb m
  hprob_lt_one : ∀ m ∈ moduli, deletionProb m < 1

namespace RandomSieveModel

variable (R : RandomSieveModel)

def survivalProb : ℝ :=
  ∏ p ∈ R.moduli, (1 - R.deletionProb p)

lemma survivalProb_pos : 0 < R.survivalProb := by
  apply Finset.prod_pos
  intro p hp
  linarith [R.hprob_lt_one p hp]

lemma survivalProb_le_one : R.survivalProb ≤ 1 := by
  apply Finset.prod_le_one
  · intro p hp; linarith [R.hprob_lt_one p hp]
  · intro p hp; linarith [R.hprob_nonneg p hp]

def standard (primes : Finset ℕ) (hprime : ∀ p ∈ primes, Nat.Prime p) :
    RandomSieveModel where
  moduli := primes
  hprime := hprime
  deletionProb p := 1 / p
  hprob_nonneg p _ := by positivity
  hprob_lt_one p hp := by
    have h2 := (hprime p hp).two_le
    have hp_pos : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (Nat.Prime.ne_zero (hprime p hp))
    rw [div_lt_one hp_pos]
    exact_mod_cast h2

lemma standard_survivalProb (primes : Finset ℕ) (hprime : ∀ p ∈ primes, Nat.Prime p) :
    (standard primes hprime).survivalProb = ∏ p ∈ primes, (1 - 1 / (p : ℝ)) := by
  simp [survivalProb, standard]

def expectedVariance (N : ℕ) : ℝ :=
  N * R.survivalProb * (1 - R.survivalProb)

lemma expectedVariance_nonneg (N : ℕ) : 0 ≤ R.expectedVariance N := by
  apply mul_nonneg
  · apply mul_nonneg (Nat.cast_nonneg _) (le_of_lt R.survivalProb_pos)
  · linarith [R.survivalProb_le_one]

end RandomSieveModel

end
