/-
# Models.CyclicToy

Finite cyclic toy models for rapid testing of sieve-state concepts.

Status: ProvedInProject (definitions and basic verified properties)
-/
import Mathlib

open Finset BigOperators

noncomputable section

structure CyclicSieve (N : ℕ) [NeZero N] where
  primes : Finset ℕ
  hprimes : ∀ p ∈ primes, Nat.Prime p
  hprimes_dvd : ∀ p ∈ primes, p ∣ N
  removedResidue : (p : ℕ) → p ∈ primes → ZMod p

namespace CyclicSieve
variable {N : ℕ} [NeZero N] (S : CyclicSieve N)

def survives (x : ZMod N) : Prop :=
  ∀ p (hp : p ∈ S.primes),
    ZMod.castHom (S.hprimes_dvd p hp) (ZMod p) x ≠ S.removedResidue p hp

instance decidableSurvives (x : ZMod N) : Decidable (S.survives x) :=
  inferInstanceAs (Decidable (∀ p (hp : p ∈ S.primes), _))

def siftedSet : Finset (ZMod N) := Finset.univ.filter (fun x => S.survives x)
def siftedCount : ℕ := S.siftedSet.card

def expectedDensity : ℝ := ∏ p ∈ S.primes, (1 - (1 : ℝ) / p)

lemma expectedDensity_pos : 0 < S.expectedDensity := by
  apply Finset.prod_pos
  intro p hp
  have hprime := S.hprimes p hp
  have : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero hprime.ne_zero
  have : (1 : ℝ) / p < 1 := by rw [div_lt_one ‹_›]; exact_mod_cast hprime.two_le
  linarith

lemma trivialMajorant_dominates (x : ZMod N) :
    (if S.survives x then (1 : ℝ) else 0) ≤ (1 : ℝ) := by
  split_ifs <;> norm_num

end CyclicSieve

def eratosthenesCount (N z : ℕ) : ℕ :=
  ((Finset.range N).filter (fun n =>
    ∀ p ∈ (Finset.range (z + 1)).filter Nat.Prime, ¬(p ∣ (n + 1)))).card

end
