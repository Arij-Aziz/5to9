/-
# Sieve.Weights.Bounds

Explicit usable bounds from tractable or suboptimal weights.

Status: ProvedInProject (basic bounds)
-/
import Mathlib

open Finset BigOperators

noncomputable section

structure LegendreWeights where
  z : ℕ
  primes : Finset ℕ
  hprimes : ∀ p ∈ primes, Nat.Prime p
  hprimes_bound : ∀ p ∈ primes, p < z

namespace LegendreWeights
variable (L : LegendreWeights)

def primorial : ℕ := ∏ p ∈ L.primes, p

def eulerProductDensity : ℝ := ∏ p ∈ L.primes, (1 - (1 : ℝ) / p)

lemma eulerProductDensity_pos : 0 < L.eulerProductDensity := by
  apply Finset.prod_pos
  intro p hp
  have hprime := L.hprimes p hp
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero hprime.ne_zero
  have h1p : (1 : ℝ) / p < 1 := by rw [div_lt_one hp_pos]; exact_mod_cast hprime.two_le
  linarith

lemma eulerProductDensity_le_one : L.eulerProductDensity ≤ 1 := by
  apply Finset.prod_le_one
  · intro p hp
    have hp_pos : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (L.hprimes p hp).ne_zero
    have h1p : (1 : ℝ) / p < 1 := by rw [div_lt_one hp_pos]; exact_mod_cast (L.hprimes p hp).two_le
    linarith
  · intro p hp
    have hp_pos : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (L.hprimes p hp).ne_zero
    linarith [show (0 : ℝ) < 1 / p from div_pos one_pos hp_pos]

end LegendreWeights

theorem cauchy_schwarz_sieve_bound (s : Finset ℕ) (a : ℕ → ℝ) :
    (∑ n ∈ s, a n) ^ 2 ≤ s.card * (∑ n ∈ s, a n ^ 2) := by
  have := Finset.sum_le_sum fun i ( hi : i ∈ s ) => mul_self_nonneg ( a i - ( ∑ i ∈ s, a i ) / s.card );
  by_cases hs : s = ∅ <;> simp_all +decide [ sub_mul, mul_sub ];
  case _ => simp_all +decide [ ← sq, ← Finset.mul_sum _ _ _, ← Finset.sum_mul ] ; nlinarith [ mul_div_cancel₀ ( ∑ i ∈ s, a i ) ( Nat.cast_ne_zero.mpr <| Finset.card_ne_zero_of_mem <| Classical.choose_spec <| Finset.nonempty_of_ne_empty hs ) ] ;

end