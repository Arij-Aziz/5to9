/-
# Sieve.Basic

Classical sieve infrastructure: sifted sets, divisor filters, squarefree support,
local densities, and remainder decomposition.

Status: ProvedInProject (definitions and basic API)
-/
import Mathlib

open Finset BigOperators Nat

noncomputable section

def squarefreeDivisors (n : ℕ) : Finset ℕ :=
  (Nat.divisors n).filter Squarefree

lemma squarefreeDivisors_subset_divisors (n : ℕ) :
    squarefreeDivisors n ⊆ Nat.divisors n :=
  Finset.filter_subset _ _

lemma mem_squarefreeDivisors {n d : ℕ} :
    d ∈ squarefreeDivisors n ↔ d ∣ n ∧ n ≠ 0 ∧ Squarefree d := by
  simp [squarefreeDivisors, Nat.mem_divisors]; tauto

lemma one_mem_squarefreeDivisors {n : ℕ} (hn : n ≠ 0) :
    1 ∈ squarefreeDivisors n := by
  rw [mem_squarefreeDivisors]; exact ⟨one_dvd n, hn, squarefree_one⟩

structure SieveData where
  A : Finset ℕ
  sievingPrime : ℕ → Prop
  sievingPrimeDec : DecidablePred sievingPrime
  z : ℕ
  X : ℝ
  f : ℕ → ℝ
  hf_one : f 1 = 1
  hf_mult : ∀ d e : ℕ, Squarefree d → Squarefree e → Nat.Coprime d e →
    f (d * e) = f d * f e
  hf_pos : ∀ p, sievingPrime p → 0 < f p
  hX_pos : X > 0

attribute [instance] SieveData.sievingPrimeDec

namespace SieveData
variable (S : SieveData)

def P : ℕ := ∏ p ∈ (Finset.range S.z).filter (fun p => Nat.Prime p ∧ S.sievingPrime p), p
def Ad (d : ℕ) : Finset ℕ := S.A.filter (fun a => d ∣ a)
def siftedSet : Finset ℕ := S.A.filter (fun a => Nat.Coprime a S.P)
def remainder (d : ℕ) : ℝ := (S.Ad d).card - S.X / S.f d

theorem local_density_decomp (d : ℕ) :
    ((S.Ad d).card : ℝ) = S.X / S.f d + S.remainder d := by
  simp [remainder]

lemma Ad_subset (d : ℕ) : S.Ad d ⊆ S.A := Finset.filter_subset _ _

lemma Ad_mono {d e : ℕ} (h : d ∣ e) : S.Ad e ⊆ S.Ad d := by
  intro x hx; simp only [Ad, Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, dvd_trans h hx.2⟩

lemma Ad_card_le (d : ℕ) : (S.Ad d).card ≤ S.A.card := Finset.card_le_card (S.Ad_subset d)

end SieveData

structure UpperBoundSieve extends SieveData where
  lambda : ℕ → ℝ
  hlambda_one : lambda 1 = 1
  hlambda_support : ∀ d, ¬Squarefree d → lambda d = 0

namespace UpperBoundSieve
variable (U : UpperBoundSieve)

def selbergQuadForm (D : Finset ℕ) : ℝ :=
  ∑ d ∈ D, ∑ e ∈ D, U.lambda d * U.lambda e / U.f (Nat.lcm d e)

def mainSum (D : Finset ℕ) : ℝ := ∑ d ∈ D, U.lambda d * (U.Ad d).card
def mainTerm (D : Finset ℕ) : ℝ := U.X * U.selbergQuadForm D
def errorTerm (D : Finset ℕ) : ℝ := ∑ d ∈ D, |U.lambda d| * |U.remainder d|

end UpperBoundSieve

end
