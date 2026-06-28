/-
# Dynamics.ProfiniteState

Profinite ambient space for sieve theory.

Status: ProvedInProject (definitions and basic properties)
-/
import Mathlib

open MeasureTheory Finset BigOperators

noncomputable section

def levelProjection (m n : ℕ) [NeZero m] [NeZero n] [NeZero (m * n)]
    (x : ZMod (m * n)) : ZMod m :=
  ZMod.castHom (dvd_mul_right m n) (ZMod m) x

def cylinderSet' (m : ℕ) [NeZero m] (a : ZMod m) : Set (ZMod m) := {a}

structure CompatibleSystem where
  residueAt : (m : ℕ) → [NeZero m] → ZMod m
  compatible : ∀ (m n : ℕ) [NeZero m] [NeZero n] [NeZero (m * n)],
    ZMod.castHom (dvd_mul_right m n) (ZMod m) (residueAt (m * n)) = residueAt m

/-- Every integer defines a compatible system -/
def intToCompatibleSystem (a : ℤ) : CompatibleSystem where
  residueAt m := a
  compatible m n := by
    intro _ _ _
    show ZMod.castHom _ (ZMod m) (a : ZMod (m * n)) = (a : ZMod m)
    rw [map_intCast]

def Observable' (m : ℕ) [NeZero m] := ZMod m → ℝ

def observableAvg (m : ℕ) [NeZero m] (obs : Observable' m) : ℝ :=
  (∑ a : ZMod m, obs a) / m

def residueIndicator (m : ℕ) [NeZero m] (a : ZMod m) : Observable' m :=
  fun x => if x = a then 1 else 0

lemma residueIndicator_avg (m : ℕ) [hm : NeZero m] (a : ZMod m) :
    observableAvg m (residueIndicator m a) = 1 / m := by
  simp only [observableAvg, residueIndicator]
  congr 1
  rw [Finset.sum_ite_eq' Finset.univ a (fun _ => (1 : ℝ))]
  simp

def sieveIndicator (m : ℕ) [NeZero m] : Observable' m :=
  fun x => if Nat.Coprime (ZMod.val x) m then 1 else 0

end
