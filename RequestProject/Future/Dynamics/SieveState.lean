/-
# Dynamics.SieveState

Closed admissible subsets, factors, and arithmetic observables.

Status: ProvedInProject (definitions and basic properties)
-/
import Mathlib

open Finset BigOperators MeasureTheory

noncomputable section

structure AdmissibleSet (m : ℕ) [NeZero m] where
  residues : Finset (ZMod m)
  nonempty : residues.Nonempty

namespace AdmissibleSet
variable {m : ℕ} [NeZero m]

def density (A : AdmissibleSet m) : ℝ := (A.residues.card : ℝ) / (m : ℝ)

lemma density_pos (A : AdmissibleSet m) : 0 < A.density := by
  apply div_pos
  · exact Nat.cast_pos.mpr A.nonempty.card_pos
  · exact Nat.cast_pos.mpr (NeZero.pos m)

lemma density_le_one (A : AdmissibleSet m) : A.density ≤ 1 := by
  refine' div_le_one_of_le₀ _ _;
  · norm_cast;
    exact le_trans ( Finset.card_le_univ _ ) ( by norm_num );
  · positivity

def complement (A : AdmissibleSet m) (hne : (Finset.univ \ A.residues).Nonempty) :
    AdmissibleSet m where
  residues := Finset.univ \ A.residues
  nonempty := hne

lemma complement_density (A : AdmissibleSet m) (hne : (Finset.univ \ A.residues).Nonempty) :
    A.density + (A.complement hne).density = 1 := by
  unfold AdmissibleSet.density
  have h_card : (A.residues.card : ℝ) + ((Finset.univ : Finset (ZMod m)) \ A.residues).card = m := by
    rw_mod_cast [ Finset.card_sdiff ] ; simp +decide [ Finset.card_univ ];
    exact Nat.add_sub_of_le ( le_trans ( Finset.card_le_univ _ ) ( by simp +decide ) )
  simp [h_card] at *;
  rw [ ← add_div, div_eq_iff ] <;> norm_cast <;> simp_all +decide ;
  · show A.residues.card + (Finset.univ \ A.residues).card = m
    rw [add_comm, Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _), Finset.card_univ,
      ZMod.card]
  · exact NeZero.ne m

end AdmissibleSet

structure SieveState where
  admissibleAt : (m : ℕ) → [NeZero m] → Finset (ZMod m)
  nonempty : ∀ (m : ℕ) [NeZero m], (admissibleAt m).Nonempty
  compatible : ∀ (m n : ℕ) [NeZero m] [NeZero n] [NeZero (m * n)]
    (x : ZMod (m * n)),
    x ∈ admissibleAt (m * n) →
    ZMod.castHom (dvd_mul_right m n) (ZMod m) x ∈ admissibleAt m

namespace SieveState
variable (S : SieveState)

def densityAt (m : ℕ) [NeZero m] : ℝ := ((S.admissibleAt m).card : ℝ) / (m : ℝ)

lemma densityAt_pos (m : ℕ) [NeZero m] : 0 < S.densityAt m := by
  apply div_pos
  · exact Nat.cast_pos.mpr (S.nonempty m).card_pos
  · exact Nat.cast_pos.mpr (NeZero.pos m)

def localDensityFactor (m : ℕ) [NeZero m] : ℝ := (m : ℝ) / ((S.admissibleAt m).card : ℝ)

lemma localDensityFactor_pos (m : ℕ) [NeZero m] : 0 < S.localDensityFactor m := by
  apply div_pos
  · exact Nat.cast_pos.mpr (NeZero.pos m)
  · exact Nat.cast_pos.mpr (S.nonempty m).card_pos

end SieveState

def shiftAction' (m : ℕ) [NeZero m] (s : ZMod m) : ZMod m → ZMod m := fun x => x + s

lemma shiftAction'_bijective (m : ℕ) [NeZero m] (s : ZMod m) :
    Function.Bijective (shiftAction' m s) := by
  constructor
  · intro a b h; simp [shiftAction'] at h; exact h
  · intro b; exact ⟨b - s, by simp [shiftAction']⟩

def isShiftInvariant' {m : ℕ} [NeZero m] (A : Finset (ZMod m)) : Prop :=
  ∀ s : ZMod m, A.image (shiftAction' m s) = A

lemma shift_invariant_full {m : ℕ} [NeZero m] (A : Finset (ZMod m))
    (hne : A.Nonempty) (hinv : isShiftInvariant' A) :
    A = Finset.univ := by
      -- Let's choose any element a ∈ A (exists by hne).
      obtain ⟨a, ha⟩ : ∃ a, a ∈ A := hne;
      apply le_antisymm;
      · exact Finset.subset_univ _;
      · intro b hb; specialize hinv ( b - a ) ; simp_all +decide [ Finset.ext_iff ] ;
        exact hinv _ |>.1 ⟨ a, ha, by unfold shiftAction'; ring ⟩

end