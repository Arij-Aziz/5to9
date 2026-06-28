/-
# Sieve.MajorantComparison

Concrete benchmark comparison: constructs an explicit pair of majorants
(classical = constant, improved = indicator) and proves mass improvement.

-- Sanity check / toy benchmark. This is NOT the main result.
-- See Core/SelbergComparison.lean for the main theorem.

Status: ProvedInProject
-/
import Mathlib
import RequestProject.Core.Majorant

open Finset BigOperators

noncomputable section

/-! ## The indicator function of a finset -/

/-- The indicator function of a finset S ⊆ Fin N, as a real-valued function -/
def finsetIndicator (N : ℕ) (S : Finset (Fin N)) : Fin N → ℝ :=
  fun x => if x ∈ S then 1 else 0

lemma finsetIndicator_nonneg (N : ℕ) (S : Finset (Fin N)) :
    ∀ x, 0 ≤ finsetIndicator N S x := by
  intro x; unfold finsetIndicator; split <;> norm_num

lemma finsetIndicator_ind (N : ℕ) (S : Finset (Fin N)) :
    ∀ x, finsetIndicator N S x = 0 ∨ finsetIndicator N S x = 1 := by
  intro x; unfold finsetIndicator; split <;> simp

/-- Sum of the indicator equals the cardinality of S -/
lemma finsetIndicator_sum (N : ℕ) (S : Finset (Fin N)) :
    ∑ x : Fin N, finsetIndicator N S x = S.card := by
  unfold finsetIndicator
  simp only [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]

/-! ## Constant (classical) majorant -/

/-- The constant majorant: ν(x) = 1 for all x.
    This trivially dominates any {0,1}-valued target. -/
def constantMajorant (N : ℕ) (target : Fin N → ℝ)
    (htarget_nonneg : ∀ x, 0 ≤ target x)
    (htarget_ind : ∀ x, target x = 0 ∨ target x = 1) : Majorant N where
  nu := fun _ => 1
  target := target
  nu_nonneg := fun _ => by norm_num
  target_nonneg := htarget_nonneg
  target_indicator := htarget_ind
  domination := fun x => by
    cases htarget_ind x with
    | inl h => linarith
    | inr h => linarith

/-- The indicator majorant: ν = target itself.
    This is the tightest possible majorant for an indicator function. -/
def indicatorMajorant (N : ℕ) (target : Fin N → ℝ)
    (htarget_nonneg : ∀ x, 0 ≤ target x)
    (htarget_ind : ∀ x, target x = 0 ∨ target x = 1) : Majorant N where
  nu := target
  target := target
  nu_nonneg := htarget_nonneg
  target_nonneg := htarget_nonneg
  target_indicator := htarget_ind
  domination := fun _ => le_refl _

/-! ## Mass computations -/

/-- Mass of the constant majorant is N -/
lemma constantMajorant_mass (N : ℕ) (target : Fin N → ℝ)
    (hn : ∀ x, 0 ≤ target x)
    (hi : ∀ x, target x = 0 ∨ target x = 1) :
    (constantMajorant N target hn hi).mass = N := by
  simp [Majorant.mass, constantMajorant]

/-- Mass of the indicator majorant equals the target mass -/
lemma indicatorMajorant_mass_eq_targetMass (N : ℕ) (target : Fin N → ℝ)
    (hn : ∀ x, 0 ≤ target x)
    (hi : ∀ x, target x = 0 ∨ target x = 1) :
    (indicatorMajorant N target hn hi).mass =
    (indicatorMajorant N target hn hi).targetMass := by
  simp [Majorant.mass, Majorant.targetMass, indicatorMajorant]

/-! ## The toy benchmark comparison -/

/-- The toy benchmark comparison: constant majorant vs indicator majorant.
    Both use the same target (the finset indicator). -/
def toyComparison (N : ℕ) (S : Finset (Fin N)) : MajorantComparison N :=
  { classical := constantMajorant N (finsetIndicator N S)
      (finsetIndicator_nonneg N S) (finsetIndicator_ind N S)
    improved := indicatorMajorant N (finsetIndicator N S)
      (finsetIndicator_nonneg N S) (finsetIndicator_ind N S)
    same_target := rfl }

/-
**Main theorem**: For any proper subset S ⊊ Fin N,
    the indicator majorant has strictly smaller mass than the constant majorant.
    This is the simplest instance of a verified mass improvement.
-/
theorem toyComparison_massImprovement (N : ℕ) (S : Finset (Fin N))
    (hS_proper : S.card < N) :
    (toyComparison N S).massImprovement := by
  -- First, unroll all the definitions of the toy comparison: massImprovement, toyComparison,
  -- and the masses of the constant and indicator majorants.
  -- This should reduce the goal to a simple inequality about S.card and N.
  unfold MajorantComparison.massImprovement toyComparison constantMajorant indicatorMajorant Majorant.mass
  simp [Finset.sum_const, nsmul_one, Finset.card_fin, Nat.cast_lt] at *;
  exact_mod_cast finsetIndicator_sum N S |> fun h => h.trans_lt ( Nat.cast_lt.mpr hS_proper )

/-- Existence form: there exists a majorant comparison with mass improvement -/
theorem exists_mass_improvement (N : ℕ)
    (S : Finset (Fin N)) (hS_proper : S.card < N) :
    ∃ C : MajorantComparison N, C.massImprovement :=
  ⟨toyComparison N S, toyComparison_massImprovement N S hS_proper⟩

end
