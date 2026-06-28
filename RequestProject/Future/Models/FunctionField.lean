/-
# Models.FunctionField

Function-field analogue of the sieve architecture:
polynomials over finite fields as the validation environment.

Status: ProvedInProject (definitions and basic properties)
-/
import Mathlib
import RequestProject.Future.Applications.FunctionFieldSieve

open Polynomial Finset BigOperators
open scoped Classical

noncomputable section

variable (q : ℕ) [Fact (Nat.Prime q)]

/-- The "integers" in the function-field model: polynomials over 𝔽_q. -/
abbrev FqPoly := Polynomial (ZMod q)

/-- The "norm" (size) of a polynomial: q^(deg f) -/
def polyNorm (f : FqPoly q) : ℕ :=
  if f = 0 then 0 else q ^ f.natDegree

/-- Irreducible polynomials: the analogue of primes. -/
def isIrreduciblePoly (f : FqPoly q) : Prop :=
  Irreducible f

/-- Function-field sieve data. -/
structure FunctionFieldSieveData where
  n : ℕ
  d : ℕ
  hd : d ≤ n

namespace FunctionFieldSieveData
variable (S : FunctionFieldSieveData)

/-- The "X" parameter: q^n (total number of monic polynomials of degree n) -/
def mainTermFF : ℕ := q ^ S.n

/-- The density function: f(P) = q^(deg P) for irreducible P -/
def densityFunction (P : FqPoly q) : ℝ :=
  if P = 0 then 1 else (q : ℝ) ^ P.natDegree

end FunctionFieldSieveData

/-- In the function-field setting, the analogue of the Riemann Hypothesis
    is a theorem (Weil). This structure records the key bound. -/
structure FunctionFieldRH where
  n : ℕ
  modPoly : FqPoly q
  characterSumBound : ℝ
  hbound : characterSumBound ≤ (modPoly.natDegree - 1 : ℝ) * (q : ℝ) ^ (n / 2 : ℝ)

/-! ## Function-field Selberg main term

The following mirrors the integer setting (`hFunction`, `V_function` from
`OptimalWeights.lean`) in the polynomial ring `𝔽_q[T]`.  All objects are
`noncomputable` and use classical decidability for the irreducibility
predicate. -/

/-- `polyNorm` cast to `ℝ` equals `q ^ natDegree` for nonzero `f`. -/
lemma polyNorm_cast (f : FqPoly q) (hf : f ≠ 0) :
    (polyNorm q f : ℝ) = (q : ℝ) ^ f.natDegree := by
  simp [polyNorm, hf]

/-- Function-field analogue of `hFunction`:
    `h_FF(f) = (1/q^{deg f}) / ∏_{P | f, P irred} (1 - q^{-deg P})`. -/
def hFunctionFF (f : FqPoly q) : ℝ :=
  if f = 0 then 0
  else (1 : ℝ) / (q : ℝ) ^ f.natDegree /
    ∏ P ∈ (UniqueFactorizationMonoid.normalizedFactors f).toFinset.filter Irreducible,
      (1 - (1 : ℝ) / (q : ℝ) ^ P.natDegree)

/-
`h_FF` is nonnegative.
-/
lemma hFunctionFF_nonneg (f : FqPoly q) : 0 ≤ hFunctionFF q f := by
  unfold hFunctionFF;
  split_ifs <;> [ positivity; exact div_nonneg ( by positivity ) ( Finset.prod_nonneg fun _ _ => sub_nonneg.2 <| div_le_self zero_le_one <| one_le_pow₀ <| mod_cast Nat.Prime.pos Fact.out ) ]

/-
`h_FF(1) = 1`.
-/
lemma hFunctionFF_one : hFunctionFF q 1 = 1 := by
  unfold hFunctionFF; aesop;

/-- Squarefree divisors of a polynomial: products over subsets of its
    (normalized) irreducible factors.  This is the function-field analogue of
    `sqfDivisors P`. -/
def sqfDivisorsFF (P_mod : FqPoly q) : Finset (FqPoly q) :=
  (UniqueFactorizationMonoid.normalizedFactors P_mod).toFinset.powerset.image
    (fun s => s.prod id)

/-
`1` is always a squarefree divisor (it is the product over the empty subset).
-/
lemma one_mem_sqfDivisorsFF (P_mod : FqPoly q) :
    (1 : FqPoly q) ∈ sqfDivisorsFF q P_mod := by
  exact Finset.mem_image.mpr ⟨ ∅, Finset.mem_powerset.mpr ( Finset.empty_subset _ ), by simp +decide ⟩

/-- Function-field analogue of `V_function`: the reciprocal Selberg main sum
    over squarefree divisors of `P_mod` of degree at most `d`. -/
def V_functionFF (P_mod : FqPoly q) (d : ℕ) : ℝ :=
  ∑ f ∈ sqfDivisorsFF q P_mod,
    if Squarefree f ∧ f.natDegree ≤ d then hFunctionFF q f else 0

/-
`V_FF(P_mod, d) ≥ 1`, since the term at `f = 1` contributes `1` and all
    terms are nonnegative.
-/
lemma V_functionFF_ge_one (P_mod : FqPoly q) (d : ℕ) :
    1 ≤ V_functionFF q P_mod d := by
  refine' le_trans _ ( Finset.single_le_sum ( fun x _ => _ ) ( one_mem_sqfDivisorsFF q P_mod ) ) <;> norm_num [ hFunctionFF_one ];
  split_ifs <;> [ exact hFunctionFF_nonneg q x; exact le_rfl ]

/-- `V_FF(P_mod, d) > 0`. -/
lemma V_functionFF_pos (P_mod : FqPoly q) (d : ℕ) :
    0 < V_functionFF q P_mod d :=
  lt_of_lt_of_le zero_lt_one (V_functionFF_ge_one q P_mod d)

/-
Conservative function-field Selberg main-term bound: the main-term ratio is
    at most the full count.  (The stronger `≤ q^n/V_FF + R` with `R → 0` by
    Weil belongs to the bridge file `FunctionFieldSieve.lean`.)
-/
theorem selbergFF_mass_eq (S : FunctionFieldSieveData) (P_mod : FqPoly q) :
    (S.mainTermFF q : ℝ) / V_functionFF q P_mod S.d ≤ (S.mainTermFF q : ℝ) := by
  exact div_le_self ( Nat.cast_nonneg _ ) ( V_functionFF_ge_one q P_mod S.d )

/-- Build a concrete `FunctionFieldSieveResult` from `FunctionFieldSieveData`,
    witnessing that the function-field Selberg sieve produces an improved
    (≤ classical) bound with improvement factor `1 / V_FF`. -/
def FunctionFieldSieve_to_FunctionFieldSieveResult
    (S : FunctionFieldSieveData) (P_mod : FqPoly q) :
    FunctionFieldSieveResult where
  q := q
  n := S.n
  classicalBound := (S.mainTermFF q : ℝ)
  improvedBound := (S.mainTermFF q : ℝ) / V_functionFF q P_mod S.d
  improvementFactor := 1 / V_functionFF q P_mod S.d
  hfactor_pos := div_pos one_pos (V_functionFF_pos q P_mod S.d)
  hfactor_le :=
    (div_le_one (V_functionFF_pos q P_mod S.d)).mpr (V_functionFF_ge_one q P_mod S.d)
  hbound := div_eq_mul_one_div _ _
  hclassical_pos := by
    have hq : 0 < q := (Fact.out : Nat.Prime q).pos
    have h : 0 < S.mainTermFF q := by
      simpa [FunctionFieldSieveData.mainTermFF] using Nat.pow_pos hq
    exact_mod_cast h

end