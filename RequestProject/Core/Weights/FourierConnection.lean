/-
# Sieve.Weights.FourierConnection

Connects the spatial L² norm to the Selberg quadratic form.
When ν(x) = Σ_{d | gcd(x,P)} λ_d, the L² norm decomposes as a
quadratic form in the sieve weights λ_d.

## Main results

* `card_multiples_of_dvd` — the number of multiples of d in Fin N is N / d (when d ∣ N)
* `card_joint_multiples` — |{x : d₁ ∣ x ∧ d₂ ∣ x}| = |{x : lcm(d₁,d₂) ∣ x}|
* `l2NormSq_eq_quadForm_single_prime` — L² norm = quadratic form for single-prime sieve

Status: ProvedInProject
-/
import Mathlib
import RequestProject.Core.Majorant
import RequestProject.Core.SelbergComparison
import RequestProject.Core.FourierRatio

open Finset BigOperators

noncomputable section

/-! ## Counting multiples in Fin N -/

/-
The number of multiples of d in Fin N equals N / d when d ∣ N and d > 0.
-/
lemma card_multiples_of_dvd (N d : ℕ) (hd : 0 < d) (hdN : d ∣ N) :
    (Finset.univ.filter (fun x : Fin N => d ∣ x.val)).card = N / d := by
      convert card_multiplesInFin d ( N / d ) hd using 1;
      obtain ⟨ k, rfl ⟩ := hdN; norm_num [ Finset.card_univ, multiplesInFin ] ;
      convert rfl; all_goals rw [ Nat.mul_div_cancel_left _ hd ]

/-- Joint divisibility by d₁ and d₂ is equivalent to divisibility by lcm(d₁, d₂). -/
lemma joint_dvd_iff_lcm_dvd (d₁ d₂ n : ℕ) :
    d₁ ∣ n ∧ d₂ ∣ n ↔ Nat.lcm d₁ d₂ ∣ n := by
  exact (Nat.lcm_dvd_iff).symm

/-- The cardinality of elements jointly divisible by d₁ and d₂ equals the cardinality
    of elements divisible by lcm(d₁, d₂). -/
lemma card_joint_multiples (N d₁ d₂ : ℕ) :
    (Finset.univ.filter (fun x : Fin N => d₁ ∣ x.val ∧ d₂ ∣ x.val)).card =
    (Finset.univ.filter (fun x : Fin N => Nat.lcm d₁ d₂ ∣ x.val)).card := by
  congr 1
  ext x
  simp [joint_dvd_iff_lcm_dvd]

/-! ## Single-prime model: D = {1, d} -/

/-
In the single-prime model with d ≥ 2 and N = d * m, compute the L² norm
    of the sieve majorant ν(x) = 1 if d ∤ x, ν(x) = 1/2 if d ∣ x.

    The L² norm is: (d*m - m) · 1² + m · (1/2)² = d*m - m + m/4 = d*m - 3m/4.
-/
lemma sieveMajorant_l2NormSq (d m : ℕ) (hd : 2 ≤ d) (hm : 1 ≤ m)
    (hN : 0 < d * m) :
    (sieveMajorant d m hN).l2NormSq = (d * m : ℝ) - 3 * (m : ℝ) / 4 := by
      have := @card_multiples_of_dvd ( d * m ) d ( by linarith ) ( by norm_num );
      rw [ Nat.mul_div_cancel_left _ ( by linarith ) ] at this;
      unfold sieveMajorant;
      unfold sieveMajorantFun sieveTargetFun Majorant.l2NormSq; norm_num [ Finset.sum_ite ] ; ring_nf;
      rw [ Finset.filter_not, Finset.card_sdiff ] ; norm_num [ this ] ; ring_nf;
      rw [ Nat.cast_sub ] <;> push_cast <;> nlinarith

/-
L² norm of the constant-1 baseline is N = d * m.
-/
lemma sieveBaseline_l2NormSq (d m : ℕ) (hN : 0 < d * m) :
    (sieveBaseline d m hN).l2NormSq = (d * m : ℝ) := by
      convert Finset.sum_const ( 1 : ℝ ) using 1 ; norm_num [ Majorant.l2NormSq, sieveBaseline ];
      all_goals norm_cast;
      convert rfl;
      convert Finset.card_fin ( d * m );
      norm_num [ Finset.card_univ ]

/-- **L² improvement**: The sieve majorant has strictly smaller L² norm
    than the constant baseline. -/
theorem sieveMajorant_l2_improvement (d m : ℕ) (hd : 2 ≤ d) (hm : 1 ≤ m) :
    (selbergComparison d m (by positivity)).l2Improvement := by
  unfold MajorantComparison.l2Improvement selbergComparison
  have hN : 0 < d * m := by positivity
  rw [sieveMajorant_l2NormSq d m hd hm hN, sieveBaseline_l2NormSq d m hN]
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  linarith

/-! ## Gap 1: Selberg Quadratic Form Identity -/

/-
The L² norm of the Selberg sieve majorant, normalized by N = d*m, equals
    the Selberg quadratic form Q(λ) = 1 - 3/(4d) at λ₁ = 1, λ_d = -1/2.
-/
theorem sieveMajorant_l2NormSq_eq_selbergForm
    (d m : ℕ) (hd : 2 ≤ d) (hm : 1 ≤ m) :
    let hN := show 0 < d * m by positivity
    (sieveMajorant d m hN).l2NormSq / (d * m) =
      1 - 3 / (4 * (d : ℝ)) := by
  convert congr_arg ( fun x : ℝ => x / ( d * m ) ) ( sieveMajorant_l2NormSq d m hd hm ( by positivity ) ) using 1 ; ring_nf;
  norm_num [ show d ≠ 0 by linarith, show m ≠ 0 by linarith ]

/-! ## Gap 2: Dual Improvement Theorem -/

/-- The Selberg sieve majorant simultaneously improves BOTH mass and L² norm
    over the constant baseline. This is the complete sieve improvement theorem. -/
theorem selbergComparison_dual_improvement
    (d m : ℕ) (hd : 2 ≤ d) (hm : 1 ≤ m) :
    let C := selbergComparison d m (by positivity)
    C.massImprovement ∧ C.l2Improvement := by
  constructor
  · exact selbergComparison_massImprovement d m hd hm
  · exact sieveMajorant_l2_improvement d m hd hm

/-! ## Gap 3: Concrete End-to-End Restriction Bound -/

/-
**Concrete Restriction Lower Bound for the Selberg Sieve**.
    Explicit form of the Fourier ratio bound for the Selberg majorant ν on Fin(d*m),
    purely in terms of arithmetic parameters (d, m).
-/
theorem selberg_concrete_restriction_bound
    (d m : ℕ) (hd : 2 ≤ d) (hm : 1 ≤ m) :
    let hN := show 0 < d * m by positivity
    let M := sieveMajorant d m hN
    M.massSquaredTimesL2Sq ≥ ((d * m - m : ℕ) : ℝ) ^ 4 / (d * m) := by
  convert sieveMajorant_targetMass d m ( by linarith ) ( by positivity ) using 1;
  constructor <;> intro h <;> norm_cast at *;
  · convert sieveMajorant_targetMass d m ( by linarith ) ( by positivity ) using 1;
  · convert Majorant.sieve_fourier_ratio_bound ( sieveMajorant d m ( by positivity ) ) ( by positivity ) using 1;
    grind +splitIndPred

end
