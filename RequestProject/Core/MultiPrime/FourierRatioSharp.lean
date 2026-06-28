/-
# Sieve.MultiPrime.FourierRatioSharp

Sharp Fourier ratio lower bound for the multi-prime Selberg majorant.
Proves existence of a non-zero Fourier mode with large coefficient.

## Main results

* `sieveMass_eq_quadForm` — mass of ν equals N · Q(λ)
* `real_l2NormSq_eq` — complex L² norm of real function equals real L² norm
* `parseval_real` — Parseval for real-valued functions
* `fourier_zero_norm_sq` — |ν̂(0)|² = mass²
* `nonzero_fourier_sum_eq` — Σ_{ξ≠0} |ν̂(ξ)|² = N·Σν² − mass²
* `sharp_fourier_ratio_lower_bound` — ∃ ξ ≠ 0 with |ν̂(ξ)|² ≥ (N·Σν²−mass²)/(N−1)

-- Source: Derived from JTNB_2006 Proposition 4.2 + l2NormSq_multiPrime_eq_quadForm + Parseval.
-- Novel: Green-Tao 2006 bounds |ν̂(ξ)| above (Prop. 3.1 iv).
-- This lower bound on max_{ξ≠0}|ν̂(ξ)|² is new.

Status: ProvedInProject
-/
import Mathlib
import RequestProject.Core.MultiPrime.L2Identity
import RequestProject.Core.Fourier

open Finset BigOperators

noncomputable section

/-- The sieve mass: Σ_x ν(x). -/
noncomputable def sieveMass (N : ℕ) (lambda : ℕ → ℝ) (P : ℕ) : ℝ :=
  ∑ x : Fin N, selbergNu N P lambda x

/-- The Selberg Fourier coefficients: DFT of the Selberg majorant. -/
noncomputable def selbergFourier (N : ℕ) [NeZero N] (lambda : ℕ → ℝ) (P : ℕ) :
    Fin N → ℂ :=
  realDft' N (selbergNu N P lambda)

/-- The sieve mass equals N · Q(λ). -/
lemma sieveMass_eq_quadForm
    (P m : ℕ) (hP : Squarefree P) (hP_pos : 0 < P) (hm : 0 < m)
    (lambda : ℕ → ℝ) :
    sieveMass (P * m) lambda P = (P * m : ℝ) * multiPrimeQuadForm P lambda := by
  exact l2NormSq_multiPrime_eq_quadForm P m hP hP_pos hm lambda

/-- For real-valued f, the complex L² norm equals the real L² norm. -/
lemma real_l2NormSq_eq {N : ℕ} (f : Fin N → ℝ) :
    l2NormSq' N (realToComplex' N f) = ∑ x : Fin N, f x ^ 2 := by
  unfold l2NormSq' realToComplex'
  simp +decide [Complex.normSq, sq]

/-- Parseval for real-valued functions:
    Σ_ξ ‖ν̂(ξ)‖² = N · Σ_x ν(x)² -/
lemma parseval_real (N : ℕ) [NeZero N] (f : Fin N → ℝ) :
    ∑ ξ : Fin N, ‖realDft' N f ξ‖ ^ 2 = (N : ℝ) * ∑ x : Fin N, f x ^ 2 := by
  convert parseval' N (realToComplex' N f) using 1
  · rfl
  · rw [real_l2NormSq_eq]

/-- The zero Fourier coefficient has norm² = mass². -/
lemma fourier_zero_norm_sq (N : ℕ) [NeZero N] (f : Fin N → ℝ) :
    ‖realDft' N f ⟨0, NeZero.pos N⟩‖ ^ 2 = (∑ x : Fin N, f x) ^ 2 := by
  convert congr_arg (· ^ 2) (congr_arg Complex.re (dft_zero_eq_sum' N f)) using 1
    <;> norm_num [Complex.normSq, Complex.sq_norm]
    <;> ring_nf!
  unfold realDft' dft'
  norm_num [realToComplex']

/-- The sum of ‖ν̂(ξ)‖² over nonzero frequencies:
    Σ_{ξ≠0} ‖ν̂(ξ)‖² = N · Σ_x ν(x)² − (Σ_x ν(x))² -/
lemma nonzero_fourier_sum_eq (N : ℕ) [NeZero N] (hN : 1 < N) (f : Fin N → ℝ) :
    ∑ ξ ∈ Finset.univ.filter (fun ξ : Fin N => ξ.val ≠ 0),
      ‖realDft' N f ξ‖ ^ 2 =
    (N : ℝ) * ∑ x : Fin N, f x ^ 2 - (∑ x : Fin N, f x) ^ 2 := by
  convert congr_arg₂ (· - ·) (parseval_real N f) (fourier_zero_norm_sq N f) using 1
  simp +decide [Finset.filter_ne', Finset.filter_eq']

/-- Pigeonhole for nonneg functions: if Σ f ≥ T and f nonneg on S with |S| = n,
    then ∃ x ∈ S with f(x) ≥ T/|S|. -/
lemma exists_ge_of_sum_ge {n : ℕ} {S : Finset (Fin n)} (hS : S.Nonempty)
    {f : Fin n → ℝ} (_hf : ∀ x ∈ S, 0 ≤ f x)
    {T : ℝ} (hT : T ≤ ∑ x ∈ S, f x) :
    ∃ x ∈ S, T / S.card ≤ f x := by
  contrapose! hT
  convert Finset.sum_lt_sum_of_nonempty hS hT using 1
  norm_num [mul_div_cancel₀, hS.ne_empty]

/-
Source: Derived from JTNB_2006 Proposition 4.2 + Parseval

Sharp Fourier ratio lower bound: there exists a nonzero frequency ξ
    with |ν̂(ξ)|² ≥ (N · Σ_x ν(x)² − mass²) / (N−1).

    Proof: Parseval gives total Fourier energy = N · Σν².
    Subtract the zero mode (= mass²) to get nonzero energy = N·Σν² − mass².
    Pigeonhole over N−1 nonzero modes gives the bound.
-/
theorem sharp_fourier_ratio_lower_bound
    (P m : ℕ) (hP : Squarefree P) (hP_pos : 0 < P) (hm : 0 < m)
    (lambda : ℕ → ℝ)
    [NeZero (P * m)]
    (hN : 1 < P * m) :
    ∃ ξ : Fin (P * m), ξ.val ≠ 0 ∧
      ‖selbergFourier (P * m) lambda P ξ‖ ^ 2 ≥
        ((P * m : ℝ) * (∑ x : Fin (P * m), selbergNu (P * m) P lambda x ^ 2)
          - (sieveMass (P * m) lambda P) ^ 2) / ((P * m : ℝ) - 1) := by
  obtain ⟨ξ, hξ⟩ : ∃ ξ ∈ Finset.univ.filter (fun ξ : Fin (P * m) => ξ.val ≠ 0), (‖(selbergFourier (P * m) lambda P ξ)‖ ^ 2) ≥ (∑ ξ ∈ Finset.univ.filter (fun ξ : Fin (P * m) => ξ.val ≠ 0), ‖(selbergFourier (P * m) lambda P ξ)‖ ^ 2) / (Finset.univ.filter (fun ξ : Fin (P * m) => ξ.val ≠ 0)).card := by
    convert exists_ge_of_sum_ge _ _ _;
    · exact ⟨ ⟨ 1, by linarith ⟩, by norm_num ⟩;
    · exact fun _ _ => sq_nonneg _;
    · rfl;
  refine' ⟨ ξ, by simpa using hξ.1, hξ.2.trans' _ ⟩;
  convert le_rfl using 2;
  · convert nonzero_fourier_sum_eq ( P * m ) hN ( selbergNu ( P * m ) P lambda ) using 1;
    · rfl
    · simp only [sieveMass]; push_cast; ring
  · norm_num [ Finset.filter_not, Finset.card_sdiff ];
    rw [ Finset.card_filter ] ; norm_num [ hP_pos, hm ]

end
