/-
# Sieve.Fourier

Finite Fourier analysis on residue spaces / finite quotient models.
Parseval-type identities and basic transform properties.

Status: ProvedInProject (definitions and basic properties)
-/
import Mathlib

open Finset BigOperators Complex

noncomputable section

/-! ## Discrete Fourier Transform on ℤ/Nℤ -/

/-- The discrete Fourier transform of a function on Fin N. -/
def dft' (N : ℕ) [NeZero N] (f : Fin N → ℂ) (k : Fin N) : ℂ :=
  ∑ n : Fin N, f n * Complex.exp (-2 * Real.pi * Complex.I * k.val * n.val / N)

/-- The inverse discrete Fourier transform. -/
def idft' (N : ℕ) [NeZero N] (F : Fin N → ℂ) (n : Fin N) : ℂ :=
  (1 / N) * ∑ k : Fin N, F k * Complex.exp (2 * Real.pi * Complex.I * k.val * n.val / N)

/-- The L² norm squared of f on Fin N -/
def l2NormSq' (N : ℕ) (f : Fin N → ℂ) : ℝ :=
  ∑ n : Fin N, ‖f n‖ ^ 2

/-- The L² norm squared of the DFT -/
def dftL2NormSq' (N : ℕ) [NeZero N] (f : Fin N → ℂ) : ℝ :=
  ∑ k : Fin N, ‖dft' N f k‖ ^ 2

/-- L² norm is nonneg -/
lemma l2NormSq'_nonneg (N : ℕ) (f : Fin N → ℂ) : 0 ≤ l2NormSq' N f :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- DFT L² norm is nonneg -/
lemma dftL2NormSq'_nonneg (N : ℕ) [NeZero N] (f : Fin N → ℂ) : 0 ≤ dftL2NormSq' N f :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-! ## Parseval's theorem -/

/-
Parseval's theorem: ‖f̂‖² = N · ‖f‖²
-/
theorem parseval' (N : ℕ) [NeZero N] (f : Fin N → ℂ) :
    dftL2NormSq' N f = N * l2NormSq' N f := by
  -- We need to evaluate the sum over $k$. Consider the inner sum
  -- $\sum_{k=0}^{N-1} e^{-2\pi i k (n-m)/N}$.
  have h_inner : ∀ n m : Fin N, ∑ k : Fin N, Complex.exp (-2 * Real.pi * Complex.I * (k.val : ℂ) * (n.val - m.val) / N) = if n = m then (↑N : ℂ) else 0 := by
    intro n m
    by_cases hnm : n = m
    · simp [hnm];
    -- When $n \neq m$, the sum $\sum_{k=0}^{N-1} e^{-2\pi i k (n-m)/N}$ is a geometric series with common ratio $e^{-2\pi i (n-m)/N}$.
    have h_geo_series : ∑ k ∈ Finset.range N, (Complex.exp (-2 * Real.pi * Complex.I * (n.val - m.val) / N)) ^ k = 0 := by
      rw [ geom_sum_eq ] <;> norm_num [ ← Complex.exp_nat_mul, mul_div_cancel₀, NeZero.ne ];
      · exact Or.inl ( sub_eq_zero_of_eq <| Complex.exp_eq_one_iff.mpr ⟨ -n + m, by push_cast; ring ⟩ );
      · rw [ Complex.exp_eq_one_iff ];
        -- Since $n \neq m$, $n - m$ is not divisible by $N$, hence $-(n - m) / N$ is not an integer.
        intro h
        obtain ⟨k, hk⟩ := h
        have h_div : (n - m : ℤ) = -k * N := by
          exact_mod_cast ( by rw [ div_eq_iff ( NeZero.ne _ ) ] at hk; norm_num [ Complex.ext_iff ] at hk; nlinarith [ Real.pi_pos ] : ( n : ℝ ) - m = -k * N );
        exact hnm ( Fin.ext <| by nlinarith [ show k = 0 by nlinarith [ Fin.is_lt n, Fin.is_lt m ] ] );
    simp_all +decide [ ← Complex.exp_nat_mul, mul_div_assoc, mul_assoc, mul_comm, mul_left_comm, Finset.sum_range ];
    exact Eq.trans ( Finset.sum_congr rfl fun _ _ => by ring_nf ) h_geo_series;
  -- Using the result of the inner sum, we can simplify the expression.
  have h_simplify : ∑ k : Fin N, (dft' N f k) * starRingEnd ℂ (dft' N f k) = ∑ n : Fin N, ∑ m : Fin N, f n * starRingEnd ℂ (f m) * ∑ k : Fin N, Complex.exp (-2 * Real.pi * Complex.I * (k.val : ℂ) * (n.val - m.val) / N) := by
    simp +decide only [dft', starRingEnd_apply, sum_mul];
    rw [ Finset.sum_comm ] ; refine' Finset.sum_congr rfl fun i hi => _ ; simp +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul ] ; ring_nf;
    rw [ Finset.sum_comm ] ; congr ; ext ; congr ; ext ; norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im ] ; ring_nf;
    norm_num [ Real.sin_add, Real.cos_add ] ; ring_nf ; norm_num;
  simp_all +decide [ mul_comm, mul_assoc, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul, dftL2NormSq', l2NormSq' ];
  convert congr_arg Complex.re h_simplify using 2 <;> norm_num [ Complex.normSq, Complex.sq_norm ] ; ring_nf

/-! ## Circular convolution (using modular arithmetic) -/

/-- Circular convolution on Fin N, using proper modular index. -/
def circConv' (N : ℕ) [NeZero N] (f g : Fin N → ℂ) (n : Fin N) : ℂ :=
  ∑ k : Fin N, f k * g ⟨((n : ZMod N) - (k : ZMod N)).val, ZMod.val_lt _⟩

/-! ## Real-valued Fourier analysis -/

/-- Embed a real function into ℂ for Fourier analysis -/
def realToComplex' (N : ℕ) (f : Fin N → ℝ) : Fin N → ℂ :=
  fun n => (f n : ℂ)

/-- The Fourier transform of a real-valued function -/
def realDft' (N : ℕ) [NeZero N] (f : Fin N → ℝ) : Fin N → ℂ :=
  dft' N (realToComplex' N f)

/-- L¹ norm of the DFT (restriction norm type quantity) -/
def dftL1Norm' (N : ℕ) [NeZero N] (f : Fin N → ℝ) : ℝ :=
  ∑ k : Fin N, ‖realDft' N f k‖

/-- Fourier coefficient at 0 is the sum of f -/
lemma dft_zero_eq_sum' (N : ℕ) [NeZero N] (f : Fin N → ℝ) :
    realDft' N f ⟨0, NeZero.pos N⟩ = ∑ n : Fin N, (f n : ℂ) := by
  simp [realDft', dft', realToComplex']

end
