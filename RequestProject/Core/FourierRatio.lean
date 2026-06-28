/-
# Sieve.FourierRatio

The Sieve Fourier Ratio Tradeoff Theorem: a discrete arithmetic analogue
of the Fourier ratio bounds in Iosevich–Li–Palsson–Yavicoli, specialized
to sieve-constrained functions on finite cyclic groups.

## Main results

* `cauchy_schwarz_mass` — Cauchy–Schwarz for the L¹ vs L² tradeoff
* `mass_sq_ge_targetMass_sq` — mass² ≥ targetMass² from domination
* `sieve_fourier_ratio_bound` — the main tradeoff: mass² · l2NormSq ≥ targetMass⁴ / N
* `sieve_fourier_ratio_fourier_form` — Fourier restatement via Parseval: mass² ≤ N · l2NormSq
* `mass_sq_le_N_mul_l2NormSq_via_parseval` — the Parseval-based proof of the Fourier bound

## Mathematical content

The theorem certifies that no sieve majorant can simultaneously have small L¹ mass
AND small L² norm without the sifted set being correspondingly small. This is an
uncertainty-type tradeoff in the Donoho–Stark sense.

The key chain is:
  domination → mass lower bound → Cauchy–Schwarz → Parseval

Status: ProvedInProject
-/
import Mathlib
import RequestProject.Core.Majorant
import RequestProject.Core.Fourier

open Finset BigOperators

noncomputable section

namespace Majorant

variable {N : ℕ} (M : Majorant N)

/-! ## Phase 0: Definitions -/

/-- The sieve Fourier ratio: mass · l2NormSq (working without sqrt to avoid Real.sqrt pain).
    This is the squared version of μ(ν) · ‖ν‖₂. -/
def sieveFourierRatio : ℝ := M.mass * M.l2NormSq

/-- mass² · l2NormSq, the quantity appearing in the main bound. -/
def massSquaredTimesL2Sq : ℝ := M.mass ^ 2 * M.l2NormSq

/-! ## Phase 1: Cauchy–Schwarz for mass vs L² norm -/

/-- Cauchy–Schwarz inequality: (∑ ν(x))² ≤ N · ∑ ν(x)².
    The L¹ norm squared is bounded by N times the L² norm squared. -/
lemma cauchy_schwarz_mass (_hN : 0 < N) :
    M.mass ^ 2 ≤ ↑N * M.l2NormSq := by
  have h_cauchy_schwarz : (∑ x : Fin N, M.nu x * 1)^2 ≤ (∑ x : Fin N, M.nu x^2) * (∑ x : Fin N, 1^2) :=
    sum_mul_sq_le_sq_mul_sq univ M.nu fun _ => 1
  simpa [mul_comm, Majorant.mass, Majorant.l2NormSq] using h_cauchy_schwarz

/-! ## Phase 1b: Parseval-based proof of the same bound -/

/-
The spatial L² norm of M.nu (as a complex function) equals M.l2NormSq.
-/
private lemma l2NormSq'_realToComplex_eq :
    l2NormSq' N (realToComplex' N M.nu) = M.l2NormSq := by
      exact Finset.sum_congr rfl fun _ _ => by unfold realToComplex'; norm_num [ abs_of_nonneg, M.nu_nonneg ] ;

/-
The DFT at k=0 has norm squared equal to mass².
-/
private lemma dft_zero_norm_sq_eq_mass_sq [NeZero N] :
    ‖realDft' N M.nu ⟨0, NeZero.pos N⟩‖ ^ 2 = M.mass ^ 2 := by
      -- Since the DFT at k=0 is equal to M.mass, taking the norm squared of that should give us M.mass squared.
      have h_dft_zero : realDft' N M.nu ⟨0, NeZero.pos N⟩ = M.mass := by
        convert dft_zero_eq_sum' N M.nu using 1;
        norm_cast;
      rw [ h_dft_zero, Complex.norm_real, Real.norm_of_nonneg ( M.mass_nonneg ) ]

/-
The k=0 term of the DFT L² norm is at most the total DFT L² norm.
-/
private lemma dft_zero_le_dftL2NormSq [NeZero N] :
    ‖realDft' N M.nu ⟨0, NeZero.pos N⟩‖ ^ 2 ≤ dftL2NormSq' N (realToComplex' N M.nu) := by
      exact Finset.single_le_sum ( fun k _ => sq_nonneg ( ‖dft' N ( realToComplex' N M.nu ) k‖ ) ) ( Finset.mem_univ _ )

/-- **Parseval-based proof**: mass² ≤ N · l2NormSq.
    This goes through the DFT: ν̂(0) = mass, and by Parseval
    ∑_k |ν̂(k)|² = N · ∑_x ν(x)², so |ν̂(0)|² ≤ ∑_k |ν̂(k)|² = N · l2NormSq.
    Uses `dft_zero_eq_sum'` and `parseval'` by name. -/
lemma mass_sq_le_N_mul_l2NormSq_via_parseval (_hN : 0 < N) [NeZero N] :
    M.mass ^ 2 ≤ ↑N * M.l2NormSq := by
  calc M.mass ^ 2
      = ‖realDft' N M.nu ⟨0, NeZero.pos N⟩‖ ^ 2 := by
        rw [M.dft_zero_norm_sq_eq_mass_sq]
    _ ≤ dftL2NormSq' N (realToComplex' N M.nu) := M.dft_zero_le_dftL2NormSq
    _ = ↑N * l2NormSq' N (realToComplex' N M.nu) := parseval' N (realToComplex' N M.nu)
    _ = ↑N * M.l2NormSq := by rw [M.l2NormSq'_realToComplex_eq]

/-! ## Phase 2: Mass dominates target mass -/

/-- mass² ≥ targetMass² since mass ≥ targetMass and both are nonneg. -/
lemma mass_sq_ge_targetMass_sq :
    M.targetMass ^ 2 ≤ M.mass ^ 2 := by
  exact pow_le_pow_left₀ (Majorant.targetMass_nonneg M) (Majorant.mass_ge_targetMass M) _

/-! ## Phase 3: The main tradeoff theorem -/

/-- **Sieve Fourier Ratio Tradeoff Theorem**:
    mass² · l2NormSq ≥ targetMass⁴ / N.

    No sieve majorant can simultaneously have small L¹ mass and small L² norm
    without the target mass being correspondingly small. -/
theorem sieve_fourier_ratio_bound (hN : 0 < N) :
    M.massSquaredTimesL2Sq ≥ M.targetMass ^ 4 / ↑N := by
  field_simp
  rw [show M.massSquaredTimesL2Sq = M.mass ^ 2 * M.l2NormSq by rfl]
  nlinarith [M.mass_sq_ge_targetMass_sq, M.cauchy_schwarz_mass hN,
    show 0 ≤ (N : ℝ) * M.l2NormSq by exact mul_nonneg (Nat.cast_nonneg _) M.l2NormSq_nonneg]

/-! ## Phase 5: Fourier restatement -/

/-- **Fourier form of the ratio bound**: mass² ≤ N · l2NormSq.
    Interpretation: |ν̂(0)|² ≤ total Fourier energy.
    The k=0 Fourier coefficient is ν̂(0) = ∑ ν(x) = mass (by `dft_zero_eq_sum'`),
    and by `parseval'`, ∑|ν̂(k)|² = N · ‖ν‖₂². So mass² ≤ N · l2NormSq.

    This version uses the Parseval-based proof path. -/
theorem sieve_fourier_ratio_fourier_form (hN : 0 < N) [NeZero N] :
    M.mass ^ 2 ≤ ↑N * M.l2NormSq := by
  exact M.mass_sq_le_N_mul_l2NormSq_via_parseval hN

end Majorant

end