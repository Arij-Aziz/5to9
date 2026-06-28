/-
# RestrictionLowerBoundSelberg.lean
# Result 2: Restriction Lower Bound for Selberg Majorants

## Mathematical Statement

For the multi-prime Selberg majorant, the 2-point correlation condition forces
a lower bound on the Fourier L⁴ norm.

The key structural observation is:
- `Majorant.l2NormSq = ∑ selbergNu(x)² = ∑ selbergWeight(x)⁴`
- The correlation `∑ selbergWeight(x) * selbergWeight(x+h)` is bounded by
  `(P*m) * multiPrimeQuadForm P lambda` (from `selbergWeight_correlation_coprime_bound`)

The restriction lower bound is stated conditionally on the Parseval-convolution
identity (which is not proved in Core/Fourier.lean).

Does NOT use `optimalWeight_quadForm_eq` (the sorry).

Status: ProvedInProject
-/
import Mathlib
import RequestProject.Core.MultiPrime.MoebiusWeights
import RequestProject.Core.MultiPrime.SelbergWeightCorrelation
import RequestProject.Core.RestrictionLowerBound
import RequestProject.Core.Transference
import RequestProject.Core.MultiPrime.FourierRatio

open Finset BigOperators PseudorandomMajorant

noncomputable section

/-
The l2NormSq of the multi-prime Selberg majorant equals the sum of
    selbergWeight(x)⁴, since selbergNu = selbergWeight².
-/
lemma majorant_l2NormSq_eq_selbergWeight_fourth
    (N P : ℕ) (lambda : ℕ → ℝ) (hP : P ≠ 0) (hlam_one : lambda 1 = 1) :
    (multiPrimeMajorant N P lambda hP hlam_one).l2NormSq =
    ∑ x : Fin N, selbergWeight N P lambda x ^ 4 := by
  -- By definition of l2NormSq, we have:
  unfold Majorant.l2NormSq multiPrimeMajorant
  simp [selbergNu_eq_sq];
  exact Finset.sum_congr rfl fun _ _ => by ring;

/-
Restriction lower bound for Selberg majorants (Fourier formulation).
    The 2-point correlation condition forces the L⁴ Fourier energy to be large.
    Conditional on the Parseval-convolution identity (hParseval hypothesis).
    This theorem is sorry-free: hParseval is a hypothesis, not a sorry.

    New result: Green-Tao prove upper bounds; this gives the lower bound direction.
-/
theorem selberg_restriction_lower_fourier
    {N : ℕ} [NeZero N] (hN : (0 : ℝ) < N)
    (P_pr : StrongPseudorandomMajorant N)
    (hcorr : P_pr.correlationError < 1)
    (hParseval : ∀ f : Fin N → ℝ,
      ∑ h : Fin N, (∑ x : Fin N, f x * f (x + h)) ^ 2 =
      N * ∑ ξ : Fin N, ‖realDft' N f ξ‖ ^ 4) :
    N ^ 2 * (1 - P_pr.correlationError) ^ 2
      ≤ ∑ ξ : Fin N, ‖realDft' N P_pr.nu ξ‖ ^ 4 := by
  -- From correlation_bound we get for each h: |(∑ x, nu(x)*nu(x+h))/N - 1| ≤ ε, so ∑ x, nu(x)*nu(x+h) ≥ N*(1-ε).
  have h_sum_bound : ∀ h : Fin N, (∑ x : Fin N, P_pr.nu x * P_pr.nu (x + h)) ≥ N * (1 - P_pr.correlationError) := by
    intros h
    have h_sum_bound : (∑ x : Fin N, P_pr.nu x * P_pr.nu (x + h)) / N ≥ 1 - P_pr.correlationError := by
      linarith [ abs_le.mp ( P_pr.correlation_bound h ) ];
    rwa [ ge_iff_le, le_div_iff₀' hN ] at h_sum_bound;
  -- By summing over h, we get ∑ h, (∑ x, nu(x)*nu(x+h))^2 ≥ N * N^2*(1-ε)^2.
  have h_sum_sq_bound : ∑ h : Fin N, (∑ x : Fin N, P_pr.nu x * P_pr.nu (x + h)) ^ 2 ≥ N * N^2 * (1 - P_pr.correlationError) ^ 2 := by
    refine' le_trans _ ( Finset.sum_le_sum fun i _ => pow_le_pow_left₀ ( mul_nonneg hN.le ( sub_nonneg.mpr hcorr.le ) ) ( h_sum_bound i ) 2 ) ; norm_num ; ring_nf ; norm_num;
  nlinarith [ hParseval P_pr.nu ]

end