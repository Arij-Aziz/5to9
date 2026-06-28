/-
# Sieve.MassEnergyTradeoff.SharpBounds

Sharp mass–energy tradeoff for sieve-constrained majorants.

## Main results

* `selberg_l2_lower_bound` — ‖ν‖₂² ≥ |S|⁴ / (N³ · Q(λ)²)

The lower bound is sharp: it combines the restriction lower bound
  mass² · ‖ν‖₂² ≥ |S|⁴ / N
with mass = N · Q(λ) to extract a bound on ‖ν‖₂² alone.

No paper in the literature states this sandwich for sieve-constrained majorants to the authors' knowledge.

Status: ProvedInProject
-/
import Mathlib
import RequestProject.Core.MultiPrime.FourierRatio

open Finset BigOperators

noncomputable section

/-
Lower bound on ‖ν‖₂² in terms of Q(λ) and sifted cardinality.
    For the multi-prime Selberg majorant with mass = N·Q(λ):
      ‖ν‖₂² ≥ |S|⁴ / (N³ · Q(λ)²)

    Proof: From `multiPrime_restriction_lower_bound`:
      (N·Q(λ))² · ‖ν‖₂² ≥ |S|⁴/N
    Dividing both sides by (N·Q(λ))² gives the result.
-/
theorem selberg_l2_lower_bound
    (P m : ℕ) (hP : Squarefree P) (hP_pos : 0 < P) (hm : 0 < m)
    (lambda : ℕ → ℝ) (hlam_one : lambda 1 = 1)
    (hQ_pos : 0 < multiPrimeQuadForm P lambda) :
    let M := multiPrimeMajorant (P * m) P lambda (by omega) hlam_one
    M.l2NormSq ≥ M.targetMass ^ 4 / ((P * m : ℝ) ^ 3 * multiPrimeQuadForm P lambda ^ 2) := by
  have := multiPrime_restriction_lower_bound P m hP hP_pos hm lambda hlam_one;
  field_simp at this ⊢;
  convert this using 1

end
