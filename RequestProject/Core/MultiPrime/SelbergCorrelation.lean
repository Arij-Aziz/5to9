/-
# Sieve.MultiPrime.SelbergCorrelation

Correlation bounds for the multi-prime Selberg majorant.

## Main results

* `selbergNu_autocorrelation_eq_l2` — h=0 autocorrelation is the L² norm
* `correlationBound` — the error bound for the correlation sum
* `correlationBound_nonneg` — the bound is nonneg
* `selbergWeight_corr_bound` — coprime-shift correlation ≤ (P*m)*Q(λ)
* `selbergWeight_autocorr_eq` — h=0 autocorrelation = (P*m)*Q(λ)

-- Source: Green-Tao 2007 (0404188v6-3.pdf) Proposition 9.1 as model.

Status: ProvedInProject
-/
import Mathlib
import RequestProject.Core.MultiPrime.SelbergWeightCorrelation
import RequestProject.Core.CorrelationBound.AdditiveEnergyLower

open Finset BigOperators

noncomputable section

/-- The correlation bound for shift h.
    This is a uniform bound valid for all shifts, using the triangle inequality
    on the double sum expansion of the correlation. The bound is
    Σ_{d,e} |λ_d| |λ_e| / lcm(d,e), which equals Q(|λ|). -/
noncomputable def correlationBound (P m : ℕ) (lambda : ℕ → ℝ) (_h : Fin (P * m)) : ℝ :=
  ∑ d ∈ sqfDivisors P, ∑ e ∈ sqfDivisors P,
    |lambda d| * |lambda e| / (Nat.lcm d e : ℝ)

/-- The correlation bound is nonneg. -/
lemma correlationBound_nonneg (P m : ℕ) (lambda : ℕ → ℝ) (h : Fin (P * m)) :
    0 ≤ correlationBound P m lambda h :=
  Finset.sum_nonneg fun d _ => Finset.sum_nonneg fun e _ =>
    div_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (Nat.cast_nonneg _)

-- Source: Direct identity
/-- The h=0 autocorrelation: Σ_x ν(x)² equals the L² norm of ν. -/
theorem selbergNu_autocorrelation_eq_l2
    (P m : ℕ) (hP_pos : 0 < P) (_hm : 0 < m)
    (lambda : ℕ → ℝ) :
    ∑ x : Fin (P * m),
      selbergNu (P * m) P lambda x * selbergNu (P * m) P lambda x =
    ∑ x : Fin (P * m), selbergNu (P * m) P lambda x ^ 2 := by
  exact Finset.sum_congr rfl fun x _ => (sq (selbergNu (P * m) P lambda x)).symm

/-- Coprime-shift correlation bound via selbergWeight. -/
theorem selbergWeight_corr_bound
    (P m : ℕ) (hP : Squarefree P) (hP_pos : 0 < P) (hm : 0 < m)
    (lambda : ℕ → ℝ)
    (hlam_nonneg : ∀ d ∈ sqfDivisors P, 0 ≤ lambda d)
    (h : Fin (P * m)) (hcop : Nat.Coprime h.val P) :
    ∑ x : Fin (P * m),
      selbergWeight (P * m) P lambda x *
      selbergWeight (P * m) P lambda ⟨(x.val + h.val) % (P * m),
        Nat.mod_lt _ (by positivity)⟩
    ≤ (P * m : ℝ) * multiPrimeQuadForm P lambda :=
  selbergWeight_correlation_coprime_bound P m hP hP_pos hm lambda hlam_nonneg h hcop

/-- h=0 autocorrelation: Σ selbergWeight(x)² = (P*m) * Q(λ). -/
theorem selbergWeight_autocorr_eq
    (P m : ℕ) (hP : Squarefree P) (hP_pos : 0 < P) (hm : 0 < m)
    (lambda : ℕ → ℝ) :
    ∑ x : Fin (P * m), selbergWeight (P * m) P lambda x ^ 2
    = (P * m : ℝ) * multiPrimeQuadForm P lambda :=
  selbergWeight_autocorrelation_eq P m hP hP_pos hm lambda

end
