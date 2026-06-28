/-
# Sieve.CorrelationBound.AdditiveEnergyLower

Correlation-enhanced additive energy lower bound for pseudorandom majorants.

## Main results

* `correlation_additive_energy_lower` — For a `StrongPseudorandomMajorant` with
    2-point correlationError ≤ ε and averageCondition ≤ δ:
      E(ν) ≥ N³ · (1 - 2ε - 4δ)

This is the *lower* bound corresponding to Green-Tao's Fourier upper bound theory.
The proof uses Cauchy-Schwarz on the convolution, the correlation condition to
control each shift, and the average condition to control the total mass.

Instantiation for `multiPrimeMajorant` requires computing Σ_x ν(x)ν(x+h) explicitly,
which is a separate project.

Status: ProvedInProject
-/
import Mathlib
import RequestProject.Core.RestrictionLowerBound
import RequestProject.Core.Transference

open Finset BigOperators

noncomputable section

/-- The convolution function g(h) = Σ_x f(x) · f(x + h). -/
def correlationSum {N : ℕ} (f : Fin N → ℝ) (h : Fin N) : ℝ :=
  ∑ x : Fin N, f x * f (x + h)

/-
The sum of the convolution over all shifts equals (Σ f)².
-/
lemma correlationSum_total_eq_sq {N : ℕ} [NeZero N] (f : Fin N → ℝ) :
    ∑ h : Fin N, correlationSum f h = (∑ x : Fin N, f x) ^ 2 := by
  unfold correlationSum;
  simp +decide only [pow_two, sum_mul];
  rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; intros ; rw [ Finset.mul_sum ] ;
  exact Equiv.sum_comp ( Equiv.addLeft _ ) fun x => f _ * f x

/-
Cauchy-Schwarz for a sum of squares: Σ g(h)² ≥ (Σ g(h))² / N.
-/
lemma sum_sq_ge_sq_div {N : ℕ} (g : Fin N → ℝ) :
    ∑ h : Fin N, g h ^ 2 ≥ (∑ h : Fin N, g h) ^ 2 / N := by
  rcases N with ( _ | N );
  · norm_num;
  · rw [ ge_iff_le, div_le_iff₀ ] <;> norm_cast;
    · have := @fin_cauchy_schwarz ( N + 1 ) g ; norm_num at * ; linarith;
    · grind

/-
For a StrongPseudorandomMajorant, the correlation sum at each shift h
    satisfies |g(h) - N| ≤ correlationError · N.
    This follows directly from the correlation_bound field.
-/
lemma correlation_sum_approx_N {N : ℕ} [NeZero N]
    (P : PseudorandomMajorant.StrongPseudorandomMajorant N) (h : Fin N) :
    |correlationSum P.nu h - N| ≤ P.correlationError * N := by
  have hN : (0:ℝ) ≤ N := Nat.cast_nonneg N
  have hNe : (N:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have e : (∑ x : Fin N, P.nu x * P.nu (x + h)) - (N:ℝ)
         = ((∑ x : Fin N, P.nu x * P.nu (x + h)) / N - 1) * N := by field_simp
  rw [show correlationSum P.nu h = ∑ x : Fin N, P.nu x * P.nu (x + h) from rfl, e, abs_mul,
      abs_of_nonneg hN]
  exact mul_le_mul_of_nonneg_right (P.correlation_bound h) hN

/-
For a PseudorandomMajorant, the total mass satisfies
    |mass - N| ≤ averageCondition · N.
-/
lemma mass_approx_N {N : ℕ} [NeZero N]
    (P : PseudorandomMajorant N) :
    |(∑ x : Fin N, P.nu x) - N| ≤ P.averageCondition * N := by
  have hN : (0:ℝ) ≤ N := Nat.cast_nonneg N
  have hNe : (N:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have e : (∑ x : Fin N, P.nu x) - (N:ℝ) = ((∑ x : Fin N, P.nu x) / N - 1) * N := by field_simp
  rw [e, abs_mul, abs_of_nonneg hN]
  exact mul_le_mul_of_nonneg_right P.havg hN

/-
The additive energy equals the sum of squared correlation sums:
    E(ν) = Σ_h (correlationSum ν h)².
    This is because E(ν) = Σ_x (Σ_a ν(a)ν(x-a))² and by change of variables
    the convolution at x equals correlationSum at the appropriate shift.
-/
lemma additiveEnergy_eq_sum_correlationSq {N : ℕ} [NeZero N] (f : Fin N → ℝ) :
    additiveEnergy' f = ∑ h : Fin N, (correlationSum f h) ^ 2 := by
  unfold additiveEnergy' correlationSum; ring_nf;
  simp +decide only [sq, sum_mul _ _ _, mul_sum, sum_sigma'];
  refine' Finset.sum_bij ( fun x hx => ⟨ x.fst - x.snd.fst - x.snd.snd, x.snd.snd, x.snd.fst ⟩ ) _ _ _ _ <;> simp +decide;
  · aesop;
  · intro b; use b.1 + b.2.1 + b.2.2, b.2.2, b.2.1; aesop;
  · grind

/-
**Correlation-enhanced additive energy lower bound.**
    For a `StrongPseudorandomMajorant` with 2-point correlationError ε
    and averageCondition δ (with ε < 1/2 and δ < 1/4):
      E(ν) ≥ N³ · (1 - 2ε - 4δ)

    Proof sketch:
    1. E(ν) = Σ_h g(h)² where g(h) = Σ_x ν(x)ν(x+h)  [additiveEnergy_eq_sum_correlationSq]
    2. Cauchy-Schwarz: Σ g(h)² ≥ (Σ g(h))²/N           [sum_sq_ge_sq_div]
    3. Σ g(h) = mass² ≥ N²(1-δ)² ≥ N²(1-2δ)            [correlationSum_total_eq_sq, mass_approx_N]
    4. So E(ν) ≥ N⁴(1-2δ)²/N = N³(1-2δ)² ≥ N³(1-4δ)
    5. The correlationError bound gives the -2ε term.
-/
theorem correlation_additive_energy_lower {N : ℕ} [NeZero N]
    (P : PseudorandomMajorant.StrongPseudorandomMajorant N)
    (hN : (0 : ℝ) < N)
    (hε : P.correlationError < 1 / 2)
    (_hδ : P.averageCondition < 1 / 4) :
    additiveEnergy' P.nu ≥ (N : ℝ) ^ 3 * (1 - 2 * P.correlationError - 4 * P.averageCondition) := by
  -- By correlation_bound: g(h) ≥ N - εN for all h
  have h_g_ge : ∀ h : Fin N, correlationSum P.nu h ≥ N - P.correlationError * N := by
    exact fun h => by linarith [ abs_le.mp ( correlation_sum_approx_N P h ) ] ;
  -- Therefore, Σ_h g(h)² ≥ N · (N - εN)² = N³(1 - ε)²
  have h_sum_ge : ∑ h : Fin N, (correlationSum P.nu h) ^ 2 ≥ N * (N - P.correlationError * N) ^ 2 := by
    exact le_trans ( by norm_num ) ( Finset.sum_le_sum fun i _ => pow_le_pow_left₀ ( by nlinarith [ show ( P.correlationError : ℝ ) ≥ 0 from P.hcorr_pos ] ) ( h_g_ge i ) 2 );
  rw [ additiveEnergy_eq_sum_correlationSq ];
  nlinarith [ show ( N : ℝ ) ^ 3 > 0 by positivity, show ( N : ℝ ) ^ 2 * P.correlationError ≥ 0 by exact mul_nonneg ( sq_nonneg _ ) ( show 0 ≤ P.correlationError by exact P.hcorr_pos ), show ( N : ℝ ) ^ 2 * P.averageCondition ≥ 0 by exact mul_nonneg ( sq_nonneg _ ) ( show 0 ≤ P.averageCondition by exact le_trans ( abs_nonneg _ ) P.havg ) ]

end
