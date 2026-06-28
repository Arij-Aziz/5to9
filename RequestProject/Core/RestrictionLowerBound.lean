/-
# Sieve.RestrictionLowerBound

Restriction lower bound for Selberg majorants.

Any nonneg majorant ν dominating a sifted indicator 1_S on Fin N satisfies
  mass(ν)² · ‖ν‖₂² ≥ |S|⁴ / N

This is complementary to the Green-Tao restriction upper bound theory:
once a majorant dominates a sifted set of size |S|, some amount of
Fourier/spatial energy is unavoidable.

The proof proceeds by:
  1. Cauchy-Schwarz on Fin N: (Σ ν(x))² ≤ N · Σ ν(x)²
  2. Rearranging and multiplying by mass²
  3. Using mass_ge_targetMass to replace mass by |S|

We also provide a Fourier reformulation via Parseval,
additive energy lower bounds, and Selberg-specific corollaries.

Status: ProvedInProject
-/
import Mathlib
import RequestProject.Core.Majorant
import RequestProject.Core.Fourier

open Finset BigOperators

noncomputable section

/-! ## Section A & B: Generic Cauchy-Schwarz and mass-energy inequality -/

/-- Generic Cauchy-Schwarz on Fin N: (Σ f(x))² ≤ N · Σ f(x)².
    This is the finite-dimensional Cauchy-Schwarz inequality with
    the constant function 1. -/
theorem fin_cauchy_schwarz {N : ℕ} (f : Fin N → ℝ) :
    (∑ x : Fin N, f x) ^ 2 ≤ N * (∑ x : Fin N, f x ^ 2) := by
  have h_cauchy_schwarz : ∀ (u v : Fin N → ℝ), (∑ i, u i * v i) ^ 2 ≤ (∑ i, u i ^ 2) * (∑ i, v i ^ 2) := by
    exact fun u v => sum_mul_sq_le_sq_mul_sq univ u v
  simpa using h_cauchy_schwarz 1 f

/-- For nonneg functions: mass² ≤ N · l2NormSq. -/
lemma mass_sq_le_card_mul_l2NormSq {N : ℕ} (M : Majorant N) :
    M.mass ^ 2 ≤ N * M.l2NormSq := by
  exact fin_cauchy_schwarz M.nu

/-- The mass-energy lower bound:
    mass² · l2NormSq ≥ mass⁴ / N -/
theorem mass_energy_lower_bound {N : ℕ} (M : Majorant N) (hN : (0 : ℝ) < N) :
    M.mass ^ 2 * M.l2NormSq ≥ M.mass ^ 4 / N := by
  rw [ge_iff_le, div_le_iff₀' hN]; nlinarith [mass_sq_le_card_mul_l2NormSq M]

/-! ## Section C: The restriction lower bound with sifted cardinality -/

/-- **Restriction lower bound for majorants**.
    Any nonneg majorant ν dominating a target indicator satisfies:
      mass(ν)² · ‖ν‖₂² ≥ targetMass⁴ / N

    This is the core sieve restriction lower bound:
    once ν dominates a set of size |S|, it cannot simultaneously
    have small mass and small L² energy. -/
theorem restriction_lower_bound {N : ℕ} (M : Majorant N) (hN : (0 : ℝ) < N) :
    M.mass ^ 2 * M.l2NormSq ≥ M.targetMass ^ 4 / N := by
  refine' le_trans _ (mass_energy_lower_bound M hN);
  gcongr;
  · exact Finset.sum_nonneg fun _ _ => M.target_nonneg _;
  · exact Majorant.mass_ge_targetMass M

/-- Corollary: l2NormSq ≥ targetMass² / N when mass = targetMass (tight majorant). -/
theorem tight_majorant_l2_lower {N : ℕ} (M : Majorant N) (hN : (0 : ℝ) < N)
    (htight : M.mass = M.targetMass) :
    M.l2NormSq ≥ M.targetMass ^ 2 / N := by
  rw [← htight, ge_iff_le, div_le_iff₀'] <;>
    first | positivity | simpa [← sq] using mass_sq_le_card_mul_l2NormSq M;

/-! ## Section D: Fourier reformulation -/

/-- The zero Fourier coefficient of ν equals the mass (as a complex number). -/
lemma dft_zero_eq_mass {N : ℕ} [NeZero N] (M : Majorant N) :
    realDft' N M.nu ⟨0, NeZero.pos N⟩ = (M.mass : ℂ) := by
  unfold realDft' dft' realToComplex' Majorant.mass; norm_num;

/-- Fourier energy reformulation of the restriction lower bound.
    Expressed using Parseval: the total Fourier energy ‖ν̂‖₂² = N · ‖ν‖₂²,
    so the zero-mode contribution |ν̂(0)|² = mass² satisfies:
      |ν̂(0)|⁴ ≤ N · mass² · ‖ν̂‖₂²
    which is the Fourier restriction lower bound. -/
theorem restriction_lower_bound_zero_mode {N : ℕ} [NeZero N] (M : Majorant N)
    (hN : (0 : ℝ) < N) :
    M.targetMass ^ 4 ≤ N * (M.mass ^ 2) *
      (dftL2NormSq' N (realToComplex' N M.nu) / N) := by
  have h_restrict : M.mass ^ 2 * (dftL2NormSq' N (realToComplex' N M.nu) / N) ≥
      M.targetMass ^ 4 / N := by
    have := @restriction_lower_bound N M;
    convert this hN using 1;
    rw [parseval'];
    unfold l2NormSq' realToComplex' Majorant.l2NormSq;
    norm_num [mul_div_cancel_left₀, hN.ne'];
  rw [ge_iff_le, div_le_iff₀] at h_restrict <;> linarith

/-! ## Section E: Additive energy lower bound -/

/-- Additive energy of a function on Fin N:
    E(ν) = Σ_{x,y,z,w : x+y=z+w} ν(x)ν(y)ν(z)ν(w)
    Computed as Σ_x (Σ_a ν(a)ν(x-a))². -/
def additiveEnergy' {N : ℕ} [NeZero N] (f : Fin N → ℝ) : ℝ :=
  ∑ x : Fin N, (∑ a : Fin N, f a * f (x - a)) ^ 2

/-- Additive energy is nonneg -/
lemma additiveEnergy'_nonneg {N : ℕ} [NeZero N] (f : Fin N → ℝ) :
    0 ≤ additiveEnergy' f :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- The L² norm squared, defined as a real number sum of squares. -/
def l2NormSq_real {N : ℕ} (f : Fin N → ℝ) : ℝ :=
  ∑ x : Fin N, f x ^ 2

/-
The convolution sum identity: Σ_x (Σ_a f(a)f(x-a)) = (Σ f)².
-/
lemma convolution_sum_eq_sq {N : ℕ} [NeZero N] (f : Fin N → ℝ) :
    ∑ x : Fin N, (∑ a : Fin N, f a * f (x - a)) = (∑ x : Fin N, f x) ^ 2 := by
  rw [ sq, Finset.sum_comm ];
  simp +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ];
  rw [ Finset.sum_mul _ _ _ ];
  exact Finset.sum_congr rfl fun i hi => by rw [ show ∑ x : Fin N, f ( x - i ) = ∑ x : Fin N, f x from Equiv.sum_comp ( Equiv.subRight i ) _ ] ;

/-
For nonneg f: (Σ f)² ≥ Σ f². This holds because (Σ f)² = Σ f² + 2·Σ_{i<j} f(i)f(j)
    and all cross terms are nonneg.
-/
lemma sum_sq_ge_sq_sum {N : ℕ} (f : Fin N → ℝ) (hf : ∀ x, 0 ≤ f x) :
    (∑ x : Fin N, f x) ^ 2 ≥ ∑ x : Fin N, f x ^ 2 := by
  simpa only [ sq, Finset.sum_mul ] using Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ( Finset.single_le_sum ( fun i _ => hf i ) ( Finset.mem_univ i ) ) ( hf i )

/-
Additive energy lower bound via Cauchy-Schwarz (for nonneg functions):
    E(ν) ≥ (Σ ν(x)²)² / N

    Proof: By Cauchy-Schwarz, E ≥ (Σ_x g(x))²/N where g(x) = Σ_a f(a)f(x-a).
    The convolution sum identity gives Σ g(x) = (Σ f)².
    So E ≥ (Σ f)⁴/N. For nonneg f, (Σ f)² ≥ Σ f²,
    hence (Σ f)⁴ ≥ (Σ f²)² and E ≥ (Σ f²)²/N.
-/
theorem additiveEnergy_lower_bound {N : ℕ} [NeZero N] (f : Fin N → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hN : (0 : ℝ) < N) :
    additiveEnergy' f ≥ (l2NormSq_real f) ^ 2 / N := by
  have h_cauchy_schwarz : (Finset.sum Finset.univ (fun x => (Finset.sum Finset.univ (fun a => f a * f (x - a))) ^ 2)) * N ≥ (Finset.sum Finset.univ (fun x => (Finset.sum Finset.univ (fun a => f a * f (x - a))))) ^ 2 := by
    have := @fin_cauchy_schwarz N ( fun x => ∑ a, f a * f ( x - a ) );
    linarith;
  rw [ ge_iff_le, div_le_iff₀ ] <;> try positivity;
  refine le_trans ?_ h_cauchy_schwarz;
  apply pow_le_pow_left₀ ( Finset.sum_nonneg fun _ _ => sq_nonneg _ )
  calc l2NormSq_real f ≤ (∑ x, f x) ^ 2 := sum_sq_ge_sq_sum f hf
    _ = ∑ x, ∑ a, f a * f (x - a) := (convolution_sum_eq_sq f).symm

/-! ## Section F: Integration with Selberg data -/

/-
For a majorant of a sifted indicator:
    additiveEnergy(ν) ≥ targetMass⁴ / N³

    This follows from:
    1. E(ν) ≥ ‖ν‖₂⁴ / N  (additive energy lower bound)
    2. ‖ν‖₂² ≥ mass² / N  (Cauchy-Schwarz)
    3. mass ≥ targetMass   (domination)
-/
theorem sieve_additive_energy_lower {N : ℕ} [NeZero N] (M : Majorant N)
    (hN : (0 : ℝ) < N) :
    additiveEnergy' M.nu ≥ M.targetMass ^ 4 / N ^ 3 := by
  refine le_trans ?_ ( additiveEnergy_lower_bound M.nu M.nu_nonneg hN );
  have h_l2_norm_sq : M.l2NormSq ≥ M.targetMass ^ 2 / N := by
    have h_l2NormSq_ge_targetMass_sq_div_N : M.l2NormSq ≥ M.mass ^ 2 / N := by
      exact div_le_iff₀' hN |>.2 ( by linarith [ mass_sq_le_card_mul_l2NormSq M ] );
    exact le_trans ( div_le_div_of_nonneg_right ( pow_le_pow_left₀ ( by exact Finset.sum_nonneg fun _ _ => M.target_nonneg _ ) ( M.mass_ge_targetMass ) _ ) hN.le ) h_l2NormSq_ge_targetMass_sq_div_N;
  have h2 : M.targetMass ^ 4 / (N:ℝ) ^ 3 = (M.targetMass ^ 2 / (N:ℝ)) ^ 2 / N := by ring
  rw [h2]
  gcongr
  exact h_l2_norm_sq

end