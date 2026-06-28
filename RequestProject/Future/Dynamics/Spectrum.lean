/-
# Dynamics.Spectrum

Ergodic rotations, observable averages, and spectral packaging
for sieve-state dynamics.

Status: ProvedInProject (definitions and basic spectral properties)
-/
import Mathlib
import RequestProject.Core.MultiPrime.FourierRatio
import RequestProject.Core.MultiPrime.L2Identity

open Finset BigOperators Complex

noncomputable section

/-! ## Characters on ZMod m -/

/-- A multiplicative character on ZMod m via exponential map. -/
def additiveChar' (m : ℕ) [NeZero m] (k : ZMod m) : ZMod m → ℂ :=
  fun x => Complex.exp (2 * Real.pi * Complex.I * (ZMod.val x * ZMod.val k : ℝ) / m)

/-- Character at k=0 is identically 1 -/
lemma additiveChar'_zero (m : ℕ) [NeZero m] :
    additiveChar' m 0 = fun _ => 1 := by
  ext x
  simp [additiveChar', ZMod.val_zero]

/-! ## Spectral decomposition of observables -/

/-- Fourier coefficient of an observable at character k -/
def fourierCoeff' (m : ℕ) [NeZero m] (obs : ZMod m → ℝ) (k : ZMod m) : ℂ :=
  ∑ x : ZMod m, (obs x : ℂ) * starRingEnd ℂ (additiveChar' m k x)

/-- An observable is spectrally concentrated at a set of characters
    if most of its L² energy is captured by those characters. -/
def spectrallyConcentrated (m : ℕ) [NeZero m] (obs : ZMod m → ℝ)
    (S : Finset (ZMod m)) (eta : ℝ) : Prop :=
  ∑ k ∈ Finset.univ \ S, ‖fourierCoeff' m obs k‖ ^ 2 ≤ eta * (m : ℝ) ^ 2

/-! ## Ergodic averages -/

/-- The time average of an observable along an orbit -/
def orbitAverage (m : ℕ) [NeZero m] (obs : ZMod m → ℝ) (x₀ : ZMod m)
    (T : ℕ) : ℝ :=
  (∑ t ∈ Finset.range T, obs (x₀ + (t : ZMod m))) / T

/-- The space average of an observable -/
def spaceAverage (m : ℕ) [NeZero m] (obs : ZMod m → ℝ) : ℝ :=
  (∑ x : ZMod m, obs x) / m

/-
For a full orbit (T = m), orbit average equals space average
-/
lemma orbit_avg_eq_space_avg (m : ℕ) [hm : NeZero m]
    (obs : ZMod m → ℝ) (x₀ : ZMod m) :
    orbitAverage m obs x₀ m = spaceAverage m obs := by
  unfold orbitAverage spaceAverage
  congr 1
  rw [← Equiv.sum_comp (Equiv.addLeft x₀) obs]
  refine Finset.sum_nbij' (i := fun t => (t : ZMod m)) (j := fun x => x.val)
    ?_ ?_ ?_ ?_ ?_
  · intro a ha; simp
  · intro a ha; simp [ZMod.val_lt]
  · intro a ha; simp [Nat.mod_eq_of_lt (Finset.mem_range.mp ha), ZMod.val_natCast]
  · intro a ha; simp
  · intro a ha; rfl

/-! ## Spectral gap and mixing -/

/-- Spectral gap: the largest nontrivial Fourier coefficient is small. -/
def hasSpectralGap (m : ℕ) [NeZero m] (obs : ZMod m → ℝ) (gap : ℝ) : Prop :=
  ∀ k : ZMod m, k ≠ 0 → ‖fourierCoeff' m obs k‖ ≤ gap

/-- Mixing rate: largest nontrivial Fourier coefficient normalized -/
def mixingRate (m : ℕ) [NeZero m] (obs : ZMod m → ℝ) : ℝ :=
  Finset.univ.sup' ⟨(0 : ZMod m), Finset.mem_univ _⟩
    (fun k => if k = (0 : ZMod m) then 0 else ‖fourierCoeff' m obs k‖ / m)

/-! ## Bridge to the multi-prime quadratic form

These results connect the spectral / Fourier layer (over `ZMod m`) to the
number-theoretic object `multiPrimeQuadForm`. -/

/-
Summing a function of `Fin n` along the canonical `ZMod.val` identification
    of `ZMod n` with `Fin n` agrees with the direct sum over `Fin n`.
-/
lemma zmod_sum_eq_fin_sum (n : ℕ) [NeZero n] (f : Fin n → ℝ) :
    ∑ x : ZMod n, f ⟨ZMod.val x, ZMod.val_lt x⟩ = ∑ y : Fin n, f y := by
  convert Finset.sum_congr rfl fun x hx => ?_;
  rotate_left;
  exact fun x => f ⟨ x.val, ZMod.val_lt x ⟩;
  · rfl;
  · rcases n with ( _ | _ | n ) <;> norm_cast;
    exact False.elim <| NeZero.ne 0 rfl

/-
The space average of the multi-prime Selberg majorant, viewed as an
    observable on `ZMod (P*m)`, equals the quadratic form `multiPrimeQuadForm`.
-/
lemma selberg_spaceAverage_eq_quadForm
    (P m : ℕ) [NeZero (P * m)]
    (hP : Squarefree P) (hP_pos : 0 < P) (hm : 0 < m)
    (lambda : ℕ → ℝ) :
    spaceAverage (P * m)
      (fun x : ZMod (P * m) => selbergNu (P * m) P lambda ⟨ZMod.val x, ZMod.val_lt x⟩) =
    multiPrimeQuadForm P lambda := by
  unfold spaceAverage;
  rw [ div_eq_iff ] <;> norm_cast <;> norm_num;
  · convert l2NormSq_multiPrime_eq_quadForm P m hP hP_pos hm lambda using 1;
    · convert zmod_sum_eq_fin_sum ( P * m ) _;
    · ring;
  · aesop

/-- The zeroth Fourier coefficient (total mass) of `selbergNu`, viewed as a
    complex observable on `ZMod (P*m)`, has real part `(P*m) · multiPrimeQuadForm`.

    The hypothesis `hlam_one` (`λ₁ = 1`) is requested by the blueprint signature
    but turns out to be unnecessary for this mass identity. -/
theorem selbergNu_fourier_zero_eq_quadForm
    (P m : ℕ) [NeZero (P * m)]
    (hP : Squarefree P) (hP_pos : 0 < P) (hm : 0 < m)
    (lambda : ℕ → ℝ) (hlam_one : lambda 1 = 1) :
    Complex.re
      (fourierCoeff' (P * m)
        (fun x => selbergNu (P * m) P lambda ⟨ZMod.val x, ZMod.val_lt x⟩)
        0) =
    (P * m : ℝ) * multiPrimeQuadForm P lambda := by
  unfold fourierCoeff' additiveChar' ;
  simp +decide [ mul_comm ];
  convert l2NormSq_multiPrime_eq_quadForm P m hP hP_pos hm lambda using 1;
  · convert zmod_sum_eq_fin_sum ( P * m ) _;
  · ring

/-
A spectral gap for the `selbergNu` observable bounds the mixing rate.
-/
lemma selberg_hasSpectralGap_implies_mixingRate
    (P m : ℕ) [NeZero (P * m)]
    (lambda : ℕ → ℝ) (gap : ℝ) (hgap : 0 < gap)
    (hsg : hasSpectralGap (P * m)
      (fun x => selbergNu (P * m) P lambda ⟨ZMod.val x, ZMod.val_lt x⟩) gap) :
    mixingRate (P * m)
      (fun x => selbergNu (P * m) P lambda ⟨ZMod.val x, ZMod.val_lt x⟩) ≤ gap / (P * m) := by
  unfold mixingRate;
  simp +zetaDelta at *;
  intro k; split_ifs <;> [ norm_num; exact div_le_div_of_nonneg_right ( hsg k ‹_› ) ( by positivity ) ] ;
  positivity

end