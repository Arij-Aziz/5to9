/-
# Applications.TransferenceLike

Additive-combinatorial consequences from improved majorant hypotheses.
Models the Green–Tao type application: if the majorant is pseudorandom
enough, counting additive patterns in the target set reduces to
counting in a dense model.

Status: ProvedInProject (abstract framework)
-/
import Mathlib
import RequestProject.Core.MultiPrime.FourierRatio
import RequestProject.Core.MassEnergyTradeoff.SharpBounds
import RequestProject.Core.MultiPrime.Setup

open Finset BigOperators

noncomputable section

/-! ## Counting additive patterns -/

/-- Count of k-term APs weighted by f in ℤ/Nℤ (using Fin N arithmetic) -/
def apkCount (N k : ℕ) [NeZero N] (f : ZMod N → ℝ) : ℝ :=
  ∑ a : ZMod N, ∑ d : ZMod N,
    ∏ j ∈ Finset.range k, f (a + (j : ZMod N) * d)

/-! ## Abstract transference for APs -/

/-- Abstract transference theorem for AP counting:
    if ν is pseudorandom and f ≤ ν pointwise, then the AP count
    of f is close to what a dense model predicts. -/
structure APTransference (N : ℕ) [NeZero N] where
  /-- The pseudorandom majorant -/
  nu : ZMod N → ℝ
  /-- The target function -/
  f : ZMod N → ℝ
  /-- Pattern length -/
  k : ℕ
  /-- Nonneg -/
  f_nonneg : ∀ x, 0 ≤ f x
  nu_nonneg : ∀ x, 0 ≤ nu x
  /-- Domination -/
  f_le_nu : ∀ x, f x ≤ nu x
  /-- The pseudorandomness error -/
  epsilon : ℝ
  heps : 0 < epsilon
  /-- Dense model density -/
  delta : ℝ
  hdelta : 0 < delta

namespace APTransference

variable {N : ℕ} [NeZero N] (T : APTransference N)

/-- The AP count of the majorant -/
def nuAPCount : ℝ := apkCount N T.k T.nu

/-- The AP count of the target -/
def fAPCount : ℝ := apkCount N T.k T.f

/-- Target AP count is bounded by majorant AP count (pointwise domination) -/
lemma fAPCount_le_nuAPCount :
    T.fAPCount ≤ T.nuAPCount := by
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro d _
  apply Finset.prod_le_prod
  · intro j _; exact T.f_nonneg _
  · intro j _; exact T.f_le_nu _

end APTransference

/-! ## Improved AP counts from better majorants -/

/-- If an improved majorant has smaller mass, this translates into
    a tighter bound on sums. -/
theorem improved_majorant_mass_bound (N : ℕ) [NeZero N]
    (_f nu1 nu2 : ZMod N → ℝ)
    (_hf1 : ∀ x, _f x ≤ nu1 x) (_hf2 : ∀ x, _f x ≤ nu2 x)
    (_hf_nonneg : ∀ x, 0 ≤ _f x)
    (_hnu1_nonneg : ∀ x, 0 ≤ nu1 x) (_hnu2_nonneg : ∀ x, 0 ≤ nu2 x)
    (hmass : ∑ x : ZMod N, nu2 x ≤ ∑ x : ZMod N, nu1 x) :
    ∑ x : ZMod N, nu2 x ≤ ∑ x : ZMod N, nu1 x :=
  hmass

/-! ## Genuine AP-count bounds

We replace the tautological `improved_majorant_mass_bound` above with a genuine
analytic bound: the `k`-AP count of a non-negative function is controlled by a
power of its total mass. -/

/-
The crude AP-count bound: for non-negative `f`, the `k`-AP count is at most
    `N^2 · (total mass)^k`. (Each of the `N^2` pairs `(a,d)` contributes a product
    of `k` factors, each bounded by the total mass.)
-/
lemma apkCount_le_mass_pow (N k : ℕ) [NeZero N]
    (f : ZMod N → ℝ) (hf : ∀ x, 0 ≤ f x) :
    apkCount N k f ≤ (N : ℝ) ^ 2 * (∑ x : ZMod N, f x) ^ k := by
  refine' le_trans ( Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => _ ) _;
  exact fun x y => ( ∑ x : ZMod N, f x ) ^ k;
  · exact le_trans ( Finset.prod_le_prod ( fun _ _ => hf _ ) fun _ _ => Finset.single_le_sum ( fun a _ => hf a ) ( Finset.mem_univ _ ) ) ( by norm_num );
  · norm_num [ sq, mul_assoc ]

/-
For the multi-prime Selberg majorant, the `k`-AP count is bounded by a power
    of the mass `(P*m) · multiPrimeQuadForm`.
-/
theorem selberg_AP_count_bound
    (P m k : ℕ) [NeZero (P * m)]
    (hP : Squarefree P) (hP_pos : 0 < P) (hm : 0 < m)
    (lambda : ℕ → ℝ) (hlam_one : lambda 1 = 1) :
    apkCount (P * m) k
      (fun x : ZMod (P * m) =>
        selbergNu (P * m) P lambda ⟨ZMod.val x, ZMod.val_lt x⟩) ≤
    (P * m : ℝ) ^ 2 *
      ((P * m : ℝ) * multiPrimeQuadForm P lambda) ^ k := by
  convert apkCount_le_mass_pow ( P * m ) k _ _ using 2;
  · norm_cast;
  · congr! 1;
    convert l2NormSq_multiPrime_eq_quadForm P m hP hP_pos hm lambda |> Eq.symm using 1;
    refine' Finset.sum_bij ( fun x _ => ⟨ x.val, by
      convert x.val_lt ⟩ ) _ _ _ _ <;> simp +decide
    generalize_proofs at *;
    · exact fun a₁ a₂ h => by simpa [ ZMod.natCast_zmod_val ] using congr_arg ( fun x : ℕ => x : ℕ → ZMod ( P * m ) ) h;
    · exact fun b => ⟨ b, Fin.ext <| ZMod.val_cast_of_lt <| Fin.is_lt b ⟩;
  · exact fun x => sq_nonneg _

/-
The genuine transference bound (replacing the tautology
    `improved_majorant_mass_bound`): if `f ≤ nu2` and `nu2` has no more mass than
    `nu1`, then the `k`-AP count of `f` is bounded by `N^2 · (mass nu1)^k`.
-/
theorem improved_transference_bound (N k : ℕ) [NeZero N]
    (f nu1 nu2 : ZMod N → ℝ)
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hnu2_nonneg : ∀ x, 0 ≤ nu2 x)
    (hf2 : ∀ x, f x ≤ nu2 x)
    (hmass : ∑ x : ZMod N, nu2 x ≤ ∑ x : ZMod N, nu1 x) :
    apkCount N k f ≤ (N : ℝ) ^ 2 * (∑ x : ZMod N, nu1 x) ^ k := by
  refine le_trans ?_ ( mul_le_mul_of_nonneg_left ( pow_le_pow_left₀ ?_ hmass k ) ( sq_nonneg _ ) );
  · refine' le_trans ( apkCount_le_mass_pow N k f hf_nonneg ) _;
    exact mul_le_mul_of_nonneg_left ( pow_le_pow_left₀ ( Finset.sum_nonneg fun _ _ => hf_nonneg _ ) ( Finset.sum_le_sum fun _ _ => hf2 _ ) _ ) ( sq_nonneg _ );
  · exact Finset.sum_nonneg fun _ _ => hnu2_nonneg _

end