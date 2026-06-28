/-
# Sieve.SelbergRestriction

Section E: Explicit restriction lower bounds for the Selberg sieve majorant.

Connects the abstract restriction lower bound (RestrictionLowerBound.lean)
with the concrete Selberg-shaped majorant (SelbergComparison.lean).

Main theorems:
  1. sieveMajorant_l2NormSq_explicit: exact L² norm of the Selberg majorant (alternate form)
  2. sieveMajorant_l2NormSq_eq_selbergForm_explicit: L²/N = Selberg quadratic form (alternate form)
  3. selberg_restriction_lower_bound_explicit: end-to-end bound in (d, m)
  4. selberg_additive_energy_explicit: additive energy lower bound in (d, m)

Note: `sieveMajorant_targetMass` is imported from SelbergComparison.lean.
      `sieveMajorant_l2NormSq` and `sieveMajorant_l2NormSq_eq_selbergForm` are
      imported from Weights.FourierConnection. The versions here use an alternate
      normal form (m/4 + (d*m - m) vs d*m - 3m/4) which equals the FourierConnection
      version by `ring`.

Status: ProvedInProject
-/
import Mathlib
import RequestProject.Core.Majorant
import RequestProject.Core.RestrictionLowerBound
import RequestProject.Core.SelbergComparison
import RequestProject.Core.Weights.FourierConnection

open Finset BigOperators

noncomputable section

/-! ## Helper: positivity for d*m -/

private lemma dm_pos' (hd : 2 ≤ d) (hm : 1 ≤ m) : 0 < d * m := by positivity

/-! ## Theorem 1: L² norm squared (alternate form) -/

/-
The L² norm squared of the sieve majorant (alternate normal form):
    ‖ν‖₂² = m/4 + (d*m - m)
This equals the FourierConnection version (d*m - 3m/4) by ring.
-/
theorem sieveMajorant_l2NormSq_explicit (d m : ℕ) (hd : 0 < d) (hN : 0 < d * m) :
    (sieveMajorant d m hN).l2NormSq =
      (m : ℝ) / 4 + (d * m - m : ℕ) := by
  -- Apply the definition of l2NormSq and split the sum into multiples and non-multiples.
  have h_split : (sieveMajorant d m hN).l2NormSq = ∑ x ∈ multiplesInFin d m, (sieveMajorantFun d (d * m) x)^2 + ∑ x ∈ nonMultiplesInFin d m, (sieveMajorantFun d (d * m) x)^2 := by
    convert Finset.sum_union ( multiples_disjoint_nonMultiples d m ) using 1;
    rw [ multiples_union_nonMultiples ];
    rfl;
  -- On multiples: sieveMajorantFun = 1/2, so each term is (1/2)^2 = 1/4. Sum = m * (1/4) = m/4 using card_multiplesInFin.
  have h_multiples : ∑ x ∈ multiplesInFin d m, (sieveMajorantFun d (d * m) x)^2 = (m : ℝ) / 4 := by
    rw [ Finset.sum_congr rfl fun x hx => by rw [ show sieveMajorantFun d ( d * m ) x = 1 / 2 from if_pos <| Finset.mem_filter.mp hx |>.2 ] ] ; norm_num [ card_multiplesInFin d m hd ] ; ring
  rw [h_split, h_multiples];
  rw [ Finset.sum_congr rfl fun x hx => by rw [ show sieveMajorantFun d ( d * m ) x = 1 by exact if_neg <| Finset.mem_filter.mp hx |>.2 ] ] ; norm_num [ card_nonMultiplesInFin d m hd ]

/-! ## Theorem 2: L² norm as Selberg quadratic form (alternate form) -/

/-
The L² norm of the sieve majorant equals N times the Selberg quadratic form:
    ‖ν‖₂² = (d*m) · (1 - 3/(4d))
-/
theorem sieveMajorant_l2NormSq_eq_selbergForm_explicit (d m : ℕ) (hd : 0 < d) (hN : 0 < d * m) :
    (sieveMajorant d m hN).l2NormSq =
      (d * m : ℝ) * (1 - 3 / (4 * d)) := by
  convert sieveMajorant_l2NormSq_explicit d m hd hN using 1 ; ring_nf;
  rw [ Nat.cast_sub ] <;> push_cast <;> nlinarith [ mul_inv_cancel_left₀ ( by positivity : ( d : ℝ ) ≠ 0 ) m ]

/-! ## Theorem 3: End-to-end restriction lower bound -/

/-
**Main Section E theorem**: Explicit restriction lower bound for the Selberg
    sieve majorant, stated purely in arithmetic parameters (d, m).

    mass(ν)² · ‖ν‖₂² ≥ ((d*m - m))⁴ / (d*m)

    This combines the abstract restriction_lower_bound with the concrete
    sieve majorant from SelbergComparison.lean.
-/
theorem selberg_restriction_lower_bound_explicit
    (d m : ℕ) (hd : 2 ≤ d) (hm : 1 ≤ m) :
    let hN := dm_pos' hd hm
    let M := sieveMajorant d m hN
    M.mass ^ 2 * M.l2NormSq ≥
      ((d * m - m : ℕ) : ℝ) ^ 4 / (d * m) := by
  convert restriction_lower_bound _ _ using 3;
  · exact_mod_cast Eq.symm ( sieveMajorant_targetMass d m ( by linarith ) ( by nlinarith ) );
  · norm_cast;
  · positivity

/-! ## Theorem 4: Additive energy lower bound in (d, m) -/

/-
Additive energy lower bound for the Selberg sieve majorant:
    E(ν) ≥ ((d*m - m))⁴ / (d*m)³
-/
theorem selberg_additive_energy_explicit
    (d m : ℕ) (hd : 2 ≤ d) (hm : 1 ≤ m) :
    let hN := dm_pos' hd hm
    let M := sieveMajorant d m hN
    @additiveEnergy' (d * m) ⟨by omega⟩ M.nu ≥
      ((d * m - m : ℕ) : ℝ) ^ 4 / (d * m) ^ 3 := by
  convert sieve_additive_energy_lower ( sieveMajorant d m ( dm_pos' hd hm ) ) ?_ using 1;
  · rw [ sieveMajorant_targetMass d m ( by positivity ) ( by positivity ) ] ; norm_cast;
  · positivity

/-- **The three constraints are simultaneously active on the Selberg majorant.**
    The mass-energy product lies strictly between the restriction lower bound
    and the baseline upper bound. This is the central claim of Section 6. -/
theorem selberg_mass_energy_interval (d m : ℕ) (hd : 2 ≤ d) (hm : 1 ≤ m) :
    let hN := show 0 < d * m by positivity
    let M := sieveMajorant d m hN
    ((d * m - m : ℕ) : ℝ) ^ 4 / (d * m) ≤ M.mass ^ 2 * M.l2NormSq
    ∧ M.mass ^ 2 * M.l2NormSq < (d * m : ℝ) ^ 3 := by
  constructor
  · exact selberg_restriction_lower_bound_explicit d m hd hm
  · have hN : 0 < d * m := by positivity
    have hmass := sieveMajorant_mass d m (by omega) hN
    have hl2 := sieveMajorant_l2NormSq d m hd hm hN
    have hm_pos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have hd_pos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    have h1 : (sieveMajorant d m hN).mass ^ 2 * (sieveMajorant d m hN).l2NormSq
            = (↑d * ↑m - ↑m / 2) ^ 2 * (↑d * ↑m - 3 * ↑m / 4) := by
      rw [hmass, hl2]
    rw [h1]
    nlinarith [sq_nonneg ((d : ℝ) * m - m / 2),
               mul_pos hd_pos hm_pos,
               mul_pos (mul_pos hd_pos hm_pos) hm_pos,
               mul_pos (mul_pos hd_pos hd_pos) (mul_pos hm_pos hm_pos),
               sq_nonneg ((d : ℝ) * m),
               sq_nonneg (m : ℝ),
               mul_pos hd_pos (mul_pos hd_pos hm_pos)]

end
