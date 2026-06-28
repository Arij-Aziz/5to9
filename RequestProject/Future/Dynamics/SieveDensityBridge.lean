/-
# Future.Dynamics.SieveDensityBridge

Bridge between SieveState compatibility and density-level bounds.
Moved from Core/KineticPropagation.lean since it depends on Future/ infrastructure.
-/
import Mathlib
import RequestProject.Future.Dynamics.SieveState

open Finset BigOperators Nat

noncomputable section

/-
The compatible projection property of SieveState implies an inequality
    on localDensityFactor for coprime moduli. This connects the set-level
    compatibility (SieveState.compatible) to density-level bounds.
-/
theorem sieveState_densityFactor_compat (S : SieveState)
    (m n : ℕ) [hm : NeZero m] [hn : NeZero n] [hmn : NeZero (m * n)] :
    (S.admissibleAt (m * n)).card ≤
      (S.admissibleAt m).card * n := by
  have h_compatible : ∀ (x : ZMod (m * n)), x ∈ S.admissibleAt (m * n) → (ZMod.castHom (dvd_mul_right m n) (ZMod m) x) ∈ S.admissibleAt m := by
    exact?;
  have h_fiber : ∀ (y : ZMod m), (Finset.filter (fun x : ZMod (m * n) => ZMod.castHom (dvd_mul_right m n) (ZMod m) x = y) (S.admissibleAt (m * n))).card ≤ n := by
    intro y
    have h_fiber : Finset.card (Finset.filter (fun x : ZMod (m * n) => ZMod.castHom (dvd_mul_right m n) (ZMod m) x = y) (Finset.univ : Finset (ZMod (m * n)))) ≤ n := by
      have h_fiber : ∀ (y : ZMod m), (Finset.filter (fun x : ZMod (m * n) => ZMod.castHom (dvd_mul_right m n) (ZMod m) x = y) (Finset.univ : Finset (ZMod (m * n)))).card ≤ n := by
        intro y
        have h_fiber : ∀ (x : ZMod (m * n)), ZMod.castHom (dvd_mul_right m n) (ZMod m) x = y → ∃ k : ℕ, k < n ∧ x = y.val + m * k := by
          intro x hx
          have h_fiber : ∃ k : ℕ, k < n ∧ x.val = y.val + m * k := by
            have h_fiber : x.val % m = y.val % m := by
              simp_all +decide [ ← ZMod.natCast_eq_natCast_iff' ];
            have h_fiber : x.val < m * n ∧ y.val < m := by
              exact ⟨ x.val_lt, y.val_lt ⟩;
            exact ⟨ x.val / m, Nat.div_lt_of_lt_mul <| by linarith, by linarith [ Nat.mod_add_div x.val m, Nat.mod_eq_of_lt h_fiber.2 ] ⟩;
          obtain ⟨ k, hk₁, hk₂ ⟩ := h_fiber; use k; simp_all +decide [ ZMod.natCast_zmod_val ] ;
          rw [ ← ZMod.natCast_zmod_val x ] ; aesop;
        exact le_trans ( Finset.card_le_card ( show Finset.filter ( fun x : ZMod ( m * n ) => ( ZMod.castHom ( dvd_mul_right m n ) ( ZMod m ) ) x = y ) Finset.univ ⊆ Finset.image ( fun k : ℕ => ↑y.val + ↑m * ↑k ) ( Finset.range n ) from fun x hx => by obtain ⟨ k, hk₁, rfl ⟩ := h_fiber x ( Finset.mem_filter.mp hx |>.2 ) ; exact Finset.mem_image.mpr ⟨ k, Finset.mem_range.mpr hk₁, rfl ⟩ ) ) ( Finset.card_image_le.trans ( by simpa ) );
      exact h_fiber y;
    exact le_trans ( Finset.card_le_card fun x hx => by aesop ) h_fiber;
  have h_fiber : (Finset.biUnion (S.admissibleAt m) (fun y => Finset.filter (fun x : ZMod (m * n) => ZMod.castHom (dvd_mul_right m n) (ZMod m) x = y) (S.admissibleAt (m * n)))).card ≤ (S.admissibleAt m).card * n := by
    exact le_trans ( Finset.card_biUnion_le ) ( Finset.sum_le_card_nsmul _ _ _ fun x hx => h_fiber x );
  convert h_fiber using 2 ; ext x ; aesop

end
