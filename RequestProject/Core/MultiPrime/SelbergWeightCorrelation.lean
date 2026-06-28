/-
# SelbergWeightCorrelation.lean
The unsquared Selberg weight, coprime-pairs quadratic form, and correlation theorems.

Status: ProvedInProject
-/
import Mathlib
import RequestProject.Core.MultiPrime.MoebiusWeights

open Finset BigOperators Nat

noncomputable section

/-- The multi-prime Selberg weight (unsquared).
    This is the linear sieve weight Σ_{d|gcd(x,P)} λ_d. -/
def selbergWeight (N P : ℕ) (lambda : ℕ → ℝ) (x : Fin N) : ℝ :=
  ∑ d ∈ (sqfDivisors P).filter (fun d => d ∣ Nat.gcd x.val P), lambda d

/-- selbergNu is the square of selbergWeight -/
lemma selbergNu_eq_sq (N P : ℕ) (lambda : ℕ → ℝ) (x : Fin N) :
    selbergNu N P lambda x = selbergWeight N P lambda x ^ 2 := by
  simp only [selbergNu, selbergWeight]

/-- The coprime-pairs quadratic form:
    sum over (d,e) ∈ sqfDivisors P with gcd(d,e) = 1 of λ_d λ_e / (d*e). -/
def coprimePairsQuadForm (P : ℕ) (lambda : ℕ → ℝ) : ℝ :=
  ∑ d ∈ sqfDivisors P, ∑ e ∈ (sqfDivisors P).filter (Nat.Coprime d),
    lambda d * lambda e / (d * e : ℝ)

/-
When gcd(h, P) = 1 and d, e are coprime squarefree divisors of P,
    the count of x ∈ Fin(P*m) with d | gcd(x, P) and e | gcd(x+h, P)
    equals P*m / (d*e).
-/
lemma count_coprime_shifted_multiples_coprime
    (P m : ℕ) (hP : Squarefree P) (hP_pos : 0 < P) (hm : 0 < m)
    (d e : ℕ) (hd : d ∈ sqfDivisors P) (he : e ∈ sqfDivisors P)
    (hde_cop : Nat.Coprime d e)
    (h : ℕ) (hcop : Nat.Coprime h P) :
    (Finset.univ.filter (fun x : Fin (P * m) =>
      d ∣ Nat.gcd x.val P ∧
      e ∣ Nat.gcd ((x.val + h) % (P * m)) P)).card
    = P * m / (d * e) := by
  -- The conditions $d \mid \gcd(x, P)$ and $e \mid \gcd((x + h) \% (P * m), P)$ simplify to $d \mid x$ and $e \mid (x + h)$.
  have h_conditions : ∀ x : Fin (P * m), d ∣ Nat.gcd x.val P ∧ e ∣ Nat.gcd ((x.val + h) % (P * m)) P ↔ d ∣ x.val ∧ e ∣ (x.val + h) % (P * m) := by
    intro x; exact ⟨fun h => by
      exact ⟨ Nat.dvd_trans h.1 ( Nat.gcd_dvd_left _ _ ), Nat.dvd_trans h.2 ( Nat.gcd_dvd_left _ _ ) ⟩, fun h => by
      exact ⟨ Nat.dvd_gcd h.1 ( mem_sqfDivisors.mp hd |>.1 ), Nat.dvd_gcd h.2 ( mem_sqfDivisors.mp he |>.1 ) ⟩⟩;
  -- By the Chinese Remainder Theorem, there exists a unique solution modulo $d * e$ to the system of congruences $x \equiv 0 \pmod{d}$ and $x \equiv -h \pmod{e}$.
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ℕ, x₀ < d * e ∧ x₀ ≡ 0 [MOD d] ∧ x₀ ≡ -h [ZMOD e] := by
    have h_crt : ∃ x₀ : ℕ, x₀ ≡ 0 [MOD d] ∧ x₀ ≡ -h [ZMOD e] := by
      have := Nat.chineseRemainder hde_cop;
      obtain ⟨ k, hk₁, hk₂ ⟩ := this 0 ( Int.toNat ( -h % e ) ) ; use k; simp_all +decide [ ← Int.natCast_modEq_iff ] ;
      simp_all +decide [ Int.ModEq, Int.emod_nonneg _ ( show ( e : ℤ ) ≠ 0 from mod_cast Nat.ne_of_gt ( Nat.pos_of_mem_divisors ( Finset.mem_filter.mp he |>.1 ) ) ) ];
    obtain ⟨ x₀, hx₀₁, hx₀₂ ⟩ := h_crt; exact ⟨ x₀ % ( d * e ), Nat.mod_lt _ ( Nat.mul_pos ( Nat.pos_of_mem_divisors ( Finset.mem_filter.mp hd |>.1 ) ) ( Nat.pos_of_mem_divisors ( Finset.mem_filter.mp he |>.1 ) ) ), by simpa [ Nat.ModEq, Nat.mod_mod ] using hx₀₁, by simpa [ Int.ModEq, Int.emod_eq_emod_iff_emod_sub_eq_zero ] using hx₀₂ ⟩ ;
  -- The set of solutions to the system of congruences is exactly the set of integers $x$ such that $x \equiv x₀ \pmod{d * e}$.
  have h_solutions : ∀ x : Fin (P * m), d ∣ x.val ∧ e ∣ (x.val + h) % (P * m) ↔ x.val ≡ x₀ [MOD d * e] := by
    intro x
    constructor
    intro hx
    have hx_mod : x.val ≡ x₀ [MOD d] ∧ x.val ≡ x₀ [MOD e] := by
      have hx_mod_e : (x.val + h) ≡ 0 [ZMOD e] := by
        rw [ Int.modEq_zero_iff_dvd ];
        norm_cast at *; simp_all +decide [ Nat.dvd_iff_mod_eq_zero ] ;
        rw [ ← Nat.mod_mod_of_dvd _ ( show e ∣ P * m from dvd_mul_of_dvd_left ( by exact Nat.dvd_of_mem_divisors ( Finset.mem_filter.mp he |>.1 ) ) _ ), hx.2 ];
      simp_all +decide [ ← Int.natCast_modEq_iff ];
      exact ⟨ Int.ModEq.trans ( Int.modEq_zero_iff_dvd.mpr <| Int.natCast_dvd_natCast.mpr hx.1 ) hx₀.2.1.symm, Int.ModEq.trans ( Int.modEq_iff_dvd.mpr <| by obtain ⟨ k, hk ⟩ := hx_mod_e.symm.dvd; exact ⟨ -k, by linarith ⟩ ) hx₀.2.2.symm ⟩
    have hx_mod_de : x.val ≡ x₀ [MOD d * e] := by
      rw [ ← Nat.modEq_and_modEq_iff_modEq_mul ] ; tauto;
      assumption
    exact hx_mod_de
    intro hx_mod_de
    have hx_mod : x.val ≡ x₀ [MOD d] ∧ x.val ≡ x₀ [MOD e] := by
      exact ⟨ hx_mod_de.of_dvd <| dvd_mul_right _ _, hx_mod_de.of_dvd <| dvd_mul_left _ _ ⟩
    have hx_div : d ∣ x.val ∧ e ∣ (x.val + h) % (P * m) := by
      have hx_div : d ∣ x.val ∧ e ∣ (x.val + h) := by
        simp_all +decide [ ← Int.natCast_dvd_natCast, ← ZMod.intCast_zmod_eq_zero_iff_dvd, ← ZMod.natCast_eq_natCast_iff ];
        simp_all +decide [ ← ZMod.intCast_eq_intCast_iff ];
      exact ⟨ hx_div.1, Nat.dvd_of_mod_eq_zero ( by rw [ Nat.mod_mod_of_dvd _ ( show e ∣ P * m from dvd_mul_of_dvd_left ( by exact Nat.dvd_trans ( Nat.dvd_of_mem_divisors ( Finset.mem_filter.mp he |>.1 ) ) ( Nat.dvd_refl _ ) ) _ ) ] ; exact Nat.mod_eq_zero_of_dvd hx_div.2 ) ⟩
    exact hx_div;
  -- The number of solutions to the system of congruences is exactly $P * m / (d * e)$.
  have h_card_solutions : Finset.card (Finset.filter (fun x : ℕ => x ≡ x₀ [MOD d * e]) (Finset.range (P * m))) = P * m / (d * e) := by
    have h_card_solutions : Finset.card (Finset.filter (fun x : ℕ => x ≡ x₀ [MOD d * e]) (Finset.range (d * e * (P * m / (d * e))))) = P * m / (d * e) := by
      rw [ Finset.card_eq_of_bijective ];
      use fun i hi => x₀ + i * ( d * e );
      · simp +zetaDelta at *;
        intro a ha₁ ha₂; use a / ( d * e ) ; exact ⟨ Nat.div_lt_of_lt_mul <| by linarith, by linarith [ Nat.mod_add_div a ( d * e ), show a % ( d * e ) = x₀ from ha₂.symm ▸ Nat.mod_eq_of_lt hx₀.1 ] ⟩ ;
      · simp +decide [ Nat.ModEq, Nat.add_mod, Nat.mul_mod ];
        exact fun i hi => by nlinarith;
      · aesop;
    convert h_card_solutions using 2;
    rw [ Nat.mul_div_cancel' ];
    exact dvd_mul_of_dvd_left ( Nat.Coprime.mul_dvd_of_dvd_of_dvd hde_cop ( mem_sqfDivisors.mp hd |>.1 ) ( mem_sqfDivisors.mp he |>.1 ) ) _;
  rw [ ← h_card_solutions, Finset.card_filter ];
  rw [ Finset.card_filter, Finset.sum_range ] ; aesop

/-
When gcd(h, P) = 1 and d, e share a common prime factor,
    the count is 0.
-/
lemma count_coprime_shifted_multiples_noncoprime
    (P m : ℕ) (hP : Squarefree P) (hP_pos : 0 < P) (hm : 0 < m)
    (d e : ℕ) (hd : d ∈ sqfDivisors P) (he : e ∈ sqfDivisors P)
    (hde_not_cop : ¬ Nat.Coprime d e)
    (h : ℕ) (hcop : Nat.Coprime h P) :
    (Finset.univ.filter (fun x : Fin (P * m) =>
      d ∣ Nat.gcd x.val P ∧
      e ∣ Nat.gcd ((x.val + h) % (P * m)) P)).card = 0 := by
  simp +zetaDelta at *;
  intro x hx_div_d hx_div_e
  have h_common_prime : ∃ p, Nat.Prime p ∧ p ∣ d ∧ p ∣ e := by
    exact Nat.Prime.not_coprime_iff_dvd.mp hde_not_cop;
  obtain ⟨ p, hp_prime, hp_div_d, hp_div_e ⟩ := h_common_prime
  have hp_div_x : p ∣ x.val := by
    exact Nat.dvd_trans hp_div_d hx_div_d |> Nat.dvd_trans <| Nat.gcd_dvd_left _ _
  have hp_div_xh : p ∣ (x.val + h) := by
    have hp_div_xh : p ∣ ((x.val + h) % (P * m)) := by
      exact Nat.dvd_trans hp_div_e hx_div_e |> Nat.dvd_trans <| Nat.gcd_dvd_left _ _;
    rw [ Nat.dvd_iff_mod_eq_zero ] at *;
    rw [ ← hp_div_xh, Nat.mod_mod_of_dvd _ ( dvd_mul_of_dvd_left ( show p ∣ P from Nat.dvd_trans ( Nat.dvd_of_mod_eq_zero hp_div_d ) ( Nat.dvd_of_mem_divisors ( Finset.mem_filter.mp hd |>.1 ) ) ) _ ) ]
  have hp_div_h : p ∣ h := by
    simpa using Nat.dvd_sub hp_div_xh hp_div_x
  have hp_div_P : p ∣ P := by
    exact dvd_trans hp_div_d ( mem_sqfDivisors.mp hd |>.1 )
  have hp_not_div_h : ¬p ∣ h := by
    exact fun h => hp_prime.not_dvd_one <| hcop.gcd_eq_one ▸ Nat.dvd_gcd h hp_div_P
  exact hp_not_div_h hp_div_h

/-
Correlation identity for coprime shifts using unsquared weights.
-/
theorem selbergWeight_correlation_coprime
    (P m : ℕ) (hP : Squarefree P) (hP_pos : 0 < P) (hm : 0 < m)
    (lambda : ℕ → ℝ)
    (h : Fin (P * m)) (hcop : Nat.Coprime h.val P) :
    ∑ x : Fin (P * m),
      selbergWeight (P * m) P lambda x *
      selbergWeight (P * m) P lambda ⟨(x.val + h.val) % (P * m),
        Nat.mod_lt _ (by positivity)⟩
    = (P * m : ℝ) * coprimePairsQuadForm P lambda := by
  -- Expand the correlation sum: Σ_x w(x)w(x+h) = Σ_{d,e ∈ sqfDivisors P} λ_d λ_e * #{x: d|gcd(x,P) and e|gcd(x+h,P)}.
  have h_expand : ∑ x : Fin (P * m), selbergWeight (P * m) P lambda x * selbergWeight (P * m) P lambda ⟨((x.val + h.val) % (P * m)), Nat.mod_lt _ (by positivity)⟩ = ∑ d ∈ sqfDivisors P, ∑ e ∈ sqfDivisors P, lambda d * lambda e * (Finset.univ.filter (fun x : Fin (P * m) => d ∣ Nat.gcd x.val P ∧ e ∣ Nat.gcd ((x.val + h.val) % (P * m)) P)).card := by
    have h_expand : ∀ x : Fin (P * m), selbergWeight (P * m) P lambda x = ∑ d ∈ sqfDivisors P, (if d ∣ Nat.gcd x.val P then lambda d else 0) := by
      intro x; rw [ selbergWeight ] ; rw [ Finset.sum_filter ] ;
    simp +decide only [h_expand, sum_mul _ _ _];
    simp +decide only [mul_sum, mul_ite, mul_zero];
    rw [ Finset.sum_comm, Finset.sum_congr rfl ];
    intro d hd; rw [ Finset.sum_comm ] ; simp +decide [ Finset.sum_ite ] ;
    simp +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.filter_filter ];
    simp +decide only [and_comm];
  -- By count_coprime_shifted_multiples_coprime (when gcd(d,e)=1) the count is P*m/(d*e), and by count_coprime_shifted_multiples_noncoprime (when gcd(d,e)>1) the count is 0.
  have h_count : ∀ d e : ℕ, d ∈ sqfDivisors P → e ∈ sqfDivisors P → (Finset.univ.filter (fun x : Fin (P * m) => d ∣ Nat.gcd x.val P ∧ e ∣ Nat.gcd ((x.val + h.val) % (P * m)) P)).card = if Nat.Coprime d e then P * m / (d * e) else 0 := by
    grind +suggestions;
  rw [ h_expand, coprimePairsQuadForm ];
  simp +decide only [mul_sum];
  rw [ Finset.sum_congr rfl ];
  intro d hd; rw [ Finset.sum_filter ] ; refine' Finset.sum_congr rfl fun e he => _ ; rw [ h_count d e hd he ] ; split_ifs <;> simp +decide [ *, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv ] ;
  rw [ Nat.cast_div ] <;> norm_num;
  · exact Or.inl <| Or.inl <| by ring;
  · exact dvd_mul_of_dvd_left ( Nat.Coprime.mul_dvd_of_dvd_of_dvd ‹_› ( Nat.dvd_of_mem_divisors ( Finset.filter_subset _ _ hd ) ) ( Nat.dvd_of_mem_divisors ( Finset.filter_subset _ _ he ) ) ) _;
  · exact ⟨ Nat.ne_of_gt ( Nat.pos_of_mem_divisors ( Finset.mem_filter.mp hd |>.1 ) ), Nat.ne_of_gt ( Nat.pos_of_mem_divisors ( Finset.mem_filter.mp he |>.1 ) ) ⟩

/-
coprimePairsQuadForm ≤ multiPrimeQuadForm for nonneg weights.
-/
lemma coprimePairsQuadForm_le_multiPrimeQuadForm
    (P : ℕ) (hP_pos : 0 < P) (lambda : ℕ → ℝ)
    (hlam_nonneg : ∀ d ∈ sqfDivisors P, 0 ≤ lambda d) :
    coprimePairsQuadForm P lambda ≤ multiPrimeQuadForm P lambda := by
  apply Finset.sum_le_sum;
  intro i hi;
  refine' le_trans _ ( Finset.sum_le_sum_of_subset_of_nonneg _ _ );
  rotate_left;
  exact Finset.filter ( Nat.Coprime i ) ( sqfDivisors P );
  · exact Finset.filter_subset _ _;
  · exact fun j hj hj' => div_nonneg ( mul_nonneg ( hlam_nonneg i hi ) ( hlam_nonneg j hj ) ) ( Nat.cast_nonneg _ );
  · refine' Finset.sum_le_sum fun j hj => _;
    rw [ Nat.Coprime.lcm_eq_mul ( Finset.mem_filter.mp hj |>.2 ) ] ; norm_cast

/-
Correlation ≤ (P*m) * Q(λ).
-/
theorem selbergWeight_correlation_coprime_bound
    (P m : ℕ) (hP : Squarefree P) (hP_pos : 0 < P) (hm : 0 < m)
    (lambda : ℕ → ℝ)
    (hlam_nonneg : ∀ d ∈ sqfDivisors P, 0 ≤ lambda d)
    (h : Fin (P * m)) (hcop : Nat.Coprime h.val P) :
    ∑ x : Fin (P * m),
      selbergWeight (P * m) P lambda x *
      selbergWeight (P * m) P lambda ⟨(x.val + h.val) % (P * m),
        Nat.mod_lt _ (by positivity)⟩
    ≤ (P * m : ℝ) * multiPrimeQuadForm P lambda := by
  rw [selbergWeight_correlation_coprime P m hP hP_pos hm lambda h hcop]
  exact mul_le_mul_of_nonneg_left ( coprimePairsQuadForm_le_multiPrimeQuadForm P hP_pos lambda hlam_nonneg ) ( by positivity : ( 0 : ℝ ) ≤ P * m )

/-
h=0 autocorrelation: Σ selbergWeight(x)² = (P*m) * Q(λ).
-/
theorem selbergWeight_autocorrelation_eq
    (P m : ℕ) (hP : Squarefree P) (hP_pos : 0 < P) (hm : 0 < m)
    (lambda : ℕ → ℝ) :
    ∑ x : Fin (P * m), selbergWeight (P * m) P lambda x ^ 2
    = (P * m : ℝ) * multiPrimeQuadForm P lambda := by
  simp_rw [← selbergNu_eq_sq]
  exact l2NormSq_multiPrime_eq_quadForm P m hP hP_pos hm lambda

end