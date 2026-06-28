/-
# Sieve.MultiPrime.OptimalWeights

Optimal Selberg weights and the evaluation of the quadratic form Q(λ)
at the optimal choice.

## Main definitions

* `hFunction` — the multiplicative function h(d) = g(d) / ∏_{p | d} (1 - g(p))
* `V_function` — V(D) = Σ_{d ≤ D, d ∈ sqfDiv(P)} h(d)
* `selbergOptimalWeights` — the *correct* truncated Selberg optimal weights for
  the quadratic form `multiPrimeQuadForm P λ = Σ_{d,e} λ_d λ_e / lcm(d,e)`.

## Main results

* `hFunction_one` — h(1) = 1 when g(1) = 1
* `V_function_ge_one` — V(D) ≥ 1 under standard assumptions
* `V_function_pos` — V(D) > 0 under standard assumptions
* `selbergOptimalWeights_one` — the optimal weights satisfy λ_1 = 1
* `multiPrimeQuadForm_diagonal` — Selberg diagonalisation of the quadratic form
* `optimalWeight_quadForm_eq` — Q(λ_opt) = 1 / V(1/·, P, D)

## Correction note

The quadratic form `multiPrimeQuadForm P λ = Σ_{d,e} λ_d λ_e / lcm(d,e)` is
**independent of `g`**: its value, and hence the minimum over `λ` with `λ₁ = 1`,
is determined purely by the lattice of squarefree divisors of `P`. Consequently
the only meaningful sieve density is the natural one `g(d) = 1/d`, for which
`h(d) = 1/φ(d)` and `V(1/·, P, D) = Σ_{d ≤ D, d | P} 1/φ(d)`.

The previously displayed formula `λ_d = μ(d) · V(D/d) / V(D)` is **not** the
optimiser of `multiPrimeQuadForm` in the truncated setting (a concrete
counterexample: `P = 6`, `D = 6`, `g = 1/·` gives `Q = 79/216 ≠ 1/3 = 1/V`).
The correct optimiser is the Möbius inversion of the diagonalised system,
`λ_d = d · (1/V) · Σ_{d | j ≤ D} μ(j/d) μ(j)/φ(j)`, which is recorded below and
is independent of `g`. The `g` argument is retained only for interface
compatibility with the downstream general-weight statements.

-- Source: Iwaniec-Kowalski eq. (6.63)-(6.74); Ford §4 pages 43-45; JTNB_2006 eq. (8.2)

Status: Proved
-/
import Mathlib
import RequestProject.Core.MultiPrime.L2Identity

open Finset BigOperators

noncomputable section

-- Source: Iwaniec-Kowalski eq. (6.63); Ford sieve2023-6.pdf §4 p. 43
/-- The multiplicative function h(d) = g(d) / ∏_{p ∈ primeFactors(d)} (1 - g(p)).
    For squarefree d with g multiplicative, this equals
    ∏_{p | d} g(p)/(1 - g(p)). -/
noncomputable def hFunction (g : ℕ → ℝ) (d : ℕ) : ℝ :=
  g d / ∏ p ∈ d.primeFactors, (1 - g p)

-- Source: Iwaniec-Kowalski eq. (6.74); JTNB_2006 eq. (8.2)
/-- V(D) = Σ_{d ≤ D, d ∈ sqfDivisors(P)} h(d).
    This is the reciprocal sum that appears in the Selberg upper bound. -/
noncomputable def V_function (g : ℕ → ℝ) (P D : ℕ) : ℝ :=
  ∑ d ∈ (sqfDivisors P).filter (· ≤ D), hFunction g d

-- Source: Iwaniec-Kowalski eq. (6.71)
/-- The correct truncated Selberg optimal weights for the quadratic form
    `multiPrimeQuadForm P λ = Σ_{d,e} λ_d λ_e / lcm(d,e)`.

    This is the Möbius inversion of the diagonalised optimiser
    `y_k = μ(k)/(φ(k) · V)` (for `k ≤ D`), namely
    `λ_d = d · (1/V) · Σ_{d | j ≤ D} μ(j/d) μ(j)/φ(j)`,
    where `V = V(1/·, P, D) = Σ_{k ≤ D, k | P} 1/φ(k)`.

    The weights are independent of `g`; the `g` argument is vestigial and kept
    only for interface compatibility. -/
noncomputable def selbergOptimalWeights (_g : ℕ → ℝ) (P D : ℕ) (d : ℕ) : ℝ :=
  (d : ℝ) * (∑ j ∈ (sqfDivisors P).filter (· ≤ D),
      (if d ∣ j then (ArithmeticFunction.moebius (j / d) : ℝ) *
        (ArithmeticFunction.moebius j : ℝ) / (Nat.totient j : ℝ) else 0))
    / V_function (fun n => (1 : ℝ) / n) P D

/-- h(1) = 1 when g(1) = 1. -/
lemma hFunction_one (g : ℕ → ℝ) (hg1 : g 1 = 1) : hFunction g 1 = 1 := by
  simp only [hFunction, Nat.primeFactors_one, prod_empty, hg1, div_one]

/-- V(D) ≥ 1 when D ≥ 1 and g(1) = 1, P ≠ 0, h nonneg. -/
lemma V_function_ge_one (g : ℕ → ℝ) (P D : ℕ) (hP : P ≠ 0) (hD : 1 ≤ D)
    (hg1 : g 1 = 1)
    (hh_nonneg : ∀ d ∈ sqfDivisors P, 0 ≤ hFunction g d) :
    1 ≤ V_function g P D := by
  calc (1 : ℝ) = hFunction g 1 := (hFunction_one g hg1).symm
    _ ≤ V_function g P D := Finset.single_le_sum
        (fun x hx => hh_nonneg x (Finset.mem_filter.mp hx |>.1))
        (Finset.mem_filter.mpr ⟨one_mem_sqfDivisors hP, hD⟩)

/-- V(D) > 0 when D ≥ 1, g(1) = 1, P ≠ 0, h nonneg. -/
lemma V_function_pos (g : ℕ → ℝ) (P D : ℕ) (hP : P ≠ 0) (hD : 1 ≤ D)
    (hg1 : g 1 = 1)
    (hh_nonneg : ∀ d ∈ sqfDivisors P, 0 ≤ hFunction g d) :
    0 < V_function g P D :=
  lt_of_lt_of_le zero_lt_one (V_function_ge_one g P D hP hD hg1 hh_nonneg)

/-
For squarefree k dividing P, h(1/·, k) = 1 / φ(k).
-/
lemma hFunction_inv_eq_totient_inv {P k : ℕ} (hk : k ∈ sqfDivisors P) :
    hFunction (fun n => (1 : ℝ) / n) k = 1 / (Nat.totient k : ℝ) := by
  by_cases hk0 : k = 0 <;> simp_all +decide [ hFunction ];
  -- By definition of totient function, we know that $\varphi(k) = k \prod_{p \mid k} (1 - 1/p)$.
  have h_totient : (Nat.totient k : ℝ) = k * ∏ p ∈ k.primeFactors, (1 - (p : ℝ)⁻¹) := by
    convert Nat.totient_eq_mul_prod_factors k using 1;
    norm_num [ ← @Rat.cast_inj ℝ ];
  rw [ h_totient, mul_inv ] ; ring

/-- h(1/·) is nonnegative on squarefree divisors. -/
lemma hFunction_inv_nonneg {P : ℕ} {d : ℕ} (hd : d ∈ sqfDivisors P) :
    0 ≤ hFunction (fun n => (1 : ℝ) / n) d := by
  unfold hFunction
  apply div_nonneg
  · positivity
  · apply Finset.prod_nonneg
    intro p hp
    have hp_prime := Nat.prime_of_mem_primeFactors hp
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp_prime.one_le
    simp only [one_div]
    linarith [inv_le_one_of_one_le₀ (by exact_mod_cast hp_prime.one_le : (1 : ℝ) ≤ p)]

/-- V(1/·, P, D) > 0 for D ≥ 1, P ≠ 0. -/
lemma V_inv_pos {P D : ℕ} (hP : P ≠ 0) (hD : 1 ≤ D) :
    0 < V_function (fun n => (1 : ℝ) / n) P D :=
  V_function_pos _ P D hP hD (by norm_num) (fun d hd => hFunction_inv_nonneg hd)

/-- V(1/·, P, D) expressed as a sum of inverse totients. -/
lemma V_inv_eq_sum_totient_inv (P D : ℕ) :
    V_function (fun n => (1 : ℝ) / n) P D =
      ∑ k ∈ (sqfDivisors P).filter (· ≤ D), 1 / (Nat.totient k : ℝ) := by
  unfold V_function
  exact Finset.sum_congr rfl fun k hk =>
    hFunction_inv_eq_totient_inv (Finset.mem_filter.mp hk).1

/-
**Selberg diagonalisation.** For squarefree `P`, any weights `λ`,
    `Σ_{d,e} λ_d λ_e / lcm(d,e) = Σ_k φ(k) · (Σ_{k | d} λ_d / d)²`,
    where `k, d, e` range over squarefree divisors of `P`.
-/
lemma multiPrimeQuadForm_diagonal (P : ℕ) (hP : Squarefree P) (hP_pos : 0 < P)
    (lam : ℕ → ℝ) :
    multiPrimeQuadForm P lam =
      ∑ k ∈ sqfDivisors P, (Nat.totient k : ℝ) *
        (∑ d ∈ sqfDivisors P, if k ∣ d then lam d / (d : ℝ) else 0) ^ 2 := by
  -- Now use the provided lemma to rewrite the sum.
  have h_sum_rewrite : ∑ k ∈ sqfDivisors P, (Nat.totient k : ℝ) * (∑ d ∈ sqfDivisors P, if k ∣ d then (lam d / (d : ℝ)) else 0) ^ 2 = ∑ d ∈ sqfDivisors P, ∑ e ∈ sqfDivisors P, (lam d * lam e / (d * e : ℝ)) * (∑ k ∈ sqfDivisors P, if k ∣ d ∧ k ∣ e then (Nat.totient k : ℝ) else 0) := by
    simp +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul, sq ] at *; (
    exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by split_ifs <;> ring <;> aesop ) ) ;)
  generalize_proofs at *; (
  -- Evaluate the inner sum $\sum_{k \in \text{sqfDivisors } P, k \mid d \land k \mid e} \phi(k)$.
  have h_inner_sum : ∀ d e : ℕ, d ∈ sqfDivisors P → e ∈ sqfDivisors P → ∑ k ∈ sqfDivisors P, (if k ∣ d ∧ k ∣ e then (Nat.totient k : ℝ) else 0) = Nat.gcd d e := by
    intros d e hd he
    have h_divisors : Finset.filter (fun k => k ∣ d ∧ k ∣ e) (sqfDivisors P) = Nat.divisors (Nat.gcd d e) := by
      ext k; simp [sqfDivisors] at *; (
      simp_all +decide [ Nat.dvd_gcd_iff, squarefreeDivisors ];
      exact ⟨ fun h => ⟨ ⟨ h.2.1, h.2.2 ⟩, by aesop ⟩, fun h => ⟨ ⟨ dvd_trans h.1.1 hd.1.1, by exact hd.2.squarefree_of_dvd h.1.1 ⟩, h.1.1, h.1.2 ⟩ ⟩ ;)
    generalize_proofs at *; (
    rw [ ← Finset.sum_filter, h_divisors ] ; exact mod_cast Nat.sum_totient _;)
  generalize_proofs at *; (
  rw [ h_sum_rewrite, Finset.sum_congr rfl fun d hd => Finset.sum_congr rfl fun e he => by rw [ h_inner_sum d e hd he ] ] ; norm_num [ multiPrimeQuadForm ] ; ring;
  refine' Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => _ ; rw [ Nat.lcm ] ; ring ;
  rw [ Nat.cast_div ( Nat.dvd_trans ( Nat.gcd_dvd_left _ _ ) ( dvd_mul_right _ _ ) ) ] <;> norm_num ; ring;
  exact fun hx' => absurd hx' ( Nat.ne_of_gt ( Nat.pos_of_dvd_of_pos ( mem_sqfDivisors.mp hx |>.1 ) hP_pos ) )))

/-
Möbius telescoping on the squarefree divisor lattice: for `j ∈ sqfDivisors P`
    and any `k`, `Σ_{d : k | d ∣ j} μ(j/d) = [j = k]`.
-/
lemma sqfDiv_moebius_telescope {P : ℕ} (hP : Squarefree P) {j : ℕ}
    (hj : j ∈ sqfDivisors P) (k : ℕ) :
    ∑ d ∈ sqfDivisors P,
      (if k ∣ d ∧ d ∣ j then (ArithmeticFunction.moebius (j / d) : ℝ) else 0) =
      if j = k then 1 else 0 := by
  by_cases hk : k ∣ j <;> simp_all +decide [ Finset.sum_ite ];
  · -- Since $k \mid j$, we can rewrite the sum as $\sum_{t \mid j/k} \mu((j/k)/t)$.
    have h_sum_rewrite : ∑ x ∈ sqfDivisors P, (if k ∣ x ∧ x ∣ j then (ArithmeticFunction.moebius (j / x) : ℝ) else 0) = ∑ t ∈ Nat.divisors (j / k), (ArithmeticFunction.moebius ((j / k) / t) : ℝ) := by
      have h_sum_rewrite : ∑ x ∈ sqfDivisors P, (if k ∣ x ∧ x ∣ j then (ArithmeticFunction.moebius (j / x) : ℝ) else 0) = ∑ x ∈ Nat.divisors j, (if k ∣ x then (ArithmeticFunction.moebius (j / x) : ℝ) else 0) := by
        rw [ ← Finset.sum_subset ( show Nat.divisors j ⊆ sqfDivisors P from ?_ ) ];
        · exact Finset.sum_congr rfl fun x hx => by aesop;
        · aesop;
        · simp_all +decide [ Finset.subset_iff, mem_sqfDivisors ];
          exact fun x hx₁ hx₂ => ⟨ dvd_trans hx₁ hj.1, hj.2.2.squarefree_of_dvd hx₁ ⟩;
      rw [ h_sum_rewrite, ← Finset.sum_filter ];
      refine' Finset.sum_bij ( fun x hx => x / k ) _ _ _ _ <;> simp_all +decide [ Nat.div_div_eq_div_mul ];
      · exact fun a ha₁ ha₂ ha₃ => ⟨ by rwa [ Nat.mul_div_cancel' ha₃ ], Nat.ne_of_gt ( Nat.pos_of_dvd_of_pos hk ( Nat.pos_of_ne_zero ha₂ ) ), Nat.le_of_dvd ( Nat.pos_of_ne_zero ha₂ ) hk ⟩;
      · exact fun b hb hk₁ hk₂ => ⟨ k * b, ⟨ ⟨ hb, by aesop_cat ⟩, dvd_mul_right _ _ ⟩, Nat.mul_div_cancel_left _ ( Nat.pos_of_ne_zero hk₁ ) ⟩;
      · exact fun a ha₁ ha₂ ha₃ => by rw [ Nat.mul_div_cancel' ha₃ ] ;
    have h_sum_rewrite : ∑ t ∈ Nat.divisors (j / k), (ArithmeticFunction.moebius ((j / k) / t) : ℝ) = if j / k = 1 then 1 else 0 := by
      have h_sum_rewrite : ∀ n : ℕ, n ≠ 0 → ∑ t ∈ Nat.divisors n, (ArithmeticFunction.moebius (n / t) : ℝ) = if n = 1 then 1 else 0 := by
        intro n hn_ne_zero
        have h_moebius_sum : ∑ t ∈ Nat.divisors n, (ArithmeticFunction.moebius t : ℝ) = if n = 1 then 1 else 0 := by
          have h_moebius_sum : ∑ t ∈ Nat.divisors n, (ArithmeticFunction.moebius t : ℝ) = (ArithmeticFunction.moebius * ArithmeticFunction.zeta) n := by
            simp +decide [ ArithmeticFunction.zeta, Finset.sum_filter ];
            rw [ Nat.sum_divisorsAntidiagonal fun x y => if y = 0 then 0 else ( ArithmeticFunction.moebius x : ℝ ) ];
            exact Finset.sum_congr rfl fun x hx => by rw [ if_neg ( Nat.ne_of_gt ( Nat.div_pos ( Nat.le_of_dvd ( Nat.pos_of_ne_zero hn_ne_zero ) ( Nat.dvd_of_mem_divisors hx ) ) ( Nat.pos_of_mem_divisors hx ) ) ) ] ;
          aesop;
        rw [ ← h_moebius_sum, ← Nat.sum_div_divisors ];
        exact Finset.sum_congr rfl fun x hx => by rw [ Nat.div_div_self ] <;> aesop;
      · have hjpos : 0 < j :=
          Nat.pos_of_dvd_of_pos (mem_sqfDivisors.mp hj).1
            (Nat.pos_of_ne_zero (mem_sqfDivisors.mp hj).2.1)
        have hk0 : 0 < k := Nat.pos_of_ne_zero (fun h => by simp [h] at hk; omega)
        have hjk : 0 < j / k := Nat.div_pos (Nat.le_of_dvd hjpos hk) hk0
        exact h_sum_rewrite (j / k) hjk.ne'
    cases eq_or_ne k 0 <;> simp_all +decide [ Nat.div_eq_iff_eq_mul_left ];
    · exact absurd hj ( by rw [ mem_sqfDivisors ] ; aesop );
    · simp_all +decide [ Finset.sum_ite ];
      split_ifs <;> simp_all +decide [ Nat.div_eq_iff_eq_mul_left ( Nat.pos_of_ne_zero ‹_› ) ];
  · rw [ Finset.sum_eq_zero ] ; aesop;
    exact fun x hx => False.elim <| hk <| dvd_trans ( Finset.mem_filter.mp hx |>.2.1 ) ( Finset.mem_filter.mp hx |>.2.2 )

/-
The diagonal coordinate `y_k = Σ_{k | d} λ_d / d` of `selbergOptimalWeights`
    equals `[k ≤ D] · μ(k)/(φ(k) · V)`.
-/
lemma selbergOptimalWeights_y_eq {P D : ℕ} (hP : Squarefree P) (hP_pos : 0 < P)
    (g : ℕ → ℝ) {k : ℕ} (hk : k ∈ sqfDivisors P) :
    (∑ d ∈ sqfDivisors P, if k ∣ d then selbergOptimalWeights g P D d / (d : ℝ) else 0) =
      (if k ≤ D then (ArithmeticFunction.moebius k : ℝ) / (Nat.totient k : ℝ) else 0) /
        V_function (fun n => (1 : ℝ) / n) P D := by
  convert congr_arg ( fun x : ℝ => x / V_function ( fun n => 1 / ( n : ℝ ) ) P D ) _ using 1;
  rotate_left;
  exact ( ∑ j ∈ ( sqfDivisors P ).filter ( · ≤ D ), ( ArithmeticFunction.moebius j : ℝ ) / ( Nat.totient j : ℝ ) * ( ∑ d ∈ sqfDivisors P, if k ∣ d ∧ d ∣ j then ( ArithmeticFunction.moebius ( j / d ) : ℝ ) else 0 ) );
  · -- Apply the result from `sqfDiv_moebius_telescope`.
    have h_telescope : ∀ j ∈ sqfDivisors P, (j ≤ D) → (∑ d ∈ sqfDivisors P, if k ∣ d ∧ d ∣ j then (ArithmeticFunction.moebius (j / d) : ℝ) else 0) = if j = k then 1 else 0 := by
      intros j hj hjD
      apply sqfDiv_moebius_telescope hP hj k;
    rw [ Finset.sum_congr rfl fun x hx => by rw [ h_telescope x ( Finset.mem_filter.mp hx |>.1 ) ( Finset.mem_filter.mp hx |>.2 ) ] ] ; aesop;
  · unfold selbergOptimalWeights;
    simp +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul ];
    rw [ Finset.sum_comm, Finset.sum_congr rfl ];
    intro x hx; split_ifs <;> simp_all +decide [ ne_of_gt ( show 0 < x from Nat.pos_of_mem_divisors ( Finset.mem_filter.mp hx |>.1 ) ) ] ;

/-
The optimal weights satisfy λ_1 = 1 when D ≥ 1 and P ≠ 0.
-/
lemma selbergOptimalWeights_one (g : ℕ → ℝ) (P D : ℕ) (hP : Squarefree P)
    (hP_pos : 0 < P) (hD : 1 ≤ D) :
    selbergOptimalWeights g P D 1 = 1 := by
  unfold selbergOptimalWeights; norm_num [ V_inv_eq_sum_totient_inv ] ;
  convert div_self _;
  · convert V_inv_eq_sum_totient_inv P D using 2 ; norm_num [ ArithmeticFunction.moebius_apply_of_squarefree ( show Squarefree _ from _ ) ];
    simp_all +decide [ ArithmeticFunction.moebius ];
    simp_all +decide [ ← mul_pow, sqfDivisors ];
    unfold squarefreeDivisors at *; aesop;
  · refine' ne_of_gt ( lt_of_lt_of_le _ ( Finset.single_le_sum ( fun x hx => _ ) ( show 1 ∈ _ from _ ) ) ) <;> norm_num;
    · exact div_nonneg ( mul_self_nonneg _ ) ( Nat.cast_nonneg _ );
    · exact ⟨ one_mem_sqfDivisors hP_pos.ne', hD ⟩

/-
The optimal weights vanish outside the support.
-/
lemma selbergOptimalWeights_zero (g : ℕ → ℝ) (P D : ℕ) (d : ℕ)
    (hd : d ∉ (sqfDivisors P).filter (· ≤ D)) :
    selbergOptimalWeights g P D d = 0 := by
  unfold selbergOptimalWeights;
  simp +zetaDelta at *;
  refine Or.inl <| Or.inr <| Finset.sum_eq_zero fun j hj => if_neg <| ?_;
  contrapose! hd;
  simp_all +decide [ mem_sqfDivisors ];
  exact ⟨ ⟨ dvd_trans hd hj.1.1, hj.1.2.2.squarefree_of_dvd hd ⟩, Nat.le_trans ( Nat.le_of_dvd ( Nat.pos_of_ne_zero ( by aesop ) ) hd ) hj.2 ⟩

/-
**Key theorem:** for the (corrected) optimal Selberg weights,
    `Q(λ_opt) = 1 / V(1/·, P, D)`.

    Source: Iwaniec-Kowalski eq. (6.70); Ford Theorem 4.1 p. 44.

    Proof: by `multiPrimeQuadForm_diagonal`, `Q(λ) = Σ_k φ(k) y_k²` with
    `y_k = Σ_{k | d} λ_d / d`. By `selbergOptimalWeights_y_eq`,
    `y_k = [k ≤ D] μ(k)/(φ(k) V)`, so
    `φ(k) y_k² = [k ≤ D] μ(k)²/(φ(k) V²) = [k ≤ D]/(φ(k) V²)` (as `μ(k)² = 1`
    on squarefree `k`). Summing and using `V = Σ_{k ≤ D} 1/φ(k)` gives
    `Q = (1/V²) Σ_{k ≤ D} 1/φ(k) = V/V² = 1/V`.
-/
theorem optimalWeight_quadForm_eq
    (P D : ℕ) (g : ℕ → ℝ)
    (hP : Squarefree P) (hP_pos : 0 < P)
    (hD : 1 ≤ D) :
    multiPrimeQuadForm P (selbergOptimalWeights g P D) =
      1 / V_function (fun n => (1 : ℝ) / n) P D := by
  rw [ multiPrimeQuadForm_diagonal P hP hP_pos ];
  convert Finset.sum_congr rfl fun k hk => ?_ using 2;
  rotate_left;
  use fun k => if k ≤ D then 1 / ( Nat.totient k : ℝ ) / ( V_function ( fun n => 1 / ( n : ℝ ) ) P D ) ^ 2 else 0;
  · rw [ selbergOptimalWeights_y_eq hP hP_pos g hk ];
    split_ifs <;> simp_all +decide [ sq, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv ];
    simp +decide [ ← mul_assoc, ne_of_gt ( Nat.totient_pos.mpr ( Nat.pos_of_mem_divisors ( Finset.mem_filter.mp hk |>.1 ) ) ) ];
    simp +decide [ ArithmeticFunction.moebius, mul_assoc, mul_comm, mul_left_comm ];
    norm_num [ ← mul_pow, mem_sqfDivisors.mp hk |>.2.2 ];
  · convert congr_arg ( fun x : ℝ => x / V_function ( fun n => 1 / ( n : ℝ ) ) P D ^ 2 ) ( V_inv_eq_sum_totient_inv P D ) using 1;
    · grind;
    · rw [ Finset.sum_filter, Finset.sum_div ] ; congr ; ext ; aesop

end