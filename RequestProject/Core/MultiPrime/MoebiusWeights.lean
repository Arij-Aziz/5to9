/-
# MoebiusWeights.lean
Möbius weights for the multi-prime sieve and their quadratic form evaluation.

Status: ProvedInProject
-/
import Mathlib
import RequestProject.Core.MultiPrime.OptimalWeights

open Finset BigOperators Nat

noncomputable section

-- Compatibility shim
private lemma mem_sqfDivisors_dvd {P d : ℕ} (hd : d ∈ sqfDivisors P) : d ∣ P :=
  Nat.dvd_of_mem_divisors <| Finset.filter_subset _ _ hd

/-- The Möbius weights restricted to sqfDivisors P. -/
noncomputable def moebiusWeights (P : ℕ) (d : ℕ) : ℝ :=
  if d ∈ sqfDivisors P
  then (ArithmeticFunction.moebius d : ℝ)
  else 0

/-- The Möbius weights satisfy λ_1 = 1. -/
lemma moebiusWeights_one (P : ℕ) (hP_pos : 0 < P) :
    moebiusWeights P 1 = 1 := by
  simp [moebiusWeights, one_mem_sqfDivisors hP_pos.ne', ArithmeticFunction.moebius_apply_one]

/-
Auxiliary: multiPrimeQuadForm is multiplicative on coprime squarefree factors.
-/
private lemma moebius_quadForm_mul {n m : ℕ} (hnm : n.Coprime m)
    (hn : Squarefree n) (hm : Squarefree m) :
    multiPrimeQuadForm (n * m) (moebiusWeights (n * m)) =
    multiPrimeQuadForm n (moebiusWeights n) * multiPrimeQuadForm m (moebiusWeights m) := by
  -- By definition of `sqfDivisors`, we know that `sqfDivisors (n * m)` is the set of all products of elements from `sqfDivisors n` and `sqfDivisors m`.
  have h_sqfDivisors : sqfDivisors (n * m) = Finset.image (fun (p : ℕ × ℕ) => p.1 * p.2) (sqfDivisors n ×ˢ sqfDivisors m) := by
    ext d; simp [sqfDivisors];
    constructor <;> intro hd <;> simp_all +decide [ squarefreeDivisors ];
    · rw [ Nat.dvd_mul ] at hd;
      rcases hd.1.1 with ⟨ a, b, ha, hb, rfl ⟩ ; exact ⟨ a, b, ⟨ ⟨ ha, hn.squarefree_of_dvd ha ⟩, hb, hm.squarefree_of_dvd hb ⟩, rfl ⟩ ;
    · rcases hd with ⟨ a, b, ⟨ ⟨ ⟨ ha₁, ha₂ ⟩, ha₃ ⟩, ⟨ ⟨ hb₁, hb₂ ⟩, hb₃ ⟩ ⟩, rfl ⟩ ; simp_all +decide [ Nat.squarefree_mul_iff ] ;
      exact ⟨ mul_dvd_mul ha₁ hb₁, hnm.coprime_dvd_left ha₁ |> Nat.Coprime.coprime_dvd_right hb₁ ⟩;
  unfold multiPrimeQuadForm;
  rw [ h_sqfDivisors, Finset.sum_image, Finset.sum_comm ];
  · rw [ Finset.sum_image ];
    · -- By definition of `moebiusWeights`, we know that `moebiusWeights (n * m) (d * e) = moebiusWeights n d * moebiusWeights m e` for coprime `d` and `e`.
      have h_moebiusWeights : ∀ d e : ℕ, d ∈ sqfDivisors n → e ∈ sqfDivisors m → moebiusWeights (n * m) (d * e) = moebiusWeights n d * moebiusWeights m e := by
        intros d e hd he
        have h_moebius_mul : ArithmeticFunction.moebius (d * e) = ArithmeticFunction.moebius d * ArithmeticFunction.moebius e := by
          simp +decide [ ArithmeticFunction.moebius ];
          split_ifs <;> simp_all +decide [ Nat.squarefree_mul_iff ];
          · rw [ ← pow_add, ArithmeticFunction.cardFactors_mul ] <;> aesop;
          · exact ‹¬Nat.gcd d e = 1› ( Nat.Coprime.gcd_eq_one <| Nat.Coprime.coprime_dvd_left ( mem_sqfDivisors_dvd hd ) <| Nat.Coprime.coprime_dvd_right ( mem_sqfDivisors_dvd he ) hnm );
        unfold moebiusWeights;
        rw [ if_pos ( h_sqfDivisors.symm ▸ Finset.mem_image.mpr ⟨ ( d, e ), Finset.mem_product.mpr ⟨ hd, he ⟩, rfl ⟩ ), if_pos hd, if_pos he, h_moebius_mul ] ; norm_cast;
      -- By definition of `lcm`, we know that `lcm(d * e, d' * e') = lcm(d, d') * lcm(e, e')` for coprime `d` and `e`.
      have h_lcm : ∀ d e d' e' : ℕ, d ∈ sqfDivisors n → e ∈ sqfDivisors m → d' ∈ sqfDivisors n → e' ∈ sqfDivisors m → Nat.lcm (d * e) (d' * e') = Nat.lcm d d' * Nat.lcm e e' := by
        intros d e d' e' hd he hd' he'
        have h_coprime : Nat.Coprime d e' ∧ Nat.Coprime e d' := by
          exact ⟨ Nat.Coprime.coprime_dvd_left ( mem_sqfDivisors_dvd hd ) <| Nat.Coprime.coprime_dvd_right ( mem_sqfDivisors_dvd he' ) hnm, Nat.Coprime.coprime_dvd_left ( mem_sqfDivisors_dvd he ) <| Nat.Coprime.coprime_dvd_right ( mem_sqfDivisors_dvd hd' ) hnm.symm ⟩;
        simp_all +decide [ Nat.lcm, Nat.gcd_mul_left, Nat.gcd_mul_right ];
        rw [ Nat.div_mul_div_comm ];
        · rw [ Nat.Coprime.gcd_mul ];
          · rw [ Nat.Coprime.gcd_mul_right_cancel _ h_coprime.2, Nat.Coprime.gcd_mul_left_cancel _ h_coprime.1 ] ; ring_nf;
          · exact Nat.Coprime.coprime_dvd_left ( mem_sqfDivisors_dvd hd' ) ( Nat.Coprime.coprime_dvd_right ( mem_sqfDivisors_dvd he' ) hnm );
        · exact dvd_mul_of_dvd_left ( Nat.gcd_dvd_left _ _ ) _;
        · exact dvd_mul_of_dvd_left ( Nat.gcd_dvd_left _ _ ) _;
      simp +decide only [sum_product, sum_mul_sum];
      refine' Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun l hl => _;
      rw [ h_moebiusWeights k l hk hl, h_moebiusWeights i j hi hj, h_lcm k l i j hk hl hi hj ] ; ring_nf;
      simp +decide [ Nat.lcm_comm, mul_assoc, mul_comm, mul_left_comm ];
    · intro p hp q hq; simp_all +decide [ Nat.coprime_mul_iff_left, Nat.coprime_mul_iff_right ] ;
      intro h_eq
      have h_div : p.1 ∣ q.1 ∧ q.1 ∣ p.1 := by
        exact ⟨ Nat.Coprime.dvd_of_dvd_mul_right ( show Nat.Coprime p.1 q.2 from Nat.Coprime.coprime_dvd_left ( mem_sqfDivisors_dvd hp.1 ) <| Nat.Coprime.coprime_dvd_right ( mem_sqfDivisors_dvd hq.2 ) hnm ) <| h_eq ▸ dvd_mul_right _ _, Nat.Coprime.dvd_of_dvd_mul_right ( show Nat.Coprime q.1 p.2 from Nat.Coprime.coprime_dvd_left ( mem_sqfDivisors_dvd hq.1 ) <| Nat.Coprime.coprime_dvd_right ( mem_sqfDivisors_dvd hp.2 ) hnm ) <| h_eq.symm ▸ dvd_mul_right _ _ ⟩;
      have := Nat.dvd_antisymm h_div.1 h_div.2; simp_all +decide [ sqfDivisors ] ;
      unfold squarefreeDivisors at *; aesop;
  · intro p hp q hq; simp_all +decide [ Nat.coprime_mul_iff_left, Nat.coprime_mul_iff_right ] ;
    intro h_eq
    have h_div : p.1 ∣ q.1 ∧ q.1 ∣ p.1 := by
      exact ⟨ Nat.Coprime.dvd_of_dvd_mul_right ( show Nat.Coprime p.1 q.2 from Nat.Coprime.coprime_dvd_left ( mem_sqfDivisors_dvd hp.1 ) <| Nat.Coprime.coprime_dvd_right ( mem_sqfDivisors_dvd hq.2 ) hnm ) <| h_eq ▸ dvd_mul_right _ _, Nat.Coprime.dvd_of_dvd_mul_right ( show Nat.Coprime q.1 p.2 from Nat.Coprime.coprime_dvd_left ( mem_sqfDivisors_dvd hq.1 ) <| Nat.Coprime.coprime_dvd_right ( mem_sqfDivisors_dvd hp.2 ) hnm ) <| h_eq.symm ▸ dvd_mul_right _ _ ⟩;
    have := Nat.dvd_antisymm h_div.1 h_div.2; simp_all +decide [ sqfDivisors ] ;
    unfold squarefreeDivisors at *; aesop;

/-
Auxiliary: for a prime p, Q(μ_p) = 1 - 1/p.
-/
private lemma moebius_quadForm_prime (p : ℕ) (hp : Nat.Prime p) :
    multiPrimeQuadForm p (moebiusWeights p) = 1 - 1 / (p : ℝ) := by
  unfold multiPrimeQuadForm;
  unfold sqfDivisors moebiusWeights;
  rw [ show squarefreeDivisors p = { 1, p } from ?_ ];
  · rcases p with ( _ | _ | p ) <;> norm_num [ sqfDivisors ] at *;
    norm_num [ squarefreeDivisors ];
    norm_num [ hp.squarefree, ArithmeticFunction.moebius_apply_prime hp ] ; ring;
  · ext; simp [squarefreeDivisors];
    constructor <;> intro h <;> simp_all +decide [ Nat.dvd_prime hp ];
    exact ⟨ hp.ne_zero, by rcases h with ( rfl | rfl ) <;> [ exact squarefree_one; exact hp.squarefree ] ⟩

/-
At the Möbius weights, multiPrimeQuadForm P μ = φ(P)/P.
-/
theorem moebius_quadForm_eq (P : ℕ) (hP : Squarefree P) (hP_pos : 0 < P) :
    multiPrimeQuadForm P (moebiusWeights P) =
      (Nat.totient P : ℝ) / (P : ℝ) := by
  -- Using the multiplicative property of the Möbius function and the fact that P is squarefree, we can write P as a product of primes.
  obtain ⟨ps, hps, hprod⟩ : ∃ ps : Finset ℕ, (∀ p ∈ ps, Nat.Prime p) ∧ P = ∏ p ∈ ps, p := by
    exact ⟨ P.primeFactors, fun p hp => Nat.prime_of_mem_primeFactors hp, Eq.symm <| Nat.prod_primeFactors_of_squarefree hP ⟩;
  -- By induction on the number of prime factors of $P$, we can show that the quadratic form of the Möbius weights is equal to the product of $(1 - 1/p)$ over the prime factors of $P$.
  have h_ind : ∀ (ps : Finset ℕ), (∀ p ∈ ps, Nat.Prime p) → multiPrimeQuadForm (∏ p ∈ ps, p) (moebiusWeights (∏ p ∈ ps, p)) = ∏ p ∈ ps, (1 - 1 / (p : ℝ)) := by
    intro ps hps; induction ps using Finset.induction <;> simp_all +decide ;
    · unfold multiPrimeQuadForm moebiusWeights; norm_num;
      unfold sqfDivisors;
      unfold squarefreeDivisors; norm_num;
      norm_num [ Finset.sum_filter ];
    · convert moebius_quadForm_mul _ _ _ using 1;
      · rw [ ‹multiPrimeQuadForm ( ∏ p ∈ _, p ) ( moebiusWeights ( ∏ p ∈ _, p ) ) = _›, moebius_quadForm_prime _ hps.1 ] ; ring;
      · exact Nat.Coprime.prod_right fun p hp => hps.1.coprime_iff_not_dvd.mpr fun h => ‹¬_› <| by have := Nat.prime_dvd_prime_iff_eq hps.1 ( hps.2 p hp ) ; aesop;
      · exact hps.1.squarefree;
      · have h_squarefree : ∀ {s : Finset ℕ}, (∀ p ∈ s, Nat.Prime p) → Squarefree (∏ p ∈ s, p) := by
          intros s hs; induction s using Finset.induction <;> simp_all +decide [ Nat.squarefree_mul_iff ] ;
          exact ⟨ Nat.Coprime.prod_right fun p hp => hs.1.coprime_iff_not_dvd.mpr fun h => by have := Nat.prime_dvd_prime_iff_eq hs.1 ( hs.2 p hp ) ; aesop, hs.1.squarefree ⟩;
        exact h_squarefree hps.2;
  convert h_ind ps hps using 1;
  · rw [hprod];
  · rw [ hprod, Nat.totient_eq_div_primeFactors_mul, Nat.primeFactors_prod ];
    · rw [ Nat.div_self ( Finset.prod_pos fun p hp => Nat.Prime.pos ( hps p hp ) ) ] ; norm_num [ Finset.prod_mul_distrib ];
      rw [ ← Finset.prod_div_distrib, Finset.prod_congr rfl ] ; intros ; rw [ Nat.cast_sub <| Nat.one_le_iff_ne_zero.mpr <| Nat.Prime.ne_zero <| hps _ ‹_› ] ; ring_nf ; norm_num [ Nat.Prime.ne_zero <| hps _ ‹_› ];
    · assumption

/-
V_function with g(d) = 1/d equals P/φ(P).
-/
lemma V_function_inv_eq_totient_ratio (P : ℕ) (hP : Squarefree P) (hP_pos : 0 < P) :
    V_function (fun d => (1 : ℝ) / d) P P = (P : ℝ) / (Nat.totient P : ℝ) := by
  -- For squarefree $P$, the sum $\sum_{d|P} \frac{1}{\varphi(d)}$ equals $\prod_{p|P} \left(1 + \frac{1}{p-1}\right)$.
  have h_sum : ∑ d ∈ Nat.divisors P, (1 : ℝ) / (Nat.totient d) = ∏ p ∈ Nat.primeFactors P, (1 + 1 / (p - 1 : ℝ)) := by
    -- Since $P$ is squarefree, its divisors are precisely the products of distinct prime factors of $P$.
    have h_divisors : Nat.divisors P = Finset.image (fun s => ∏ p ∈ s, p) (Finset.powerset (Nat.primeFactors P)) := by
      ext d;
      constructor <;> intro hd <;> simp_all +decide [ Nat.mem_divisors, Finset.mem_image, Finset.mem_powerset ];
      · exact ⟨ Nat.primeFactors d, Nat.primeFactors_mono hd.1 hd.2, Nat.prod_primeFactors_of_squarefree <| hP.squarefree_of_dvd hd.1 ⟩;
      · rcases hd with ⟨ s, hs, rfl ⟩ ; exact ⟨ by simpa using Nat.prod_primeFactors_dvd P |> dvd_trans ( by rw [ ← Finset.prod_sdiff hs ] ; aesop ), hP_pos.ne' ⟩ ;
    rw [ h_divisors, Finset.sum_image ];
    · -- Apply the multiplicativity of the totient function to rewrite the sum.
      have h_totient_mul : ∀ s : Finset ℕ, (∀ p ∈ s, Nat.Prime p) → Nat.totient (∏ p ∈ s, p) = ∏ p ∈ s, (p - 1) := by
        intro s hs; induction s using Finset.induction <;> simp_all +decide [ Nat.totient_prime, Nat.totient_mul ] ;
        rw [ Nat.totient_mul, Nat.totient_prime hs.1, ‹φ ( ∏ p ∈ _, p ) = _› ];
        exact Nat.Coprime.prod_right fun p hp => hs.1.coprime_iff_not_dvd.mpr fun h => ‹¬_› <| by have := Nat.prime_dvd_prime_iff_eq hs.1 ( hs.2 p hp ) ; aesop;
      rw [ Finset.sum_congr rfl fun s hs => by rw [ h_totient_mul s fun p hp => Nat.prime_of_mem_primeFactors <| Finset.mem_powerset.mp hs hp ] ];
      simp +decide [ add_comm ( 1 : ℝ ), Finset.prod_add ];
      exact Finset.sum_congr rfl fun x hx => by rw [ Finset.prod_congr rfl ] ; intros; rw [ Nat.cast_pred ( Nat.pos_of_mem_primeFactors ( Finset.mem_powerset.mp hx ‹_› ) ) ] ;
    · intro s hs t ht h_eq; apply_fun fun x => x.primeFactors at h_eq; simp_all +decide [ Finset.subset_iff, Nat.primeFactors_prod ] ;
  -- For squarefree $P$, the sum $\sum_{d|P} \frac{1}{\varphi(d)}$ equals $\prod_{p|P} \left(1 + \frac{1}{p-1}\right)$, which simplifies to $\frac{P}{\varphi(P)}$.
  have h_V_eq : ∑ d ∈ Nat.divisors P, (1 : ℝ) / (Nat.totient d) = (P : ℝ) / (Nat.totient P) := by
    -- By definition of totient function, we know that $\varphi(P) = P \prod_{p|P} (1 - 1/p)$.
    have h_totient : (Nat.totient P : ℝ) = P * ∏ p ∈ Nat.primeFactors P, (1 - 1 / (p : ℝ)) := by
      convert Nat.totient_eq_mul_prod_factors P using 1;
      norm_num [ ← @Rat.cast_inj ℝ ];
    rw [ h_sum, h_totient, div_mul_eq_div_div ];
    rw [ div_self <| by positivity, one_div, ← Finset.prod_inv_distrib ];
    refine Finset.prod_congr rfl fun p hp => ?_ ; rw [ one_add_div, one_sub_div ] <;> norm_num ; ring_nf ; linarith [ Nat.Prime.one_lt ( Nat.prime_of_mem_primeFactors hp ) ] ;
    exact sub_ne_zero_of_ne ( mod_cast Nat.Prime.ne_one ( Nat.prime_of_mem_primeFactors hp ) );
  rw [ ← h_V_eq, V_function ];
  refine' Finset.sum_bij ( fun x hx => x ) _ _ _ _ <;> simp_all +decide [ sqfDivisors ];
  · exact fun a ha ha' => ⟨ Nat.dvd_of_mem_divisors <| Finset.mem_filter.mp ha |>.1, hP_pos.ne' ⟩;
  · exact fun b hb _ => ⟨ Finset.mem_filter.mpr ⟨ Nat.mem_divisors.mpr ⟨ hb, by positivity ⟩, hP.squarefree_of_dvd hb ⟩, Nat.le_of_dvd hP_pos hb ⟩;
  · intro d hd hd'; rw [ hFunction ] ; simp_all +decide [ Nat.totient_eq_div_primeFactors_mul, Nat.prod_primeFactors_dvd ] ;
    rw [ Finset.prod_congr rfl fun x hx => Nat.cast_pred <| Nat.pos_of_mem_primeFactors hx ] ; ring_nf;
    field_simp;
    rw [ Finset.prod_congr rfl fun x hx => one_sub_div ( Nat.cast_ne_zero.mpr <| Nat.ne_of_gt <| Nat.pos_of_mem_primeFactors hx ) ] ; norm_num ; ring_nf

/-- At coprime x, selbergNu equals λ_1². -/
lemma selbergNu_at_coprime' (N P : ℕ) (lambda : ℕ → ℝ) (x : Fin N)
    (hP_pos : 0 < P) (hcop : Nat.gcd x.val P = 1)
    (hsupp : ∀ d, d ∉ sqfDivisors P → lambda d = 0) :
    selbergNu N P lambda x = lambda 1 ^ 2 := by
  unfold selbergNu
  congr 1
  rw [filter_sqfDivisors_coprime hP_pos.ne' (by rwa [Nat.Coprime])]
  simp

/-
The number of x in Fin P coprime to P is φ(P).
-/
lemma card_coprime_fin (P : ℕ) (hP_pos : 0 < P) :
    (Finset.univ.filter (fun x : Fin P => Nat.gcd x.val P = 1)).card
    = Nat.totient P := by
  refine' Finset.card_bij ( fun x hx => x.val ) _ _ _;
  · simp +contextual [ Nat.coprime_comm ];
  · aesop;
  · simp +zetaDelta at *;
    exact fun b hb hb' => ⟨ ⟨ b, hb ⟩, hb'.symm, rfl ⟩

/-
multiPrimeQuadForm is nonneg.
-/
lemma multiPrimeQuadForm_nonneg' (P : ℕ) (hP : Squarefree P) (hP_pos : 0 < P)
    (lambda : ℕ → ℝ) :
    0 ≤ multiPrimeQuadForm P lambda := by
  by_contra h_contra;
  -- Apply the identity to rewrite the sum.
  have h_identity : ∑ x : Fin (P * 1), selbergNu (P * 1) P lambda x = (P * 1 : ℝ) * multiPrimeQuadForm P lambda := by
    convert l2NormSq_multiPrime_eq_quadForm P 1 hP hP_pos ( by positivity ) lambda using 1;
    norm_num;
  exact h_contra <| by nlinarith [ show ( P : ℝ ) > 0 by positivity, show ( ∑ x : Fin ( P * 1 ), selbergNu ( P * 1 ) P lambda x ) ≥ 0 by exact Finset.sum_nonneg fun _ _ => selbergNu_nonneg _ _ _ _ ] ;

/-
The Möbius weights minimize multiPrimeQuadForm: Q(λ) ≥ φ(P)/P.
-/
theorem multiPrimeQuadForm_lower_bound'
    (P : ℕ) (hP : Squarefree P) (hP_pos : 0 < P)
    (lambda : ℕ → ℝ) (hlam1 : lambda 1 = 1)
    (hsupp : ∀ d, d ∉ sqfDivisors P → lambda d = 0) :
    (Nat.totient P : ℝ) / (P : ℝ) ≤ multiPrimeQuadForm P lambda := by
  -- By l2NormSq_multiPrime_eq_quadForm with m=1, we get P * Q(λ) = Σ_{x : Fin P} selbergNu(x).
  have h_sum : (P : ℝ) * multiPrimeQuadForm P lambda = ∑ x : Fin P, selbergNu P P lambda x := by
    convert l2NormSq_multiPrime_eq_quadForm P 1 hP hP_pos zero_lt_one lambda |> Eq.symm using 1 ; norm_num [ Finset.sum_range, Nat.mul_div_cancel_left ];
    rw [ mul_one ];
  -- Since selbergNu is nonneg, we can drop all terms except those coprime to P.
  have h_drop : ∑ x : Fin P, selbergNu P P lambda x ≥ ∑ x ∈ Finset.filter (fun x : Fin P => Nat.gcd x.val P = 1) Finset.univ, selbergNu P P lambda x := by
    exact Finset.sum_le_sum_of_subset_of_nonneg ( Finset.filter_subset _ _ ) fun _ _ _ => selbergNu_nonneg _ _ _ _;
  -- For coprime x, selbergNu(x) = λ₁² = 1 (using selbergNu_at_coprime').
  have h_coprime : ∀ x : Fin P, Nat.gcd x.val P = 1 → selbergNu P P lambda x = 1 := by
    exact fun x hx => by simpa [ hlam1 ] using selbergNu_at_coprime' P P lambda x hP_pos hx hsupp;
  rw [ div_le_iff₀ ( by positivity ) ];
  rw [ mul_comm ];
  exact h_sum.symm ▸ h_drop.trans' ( by rw [ Finset.sum_congr rfl fun x hx => h_coprime x <| Finset.mem_filter.mp hx |>.2 ] ; norm_num [ card_coprime_fin P hP_pos ] )

/-
Q(μ) = 1/V(1/·, P, P).
-/
theorem optimalWeight_quadForm_eq_moebius
    (P : ℕ) (hP : Squarefree P) (hP_pos : 0 < P) :
    multiPrimeQuadForm P (moebiusWeights P) =
      1 / V_function (fun n => (1 : ℝ) / n) P P := by
  rw [ moebius_quadForm_eq, V_function_inv_eq_totient_ratio ];
  · group;
  · assumption;
  · exact hP_pos;
  · assumption;
  · exact hP_pos

/-
Q(λ) ≥ 1/V(1/·, P, P) for any λ with λ₁ = 1.
-/
theorem multiPrimeQuadForm_lower_bound_inv
    (P : ℕ) (hP : Squarefree P) (hP_pos : 0 < P)
    (lambda : ℕ → ℝ) (hlam1 : lambda 1 = 1)
    (hsupp : ∀ d, d ∉ sqfDivisors P → lambda d = 0) :
    1 / V_function (fun n => (1 : ℝ) / n) P P ≤
      multiPrimeQuadForm P lambda := by
  convert multiPrimeQuadForm_lower_bound' P hP hP_pos lambda hlam1 hsupp using 1;
  rw [ V_function_inv_eq_totient_ratio P hP hP_pos, one_div_div ]

/-- Remainder bound at Möbius weights. -/
noncomputable def moebiusRemainderBound (P : ℕ) (remainder : ℕ → ℝ) : ℝ :=
  ∑ d ∈ sqfDivisors P, ∑ e ∈ sqfDivisors P,
    |moebiusWeights P d| * |moebiusWeights P e| * |remainder (Nat.lcm d e)|

end
