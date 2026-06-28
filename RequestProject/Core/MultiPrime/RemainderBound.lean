/-
# Sieve.MultiPrime.RemainderBound

The complete Selberg upper bound for the multi-prime sieve, connecting
a real sieve sequence A, its remainder r(d) = |A_d| - N/d, and the
sifted count |{a ∈ A : gcd(a,P)=1}|.

## Main results

* `selberg_upper_bound_complete` — the complete Selberg upper bound with remainder

Status: ProvedInProject
-/
import Mathlib
import RequestProject.Core.Weights.UpperBound
import RequestProject.Core.MultiPrime.MoebiusWeights
import RequestProject.Core.MultiPrime.JointCount
import RequestProject.Core.MultiPrime.FourierRatio

open Finset BigOperators Nat

noncomputable section

/-- Bridge between `selbergNu` and `sieveWeight`: they are the same squared sum. -/
lemma selbergNu_eq_sieveWeight_sq (N P : ℕ) (lambda : ℕ → ℝ) (x : Fin N) :
    selbergNu N P lambda x =
    (sieveWeight lambda (sqfDivisors P) x.val P) ^ 2 := by
  simp [selbergNu, sieveWeight]

/-
The count of multiples of lcm(d,e) in Finset.range(P*m),
    when d,e are squarefree divisors of P.
-/
lemma finRange_Ad_lcm_card
    (P m : ℕ) (hP_pos : 0 < P) (hm : 0 < m)
    (d e : ℕ) (hd : d ∈ sqfDivisors P) (he : e ∈ sqfDivisors P) :
    ((Finset.range (P * m)).filter (fun a => Nat.lcm d e ∣ a)).card =
    P * m / Nat.lcm d e := by
  convert card_multiples_of_dvd ( P * m ) ( Nat.lcm d e ) ?_ ?_ using 1 <;> norm_num [ Nat.lcm_pos, * ];
  · rw [ Finset.card_filter, Finset.card_filter ];
    refine' Finset.sum_bij ( fun x hx => ⟨ x, by aesop ⟩ ) _ _ _ _ <;> aesop;
  · exact ⟨ Nat.pos_of_mem_divisors ( Finset.filter_subset _ _ hd ), Nat.pos_of_mem_divisors ( Finset.filter_subset _ _ he ) ⟩;
  · exact dvd_mul_of_dvd_left ( Nat.lcm_dvd ( Finset.mem_filter.mp hd |>.2 |> fun x => Nat.dvd_of_mem_divisors <| Finset.mem_filter.mp hd |>.1 ) ( Finset.mem_filter.mp he |>.2 |> fun x => Nat.dvd_of_mem_divisors <| Finset.mem_filter.mp he |>.1 ) ) _

/-
Expand `quadraticMajorantSum` into main term plus error term.
-/
lemma quadraticMajorantSum_eq_mainTerm_plus_errorTerm
    (P m : ℕ) (hP : Squarefree P) (hP_pos : 0 < P) (hm : 0 < m)
    (lambda : ℕ → ℝ)
    (remainder : ℕ → ℝ)
    (hr : ∀ d e : ℕ, d ∈ sqfDivisors P → e ∈ sqfDivisors P →
          (((Finset.range (P * m)).filter
            (fun a => Nat.lcm d e ∣ a)).card : ℝ) =
          (P * m : ℝ) / Nat.lcm d e + remainder (Nat.lcm d e)) :
    quadraticMajorantSum lambda (sqfDivisors P)
      (Finset.range (P * m)) P =
    (P * m : ℝ) * multiPrimeQuadForm P lambda +
    ∑ d ∈ sqfDivisors P, ∑ e ∈ sqfDivisors P,
      lambda d * lambda e * remainder (Nat.lcm d e) := by
  unfold quadraticMajorantSum multiPrimeQuadForm;
  -- Expand the sum using the definition of `sieveWeight`.
  have h_expand : ∑ n ∈ Finset.range (P * m), (sieveWeight lambda (sqfDivisors P) n P) ^ 2 = ∑ d ∈ sqfDivisors P, ∑ e ∈ sqfDivisors P, lambda d * lambda e * (∑ n ∈ Finset.range (P * m), if d ∣ Nat.gcd n P ∧ e ∣ Nat.gcd n P then 1 else 0) := by
    have h_expand : ∀ n ∈ Finset.range (P * m), (sieveWeight lambda (sqfDivisors P) n P) ^ 2 = ∑ d ∈ sqfDivisors P, ∑ e ∈ sqfDivisors P, lambda d * lambda e * (if d ∣ Nat.gcd n P ∧ e ∣ Nat.gcd n P then 1 else 0) := by
      intro n hn
      have h_expand : (sieveWeight lambda (sqfDivisors P) n P) ^ 2 = (∑ d ∈ sqfDivisors P, lambda d * (if d ∣ Nat.gcd n P then 1 else 0)) ^ 2 := by
        simp +decide [ sieveWeight, Finset.sum_ite ];
      rw [ h_expand, sq, Finset.sum_mul ];
      exact Finset.sum_congr rfl fun i hi => by rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_congr rfl fun j hj => by split_ifs <;> ring_nf <;> aesop;
    rw [ Finset.sum_congr rfl h_expand, Finset.sum_comm ];
    exact Finset.sum_congr rfl fun _ _ => by rw [ Finset.sum_comm ] ; exact Finset.sum_congr rfl fun _ _ => by rw [ Finset.mul_sum _ _ _ ] ;
  -- Apply the hypothesis `hr` to each term in the sum.
  have h_apply_hr : ∀ d e : ℕ, d ∈ sqfDivisors P → e ∈ sqfDivisors P → (∑ n ∈ Finset.range (P * m), if d ∣ Nat.gcd n P ∧ e ∣ Nat.gcd n P then 1 else 0) = (P * m : ℝ) / (Nat.lcm d e : ℝ) + remainder (Nat.lcm d e) := by
    simp +zetaDelta at *;
    intro d e hd he; convert hr d e hd he using 1; congr; ext; simp +decide [ Nat.dvd_gcd_iff ] ;
    exact ⟨ fun h => Nat.lcm_dvd h.1.1 h.2.1, fun h => ⟨ ⟨ Nat.dvd_trans ( Nat.dvd_lcm_left _ _ ) h, Nat.dvd_trans ( Nat.dvd_of_mem_divisors ( Finset.mem_filter.mp hd |>.1 ) ) ( dvd_refl _ ) ⟩, Nat.dvd_trans ( Nat.dvd_lcm_right _ _ ) h, Nat.dvd_trans ( Nat.dvd_of_mem_divisors ( Finset.mem_filter.mp he |>.1 ) ) ( dvd_refl _ ) ⟩ ⟩;
  simp_all +decide [ Finset.mul_sum _ _ _, Finset.sum_add_distrib, mul_add, add_mul, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Finset.sum_mul ]

/-
Bound the double error sum by moebiusRemainderBound at Möbius weights.
-/
lemma double_error_le_moebiusRemainderBound
    (P : ℕ) (remainder : ℕ → ℝ) :
    ∑ d ∈ sqfDivisors P, ∑ e ∈ sqfDivisors P,
      moebiusWeights P d * moebiusWeights P e * remainder (Nat.lcm d e) ≤
    moebiusRemainderBound P remainder := by
  refine' Finset.sum_le_sum fun d hd => Finset.sum_le_sum fun e he => _;
  exact le_of_abs_le ( by rw [ abs_mul, abs_mul ] )

/-
The count of elements coprime to P in range(P*m) as a real sum.
-/
lemma siftedCount_le_quadraticMajorantSum
    (P m : ℕ) (hP_pos : 0 < P)
    (lambda : ℕ → ℝ) (hlam_one : lambda 1 = 1) :
    ((Finset.range (P * m)).filter (fun a => Nat.Coprime a P)).card ≤
    quadraticMajorantSum lambda (sqfDivisors P) (Finset.range (P * m)) P := by
  have h_sum_sq_ge_card_coprime : ∑ n ∈ Finset.range (P * m), (sieveWeight lambda (sqfDivisors P) n P) ^ 2 ≥ ∑ n ∈ Finset.range (P * m), (if Nat.Coprime n P then 1 else 0) := by
    apply Finset.sum_le_sum;
    intro i hi; split_ifs <;> norm_num [ sieveWeight_coprime_eq, hlam_one, * ] ;
    · rw [ sieveWeight_coprime_eq ] <;> norm_num [ hlam_one, * ];
      · exact one_mem_sqfDivisors hP_pos.ne';
      · assumption;
    · positivity;
  unfold quadraticMajorantSum; aesop;

/-
The complete Selberg upper bound for the multi-prime sieve.
-/
theorem selberg_upper_bound_complete
    (P m : ℕ) (hP : Squarefree P) (hP_pos : 0 < P) (hm : 0 < m)
    (remainder : ℕ → ℝ)
    (hr : ∀ d ∈ sqfDivisors P, ∀ e ∈ sqfDivisors P,
          (((Finset.range (P * m)).filter
            (fun a => Nat.lcm d e ∣ a)).card : ℝ) =
          (P * m : ℝ) / Nat.lcm d e + remainder (Nat.lcm d e))
    (hlam_one : moebiusWeights P 1 = 1) :
    ((Finset.range (P * m)).filter (fun a => Nat.Coprime a P)).card ≤
      (P * m : ℝ) / V_function (fun n => (1:ℝ)/n) P P +
      moebiusRemainderBound P remainder := by
  refine' le_trans ( siftedCount_le_quadraticMajorantSum P m hP_pos ( moebiusWeights P ) hlam_one ) _;
  rw [ quadraticMajorantSum_eq_mainTerm_plus_errorTerm ];
  any_goals tauto;
  refine' add_le_add _ ( double_error_le_moebiusRemainderBound P remainder );
  rw [ optimalWeight_quadForm_eq_moebius ];
  · ring_nf; norm_num;
  · assumption;
  · positivity

end
