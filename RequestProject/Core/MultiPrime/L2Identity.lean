/-
# Sieve.MultiPrime.L2Identity

Main theorem: Σ_x ν(x) = (P·m) · Q(λ, sqfDivisors P)

where ν(x) = (Σ_{d | gcd(x,P)} λ_d)² is the multi-prime Selberg majorant
and Q(λ) = Σ_{d,e} λ_d · λ_e / lcm(d,e) is the quadratic form.

Status: ProvedInProject
-/
import Mathlib
import RequestProject.Core.MultiPrime.JointCount
import RequestProject.Core.MultiPrime.Setup

open Finset BigOperators

noncomputable section

/-- d | gcd(n, P) ↔ d | n, when d | P -/
lemma dvd_gcd_iff_dvd_of_dvd_snd {d P n : ℕ} (hdP : d ∣ P) :
    d ∣ Nat.gcd n P ↔ d ∣ n :=
  ⟨fun h => dvd_trans h (Nat.gcd_dvd_left n P),
   fun h => Nat.dvd_gcd h hdP⟩

/-- The multi-prime quadratic form:
    Q(λ) = Σ_{d,e ∈ sqfDivisors P} λ_d · λ_e / lcm(d,e) -/
def multiPrimeQuadForm (P : ℕ) (lambda : ℕ → ℝ) : ℝ :=
  ∑ d ∈ sqfDivisors P, ∑ e ∈ sqfDivisors P,
    lambda d * lambda e / (Nat.lcm d e : ℝ)

/-- Step 1+2: Rewrite selbergNu as a double sum with indicators. -/
lemma selbergNu_as_double_sum (N P : ℕ) (lambda : ℕ → ℝ) (x : Fin N) :
    selbergNu N P lambda x =
    ∑ d ∈ sqfDivisors P, ∑ e ∈ sqfDivisors P,
      (if d ∣ Nat.gcd x.val P then lambda d else 0) *
      (if e ∣ Nat.gcd x.val P then lambda e else 0) := by
  unfold selbergNu
  have h1 : ∑ d ∈ (sqfDivisors P).filter (fun d => d ∣ Nat.gcd x.val P), lambda d =
      ∑ d ∈ sqfDivisors P, if d ∣ Nat.gcd x.val P then lambda d else 0 :=
    Finset.sum_filter _ _
  rw [h1, sq, Finset.sum_mul]
  congr 1; ext d
  rw [Finset.mul_sum]

/-- For squarefree divisors d, e of P: lcm(d,e) divides P. -/
lemma lcm_dvd_of_sqfDivisors {P d e : ℕ} (hd : d ∈ sqfDivisors P) (he : e ∈ sqfDivisors P) :
    Nat.lcm d e ∣ P := by
  exact Nat.lcm_dvd (mem_sqfDivisors.mp hd).1 (mem_sqfDivisors.mp he).1

/-- For squarefree divisors d, e of P with P > 0: lcm(d,e) > 0. -/
lemma lcm_pos_of_sqfDivisors {P d e : ℕ} (hP_pos : 0 < P)
    (hd : d ∈ sqfDivisors P) (he : e ∈ sqfDivisors P) :
    0 < Nat.lcm d e := by
  have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos (mem_sqfDivisors.mp hd).1 hP_pos
  have he_pos : 0 < e := Nat.pos_of_dvd_of_pos (mem_sqfDivisors.mp he).1 hP_pos
  exact Nat.pos_of_ne_zero (by intro h; simp [Nat.lcm_eq_zero_iff] at h; omega)

/-
Step 3+4: The inner sum (over x) of indicator products equals
    lambda_d * lambda_e * (N / lcm(d,e))
    when d, e are squarefree divisors of P and N = P * m.
-/
lemma inner_sum_eq_count (P m : ℕ) (hP_pos : 0 < P) (hm : 0 < m)
    (lambda : ℕ → ℝ)
    {d e : ℕ} (hd : d ∈ sqfDivisors P) (he : e ∈ sqfDivisors P) :
    ∑ x : Fin (P * m),
      (if d ∣ Nat.gcd x.val P then lambda d else 0) *
      (if e ∣ Nat.gcd x.val P then lambda e else 0) =
    lambda d * lambda e * ((P * m) / (Nat.lcm d e : ℝ)) := by
  have h_double_sum : ∑ x : Fin (P * m), (if d ∣ Nat.gcd x.val P then lambda d else 0) * (if e ∣ Nat.gcd x.val P then lambda e else 0) = lambda d * lambda e * ((Finset.univ.filter (fun x : Fin (P * m) => d ∣ x.val ∧ e ∣ x.val)).card : ℝ) := by
    rw [ Finset.card_filter ];
    push_cast [ Finset.mul_sum _ _ _ ];
    refine' Finset.sum_congr rfl fun x hx => _;
    split_ifs <;> simp_all +decide [ Nat.dvd_gcd_iff ];
    · exact False.elim <| ‹¬e ∣ P› <| Nat.dvd_trans ( Nat.dvd_of_mem_divisors <| Finset.filter_subset _ _ he ) <| dvd_refl _;
    · exact False.elim <| ‹¬d ∣ P› <| dvd_trans ( by aesop ) <| mem_sqfDivisors.mp hd |>.1;
    · exact False.elim <| ‹¬d ∣ P› <| dvd_trans ( by aesop ) <| mem_sqfDivisors.mp hd |>.1;
  convert h_double_sum using 2;
  rw [ card_joint_multiples_of_lcm ];
  · rw [ Nat.cast_div_charZero ];
    · norm_cast;
    · exact dvd_mul_of_dvd_left ( lcm_dvd_of_sqfDivisors hd he ) _;
  · positivity;
  · exact dvd_mul_of_dvd_left ( lcm_dvd_of_sqfDivisors hd he ) _;
  · exact Nat.lcm_pos ( Nat.pos_of_mem_divisors ( Finset.mem_filter.mp hd |>.1 ) ) ( Nat.pos_of_mem_divisors ( Finset.mem_filter.mp he |>.1 ) )

/-
**Main theorem**: The sum of the multi-prime Selberg majorant equals
    N times the quadratic form Q(λ).
-/
theorem l2NormSq_multiPrime_eq_quadForm
    (P m : ℕ) (hP : Squarefree P) (hP_pos : 0 < P) (hm : 0 < m)
    (lambda : ℕ → ℝ) :
    ∑ x : Fin (P * m), selbergNu (P * m) P lambda x =
    (P * m : ℝ) * multiPrimeQuadForm P lambda := by
  -- The sum of the Selbergν function can be expressed as a double sum over the squarefree divisors of P, which is exactly the quadratic form Q(λ).
  have h_double_sum : ∑ x : Fin (P * m), selbergNu (P * m) P lambda x = ∑ d ∈ sqfDivisors P, ∑ e ∈ sqfDivisors P, lambda d * lambda e * ((P * m) / (Nat.lcm d e : ℝ)) := by
    rw [ Finset.sum_congr rfl fun x hx => selbergNu_as_double_sum _ _ _ _ ];
    rw [ Finset.sum_comm, Finset.sum_congr rfl ];
    intro d hd; rw [ Finset.sum_comm ] ; refine' Finset.sum_congr rfl fun e he => _ ;
    convert inner_sum_eq_count P m hP_pos hm lambda hd he using 1;
  unfold multiPrimeQuadForm; simp +decide [ h_double_sum, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] ;

end