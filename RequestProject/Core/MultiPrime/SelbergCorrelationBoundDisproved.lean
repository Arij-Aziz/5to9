/-
# Disproof of `selbergNu_correlation_bound`
## Statement (what we wanted to prove)
An earlier attempt proposed the following correlation bound for the 
multi-prime Selberg majorant ν, modeled on
Green–Tao 2007 (Proposition 9.1):
  **Claimed theorem**: For all squarefree P > 0, all m > 0, all sieve weights λ
  with λ₁ = 1, and for every shift h : Fin(P·m),
    |Σ_{x : Fin(P·m)} ν(x) · ν(x + h) / (P·m) − Q(λ)| ≤ correlationBound P m λ h
where:
  • ν(x) = (Σ_{d | gcd(x,P)} λ_d)²   is the multi-prime Selberg majorant
  • Q(λ) = Σ_{d,e ∈ sqfDivisors P} λ_d · λ_e / lcm(d,e)  is the quadratic form
  • correlationBound = Σ_{d,e} |λ_d| · |λ_e| / lcm(d,e)  (the triangle-inequality bound)
In plain English: the average shifted correlation of the Selberg sieve majorant
was claimed to be close to the quadratic form Q(λ) for every shift h, with
error controlled by the correlation bound.
## Why it is false
The statement is false as stated (without a lower bound on N = P·m). A concrete
counterexample is given by P = 2, m = 2 (so N = 4), with λ₁ = λ₂ = 1 and
shift h = 0.
The underlying issue is that the blueprint's equidistribution argument (Sub-step 2)
— which claims that the pair (x mod p, (x+h) mod p) is equidistributed — requires
N to be large relative to P. Without such a hypothesis, the correlation sum can
deviate from Q(λ) beyond the proposed bound.
## What this file contains
We formalize:
1. `selbergNu_correlation_bound_statement` — the exact proposition from the blueprint.
2. `selbergNu_correlation_bound_is_false` — a proof that this proposition is FALSE.
Status: ProvedInProject (disproof)
-/
import Mathlib
import RequestProject.Core.MultiPrime.Setup
import RequestProject.Core.MultiPrime.L2Identity
import RequestProject.Core.MultiPrime.SelbergCorrelation
open Finset BigOperators
noncomputable section
/-- The original proposed theorem statement from the blueprint (C1).
    We show its negation is provable, i.e., this statement is FALSE.
    In English: "For all squarefree P > 0, all m > 0, all sieve weights λ with
    λ₁ = 1, and all shifts h : Fin(P·m), the difference between the average
    shifted correlation Σ_x ν(x)·ν(x+h)/(P·m) and the quadratic form Q(λ) is
    bounded by the correlation bound Σ_{d,e} |λ_d|·|λ_e|/lcm(d,e)." -/
def selbergNu_correlation_bound_statement : Prop :=
  ∀ (P m : ℕ) (hP : Squarefree P) (hP_pos : 0 < P) (hm : 0 < m)
    (lambda : ℕ → ℝ) (hlam_one : lambda 1 = 1)
    (h : Fin (P * m)),
    |∑ x : Fin (P * m),
        selbergNu (P * m) P lambda x *
          selbergNu (P * m) P lambda ⟨(x.val + h.val) % (P * m),
            Nat.mod_lt _ (Nat.mul_pos hP_pos hm)⟩
      / (P * m) - multiPrimeQuadForm P lambda| ≤
    correlationBound P m lambda h
/-- **Disproof**: The blueprint's `selbergNu_correlation_bound` is false.
**In English**: It is NOT the case that, for all squarefree P > 0, all m > 0,
all sieve weights λ with λ₁ = 1, and all shifts h, the average shifted
correlation of the Selberg majorant is within `correlationBound` of Q(λ).
A counterexample exists with P = 2, m = 2 (N = 4), λ₁ = λ₂ = 1, h = 0.
The statement fails because it lacks a hypothesis requiring N = P·m to be
sufficiently large relative to P (needed for equidistribution of residues). -/
theorem selbergNu_correlation_bound_is_false :
    ¬ selbergNu_correlation_bound_statement := by
  unfold selbergNu_correlation_bound_statement
  push_neg
  use 2, 2
  refine' ⟨_, by decide, by decide, _⟩
  · native_decide +revert
  · refine' ⟨fun x => if x = 1 then 1 else if x = 2 then 1 else 0, _, 0, _⟩ <;> norm_num
    unfold correlationBound selbergNu multiPrimeQuadForm
    norm_num [Fin.sum_univ_succ, Finset.sum_filter, Finset.sum_range_succ]
    rw [show sqfDivisors 2 = {1, 2} by native_decide]
    norm_num [Finset.sum_pair]
end
