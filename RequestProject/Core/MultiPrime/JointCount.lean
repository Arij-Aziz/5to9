/-
# Sieve.MultiPrime.JointCount

Critical lemma: |{x : Fin N | d | x ∧ e | x}| = N / lcm(d,e) when lcm(d,e) | N.

This is the combinatorial engine for the multi-prime L² identity.

Status: ProvedInProject
-/
import Mathlib
import RequestProject.Core.Weights.FourierConnection

open Finset BigOperators

noncomputable section

/-- When lcm(d,e) divides N, the count of elements of Fin N
    divisible by both d and e equals N / lcm(d,e). -/
theorem card_joint_multiples_of_lcm (N d e : ℕ)
    (hN : 0 < N) (hlcm : Nat.lcm d e ∣ N) (hlcm_pos : 0 < Nat.lcm d e) :
    (Finset.univ.filter (fun x : Fin N => d ∣ x.val ∧ e ∣ x.val)).card =
    N / Nat.lcm d e := by
  have h_filter_eq :
      (Finset.univ.filter (fun x : Fin N => d ∣ x.val ∧ e ∣ x.val)) =
      (Finset.univ.filter (fun x : Fin N => Nat.lcm d e ∣ x.val)) := by
    apply Finset.filter_congr
    intro x _
    exact Nat.lcm_dvd_iff.symm
  rw [h_filter_eq]
  exact card_multiples_of_dvd N (Nat.lcm d e) hlcm_pos hlcm

end
