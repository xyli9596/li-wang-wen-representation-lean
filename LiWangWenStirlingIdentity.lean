import Mathlib.Data.Complex.Basic
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.RingTheory.Binomial

set_option autoImplicit false
noncomputable section
open Polynomial
open scoped BigOperators

namespace LiWangWen

/-- Power-to-falling-factorial conversion with the actual Stirling numbers
 of the second kind used in the paper's matrix `M`. -/
theorem power_eq_stirling_descPochhammer (x : ℂ) (n : ℕ) :
    x^n = ∑ k ∈ Finset.range (n+1), (Nat.stirlingSecond n k : ℂ)*
      (descPochhammer ℂ k).eval x := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep (k : ℕ) : x*(descPochhammer ℂ k).eval x =
        (descPochhammer ℂ (k+1)).eval x + (k : ℂ)*(descPochhammer ℂ k).eval x := by
      rw [descPochhammer_succ_right]
      simp only [eval_mul,eval_sub,eval_X,eval_natCast]
      ring
    rw [pow_succ',ih,Finset.mul_sum]
    have hsum : (∑ k ∈ Finset.range (n+1), x*((Nat.stirlingSecond n k : ℂ)*
        (descPochhammer ℂ k).eval x)) =
        (∑ k ∈ Finset.range (n+1), (Nat.stirlingSecond n k : ℂ)*
          (descPochhammer ℂ (k+1)).eval x) +
        (∑ k ∈ Finset.range (n+1), (k : ℂ)*(Nat.stirlingSecond n k : ℂ)*
          (descPochhammer ℂ k).eval x) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      rw [mul_left_comm x, hstep]
      ring
    rw [hsum]
    have hlast : (∑ k ∈ Finset.range (n+1), (k : ℂ)*(Nat.stirlingSecond n k : ℂ)*
        (descPochhammer ℂ k).eval x) =
        ∑ k ∈ Finset.range (n+2), (k : ℂ)*(Nat.stirlingSecond n k : ℂ)*
          (descPochhammer ℂ k).eval x := by
      conv_rhs => rw [Finset.sum_range_succ]
      simp [Nat.stirlingSecond_eq_zero_of_lt (Nat.lt_succ_self n)]
    rw [hlast,Finset.sum_range_succ' (fun k =>
      (k : ℂ)*(Nat.stirlingSecond n k : ℂ)*(descPochhammer ℂ k).eval x),
      Finset.sum_range_succ' (fun k => (Nat.stirlingSecond (n+1) k : ℂ)*
        (descPochhammer ℂ k).eval x)]
    simp only [Nat.cast_zero,zero_mul,Nat.stirlingSecond_succ_zero,add_zero]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Nat.stirlingSecond_succ_succ]
    push_cast
    ring

#print axioms power_eq_stirling_descPochhammer
end LiWangWen
