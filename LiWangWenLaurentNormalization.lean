import LiWangWenFourierReconstruction
import LiWangWenPolynomialNormalization

set_option autoImplicit false
noncomputable section
open Polynomial
open scoped BigOperators

namespace LiWangWen

/-- Shift the smallest actual Fourier frequency into the exponential factor.
The remaining polynomial has a nonzero value at the origin. -/
theorem finite_fourier_normalized_lift {p : ℂ → ℂ}
    (hp : Differentiable ℂ p) (hper : Function.Periodic p exponentialPeriod)
    (hs : (Function.support (verticalFourierCoeff p)).Finite) (hne : p ≠ 0) :
    ∃ m : ℤ, ∃ u : Polynomial ℂ, u.eval 0 ≠ 0 ∧
      p = lift (m : ℂ) u := by
  classical
  let s := hs.toFinset
  have hz : ∀ m ∉ s, verticalFourierCoeff p m = 0 := by
    intro m hm
    exact not_not.mp (fun h => hm (hs.mem_toFinset.mpr h))
  have hsn : s.Nonempty := by
    by_contra h
    have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    apply hne
    funext z
    simpa [he] using finite_fourier_reconstruction p hp hper s hz z
  let m := s.min' hsn
  have hm : m ∈ s := Finset.min'_mem s hsn
  have hmin : ∀ l ∈ s, m ≤ l := fun l hl => Finset.min'_le s l hl
  let u : Polynomial ℂ := ∑ l ∈ s,
    C (verticalFourierCoeff p l) * X^(l-m).toNat
  have hdeg (l : ℤ) (hl : l ∈ s) : ((l-m).toNat : ℤ) = l-m :=
    Int.toNat_of_nonneg (sub_nonneg.mpr (hmin l hl))
  have hu : u.eval 0 = verticalFourierCoeff p m := by
    dsimp [u]
    simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    rw [Finset.sum_eq_single m]
    · simp
    · intro l hl hlm
      have hpos : 0 < (l-m).toNat := by
        have hlt : m < l := lt_of_le_of_ne (hmin l hl) (Ne.symm hlm)
        have hd := hdeg l hl
        omega
      simp [zero_pow (Nat.ne_of_gt hpos)]
    · exact fun h => (h hm).elim
  refine ⟨m,u,?_,?_⟩
  · rw [hu]
    exact hs.mem_toFinset.mp hm
  · funext z
    rw [finite_fourier_reconstruction p hp hper s hz z]
    dsimp [lift,u]
    simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    have he : Complex.exp ((m : ℂ)*z) * Complex.exp z ^ (l-m).toNat =
        Complex.exp ((l : ℂ)*z) := by
      rw [← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      have hc : ((l-m).toNat : ℂ) = (l : ℂ)-(m : ℂ) := by
        exact_mod_cast hdeg l hl
      rw [hc]
      ring
    calc
      verticalFourierCoeff p l * Complex.exp ((l : ℂ)*z) =
          verticalFourierCoeff p l *
            (Complex.exp ((m : ℂ)*z) * Complex.exp z ^ (l-m).toNat) := by rw [he]
      _ = _ := by ring

#print axioms finite_fourier_normalized_lift
end LiWangWen
