import LiWangWenRepresentation

set_option autoImplicit false
noncomputable section
open Polynomial
open scoped BigOperators

namespace LiWangWen

theorem verticalFourierCoeff_floquetContribution (a : ℂ) {p : ℂ → ℂ}
    (hp : Differentiable ℂ p) (hper : Function.Periodic p exponentialPeriod)
    (l d j : ℕ) (m : ℤ) :
    verticalFourierCoeff (floquetMonomialContribution a p l d j) m =
      (∑ i ∈ Finset.range (d+1), (d.choose i : ℂ) *
        (Polynomial.derivative^[i] ((X : Polynomial ℂ)^l)).coeff j *
        ((m : ℂ)+a)^(d-i)) * verticalFourierCoeff p m := by
  unfold floquetMonomialContribution
  rw [verticalFourierCoeff_sum]
  · simp_rw [verticalFourierCoeff_const_mul,
      verticalFourierCoeff_iterate_shiftedDeriv a hp hper, ← mul_assoc]
    exact (Finset.sum_mul _ _ _).symm
  · intro i hi
    exact continuous_const.mul (iterate_shiftedDeriv_entire a hp (d-i)).continuous

/-- At the lowest occupied Fourier frequency, the largest occupied monomial
 degree forces the indicial equation. Higher exponential groups cannot
 contribute, and higher monomial degrees have zero coefficient there. -/
theorem floquet_indicial_root_at_lowest_frequency {n : ℕ}
    {P : Fin (n+1) → Polynomial ℂ} (a : ℂ) (k : ℕ) (p : ℕ → ℂ → ℂ)
    (hp : ∀ l < k, Differentiable ℂ (p l) ∧ Function.Periodic (p l) exponentialPeriod)
    (hsol : Solves P (fun z => Complex.exp (a*z)*∑ l ∈ Finset.range k, z^l*p l z))
    (m : ℤ) (hlow : ∀ l < k, ∀ t < m, verticalFourierCoeff (p l) t = 0)
    {j : ℕ} (hj : j < k) (hne : verticalFourierCoeff (p j) m ≠ 0)
    (hhigher : ∀ l < k, j < l → verticalFourierCoeff (p l) m = 0) :
    indicial P (a+(m : ℂ)) = 0 := by
  let G (d : Fin (n+1)) (l : ℕ) : ℂ → ℂ :=
    fun z => (P d).eval (Complex.exp z)*floquetMonomialContribution a (p l) l d.val j z
  have hG (d : Fin (n+1)) (l : ℕ) (hl : l < k) : Continuous (G d l) :=
    ((P d).continuous.comp Complex.continuous_exp).mul
      (floquetMonomialContribution_entire a (hp l hl).1 l d.val j).continuous
  have hfcoeff (d : Fin (n+1)) (l : ℕ) (hl : l < k) :
      verticalFourierCoeff (G d l) m = (P d).coeff 0 *
        verticalFourierCoeff (floquetMonomialContribution a (p l) l d.val j) m := by
    rw [verticalFourierCoeff_polynomial_exp_mul _
      (floquetMonomialContribution_entire a (hp l hl).1 l d.val j).continuous]
    rw [Finset.sum_eq_single 0]
    · simp
    · intro t ht ht0
      rw [verticalFourierCoeff_floquetContribution a (hp l hl).1 (hp l hl).2]
      have htm : m-(t : ℤ) < m := by omega
      rw [hlow l hl _ htm,mul_zero,mul_zero]
    · simp
  have he : (fun z => ∑ d : Fin (n+1), ∑ l ∈ Finset.range k, G d l z) = 0 := by
    funext z
    simpa only [G,Finset.mul_sum,Pi.zero_apply] using
      floquet_block_coefficient_equation a k p hp hsol j z
  have hz := congrArg (fun f : ℂ → ℂ => verticalFourierCoeff f m) he
  rw [verticalFourierCoeff_sum] at hz
  · have hinner (d : Fin (n+1)) :
        verticalFourierCoeff (fun z => ∑ l ∈ Finset.range k, G d l z) m =
          (P d).coeff 0 * ((m : ℂ)+a)^d.val * verticalFourierCoeff (p j) m := by
      rw [verticalFourierCoeff_sum]
      · rw [Finset.sum_eq_single j]
        · rw [hfcoeff d j hj]
          have hdiag : floquetMonomialContribution a (p j) j d.val j =
              (shiftedDeriv a)^[d.val] (p j) :=
            funext (fun z => floquetMonomialContribution_diagonal a (p j) j d.val z)
          rw [hdiag,verticalFourierCoeff_iterate_shiftedDeriv a (hp j hj).1 (hp j hj).2]
          ring
        · intro l hl hlj
          have hlk := Finset.mem_range.mp hl
          rw [hfcoeff d l hlk]
          rcases lt_or_gt_of_ne hlj with hlt | hgt
          · have hez : floquetMonomialContribution a (p l) l d.val j = 0 :=
              funext (fun z => floquetMonomialContribution_eq_zero_of_lt a (p l) hlt d.val z)
            simp [hez,verticalFourierCoeff,fourierWeight]
          · rw [verticalFourierCoeff_floquetContribution a (hp l hlk).1 (hp l hlk).2,
              hhigher l hlk hgt,mul_zero,mul_zero]
        · exact fun h => (h (Finset.mem_range.mpr hj)).elim
      · intro l hl
        exact hG d l (Finset.mem_range.mp hl)
    simp_rw [hinner] at hz
    have hzero : verticalFourierCoeff (0 : ℂ → ℂ) m = 0 := by
      simp [verticalFourierCoeff,fourierWeight]
    rw [hzero,← Finset.sum_mul] at hz
    have hfactor : (∑ d : Fin (n+1), (P d).coeff 0 * ((m : ℂ)+a)^d.val) =
        indicial P (a+(m : ℂ)) := by
      simp only [indicial,coeff_zero_eq_eval_zero,add_comm]
    rw [hfactor] at hz
    exact (mul_eq_zero.mp hz).resolve_right hne
  · intro d hd
    apply continuous_finsetSum
    intro l hl
    exact hG d l (Finset.mem_range.mp hl)

#print axioms verticalFourierCoeff_floquetContribution
#print axioms floquet_indicial_root_at_lowest_frequency
end LiWangWen
