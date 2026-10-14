import LiWangWenLemma51Periodic

/-!
# Removing a common exponential factor from a Fourier recurrence

For arbitrary nonzero polynomial-exponential differential operators the
first nonzero Fourier shift need not be zero. Selecting both extreme
nonzero shifts and translating the index reduces the equation to the
bilateral recurrence theorem. In particular this includes every leading
coefficient `X^gamma`.
-/

set_option autoImplicit false
noncomputable section
open Filter Finset Polynomial
open scoped Topology

namespace LiWangWen

/-- Reindexing an interval beginning at `L` does not change the actual
integer argument of a Fourier coefficient after translation by `L`. -/
theorem fourier_recurrence_sum_shift (Q : ℕ → Polynomial ℂ) (c : ℤ → ℂ)
    {L H : ℕ} (hLH : L ≤ H) (m : ℤ) :
    (∑ d ∈ Finset.range (H-L+1), (Q (L+d)).eval ((m-d : ℤ) : ℂ)*c (m-d)) =
      ∑ d ∈ Finset.Icc L H, (Q d).eval ((m+L-d : ℤ) : ℂ)*c (m+L-d) := by
  apply Finset.sum_bij (fun d _ => L+d)
  · intro d hd
    have hd' : d ≤ H-L := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hd
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro d hd e he hde
    omega
  · intro d hd
    have hd' := Finset.mem_Icc.mp hd
    refine ⟨d-L, Finset.mem_range.mpr (by omega), by omega⟩
  · intro d hd
    have he : m+(L : ℤ)-((L+d : ℕ) : ℤ) = m-(d : ℤ) := by omega
    rw [he]

/-- Any actual nonzero differential operator supplies a nonzero Fourier
recurrence polynomial, without assuming a constant leading coefficient. -/
theorem exists_nonzero_fourierRecurrencePolynomial {n : ℕ}
    (P : Fin (n+1) → Polynomial ℂ) (a : ℂ) (hne : ∃ j, P j ≠ 0) :
    ∃ d : ℕ, fourierRecurrencePolynomial P a d ≠ 0 := by
  obtain ⟨j,hj⟩ := hne
  refine ⟨(P j).natDegree, fun h => ?_⟩
  have hh := (fourierRecurrencePolynomial_eq_zero_iff P a (P j).natDegree).mp h j
  rw [Polynomial.coeff_natDegree] at hh
  exact (Polynomial.leadingCoeff_ne_zero.mpr hj) hh

/-- Selecting the smallest and largest nonzero shift produces a genuine
bilateral recurrence with nonzero endpoint polynomials. An eventual
inhomogeneous balance remains eventual after the required index shift. -/
theorem exists_fourier_polynomial_recurrence_of_nonzero {n : ℕ}
    (P : Fin (n+1) → Polynomial ℂ) (a : ℂ) (hne : ∃ j, P j ≠ 0)
    (c : ℤ → ℂ) (M : ℕ)
    (hbalance : ∀ m : ℤ, (M : ℤ) ≤ |m| →
      (∑ j : Fin (n+1), ∑ d ∈ Finset.range ((P j).natDegree+1),
        (P j).coeff d * (((m-d : ℤ) : ℂ)+a)^j.val * c (m-d)) = 0) :
    ∃ D N : ℕ, ∃ R : ℕ → Polynomial ℂ, R 0 ≠ 0 ∧ R D ≠ 0 ∧
      ∀ m : ℤ, (N : ℤ) ≤ |m| → (∑ d ∈ Finset.range (D+1),
        (R d).eval ((m-d : ℤ) : ℂ)*c (m-d)) = 0 := by
  classical
  let U := Finset.univ.sup (fun j : Fin (n+1) => (P j).natDegree)
  have hU : ∀ j, (P j).natDegree ≤ U := fun j => Finset.le_sup
    (f := fun j => (P j).natDegree) (Finset.mem_univ j)
  let Q : ℕ → Polynomial ℂ := fourierRecurrencePolynomial P a
  let s := (Finset.range (U+1)).filter (fun d => Q d ≠ 0)
  obtain ⟨d0,hd0⟩ := exists_nonzero_fourierRecurrencePolynomial P a hne
  have hd0U : d0 ≤ U := by
    by_contra h
    exact hd0 (fourierRecurrencePolynomial_eq_zero_above P a hU (lt_of_not_ge h))
  have hs : s.Nonempty := ⟨d0, Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (by omega), hd0⟩⟩
  let L := s.min' hs
  let H := s.max' hs
  have hLs : L ∈ s := Finset.min'_mem s hs
  have hHs : H ∈ s := Finset.max'_mem s hs
  have hLH : L ≤ H := Finset.min'_le s H hHs
  have hHU : H ≤ U := by
    have hh := Finset.mem_range.mp (Finset.mem_filter.mp hHs).1
    omega
  refine ⟨H-L, M+L, (fun d => Q (L+d)), ?_, ?_, ?_⟩
  · simpa only [Nat.add_zero] using (Finset.mem_filter.mp hLs).2
  · simpa only [Nat.add_sub_of_le hLH] using (Finset.mem_filter.mp hHs).2
  · intro m hm
    have hm' : (M : ℤ) ≤ |m+(L : ℤ)| := by
      have ht : |m| ≤ |m+(L : ℤ)|+(L : ℤ) := by
        have h := abs_sub (m+(L : ℤ)) (L : ℤ)
        simpa only [add_sub_cancel_right, abs_of_nonneg (Int.natCast_nonneg L)] using h
      have hmcast : (M : ℤ)+(L : ℤ) ≤ |m| := by simpa only [Nat.cast_add] using hm
      omega
    have hbal := fourierRecurrence_uniform_balance_of_balance P a c U hU
      (m+(L : ℤ)) (hbalance _ hm')
    rw [fourier_recurrence_sum_shift Q c hLH]
    have heq : (∑ d ∈ Finset.Icc L H,
        (Q d).eval ((m+L-d : ℤ) : ℂ)*c (m+L-d)) =
        ∑ d ∈ Finset.range (U+1), (Q d).eval ((m+L-d : ℤ) : ℂ)*c (m+L-d) := by
      apply Finset.sum_subset
      · intro d hd
        have hh := Finset.mem_Icc.mp hd
        exact Finset.mem_range.mpr (by omega)
      · intro d hdU hdLH
        have hzero : Q d = 0 := by
          by_contra hne
          have hds : d ∈ s := Finset.mem_filter.mpr ⟨hdU,hne⟩
          exact hdLH (Finset.mem_Icc.mpr
            ⟨Finset.min'_le s d hds, Finset.le_max' s d hds⟩)
        rw [hzero, Polynomial.eval_zero, zero_mul]
    exact heq.trans hbal

/-- Periodic finite-order solutions of every nonzero polynomial-exponential
operator have finite Fourier support when their residual does. -/
theorem periodic_finiteOrder_fourier_support_of_nonzero_residual {n : ℕ}
    (P : Fin (n+1) → Polynomial ℂ) (a : ℂ) (hne : ∃ j, P j ≠ 0)
    {p : ℂ → ℂ} (hp : Differentiable ℂ p)
    (hper : Function.Periodic p exponentialPeriod) (hfo : CRGOrder.FiniteOrder p)
    (hres : ∃ M : ℕ, ∀ m : ℤ, (M : ℤ) ≤ |m| →
      verticalFourierCoeff (fun z => ∑ j : Fin (n+1),
        (P j).eval (Complex.exp z)*((shiftedDeriv a)^[j.val] p) z) m = 0) :
    ∃ N : ℕ, ∀ m : ℤ, (N : ℤ) ≤ |m| → verticalFourierCoeff p m = 0 := by
  obtain ⟨M,hM⟩ := hres
  have hbalance := fun m hm => hM m hm
  simp_rw [verticalFourierCoeff_shiftedOperator P a hp hper] at hbalance
  obtain ⟨D,N,Q,hQ0,hQD,hrec⟩ := exists_fourier_polynomial_recurrence_of_nonzero
    P a hne (verticalFourierCoeff p) M hbalance
  exact integer_polynomial_recurrence_finite_support Q hQ0 hQD hrec
    (verticalFourierCoeff_factorial_decay_pos hp hper hfo)
    (verticalFourierCoeff_factorial_decay_neg hp hper hfo)

/-- Every natural leading power is included, even when every coefficient
of the differential operator has a common positive exponential power. -/
theorem periodic_finiteOrder_fourier_support_of_leading_power {n γ : ℕ}
    (P : Fin (n+1) → Polynomial ℂ) (a : ℂ) (hlead : P (Fin.last n) = Polynomial.X^γ)
    {p : ℂ → ℂ} (hp : Differentiable ℂ p)
    (hper : Function.Periodic p exponentialPeriod) (hfo : CRGOrder.FiniteOrder p)
    (hsol : Solves P (fun z => Complex.exp (a*z)*p z)) :
    ∃ N : ℕ, ∀ m : ℤ, (N : ℤ) ≤ |m| → verticalFourierCoeff p m = 0 := by
  obtain ⟨D,N,Q,hQ0,hQD,hrec⟩ := exists_fourier_polynomial_recurrence_of_nonzero
    P a ⟨Fin.last n, by rw [hlead]; exact pow_ne_zero _ Polynomial.X_ne_zero⟩
    (verticalFourierCoeff p) 0
    (fun m _ => verticalFourierCoeff_ode_balance P a hp hper hsol m)
  exact integer_polynomial_recurrence_finite_support Q hQ0 hQD hrec
    (verticalFourierCoeff_factorial_decay_pos hp hper hfo)
    (verticalFourierCoeff_factorial_decay_neg hp hper hfo)

end LiWangWen

#print axioms LiWangWen.fourier_recurrence_sum_shift
#print axioms LiWangWen.exists_nonzero_fourierRecurrencePolynomial
#print axioms LiWangWen.exists_fourier_polynomial_recurrence_of_nonzero
#print axioms LiWangWen.periodic_finiteOrder_fourier_support_of_nonzero_residual
#print axioms LiWangWen.periodic_finiteOrder_fourier_support_of_leading_power
