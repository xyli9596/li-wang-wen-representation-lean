import LiWangWenFourierRecurrence
import Mathlib.Algebra.Polynomial.Taylor

/-!
# The finite polynomial recurrence of actual Fourier coefficients

The polynomial at shift `d` is `Σ_j coeff(P_j,d) (X+a)^j`.
Its extreme nonzero shifts are obtained from the actual finite supports of
the equation coefficients; they are not extra recurrence assumptions.
-/

set_option autoImplicit false
noncomputable section
open Complex Polynomial Finset
open scoped Topology

namespace LiWangWen

def fourierRecurrenceBase {n : ℕ} (P : Fin (n+1) → Polynomial ℂ) (d : ℕ) : Polynomial ℂ :=
  ∑ j : Fin (n+1), Polynomial.monomial j.val ((P j).coeff d)

def fourierRecurrencePolynomial {n : ℕ} (P : Fin (n+1) → Polynomial ℂ)
    (a : ℂ) (d : ℕ) : Polynomial ℂ :=
  Polynomial.taylor a (fourierRecurrenceBase P d)

theorem fourierRecurrenceBase_coeff {n : ℕ} (P : Fin (n+1) → Polynomial ℂ)
    (d : ℕ) (k : Fin (n+1)) :
    (fourierRecurrenceBase P d).coeff k.val = (P k).coeff d := by
  classical
  simp only [fourierRecurrenceBase, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hj
    simp [show j.val ≠ k.val from fun h => hj (Fin.ext h)]
  · simp

theorem fourierRecurrencePolynomial_eval {n : ℕ} (P : Fin (n+1) → Polynomial ℂ)
    (a : ℂ) (d : ℕ) (x : ℂ) :
    (fourierRecurrencePolynomial P a d).eval x =
      ∑ j : Fin (n+1), (P j).coeff d * (x+a)^j.val := by
  simp [fourierRecurrencePolynomial, fourierRecurrenceBase, Polynomial.eval_finsetSum]

theorem fourierRecurrencePolynomial_eq_zero_iff {n : ℕ}
    (P : Fin (n+1) → Polynomial ℂ) (a : ℂ) (d : ℕ) :
    fourierRecurrencePolynomial P a d = 0 ↔ ∀ j, (P j).coeff d = 0 := by
  rw [fourierRecurrencePolynomial, Polynomial.taylor_eq_zero]
  constructor
  · intro h j
    have hh := congrArg (fun p : Polynomial ℂ => p.coeff j.val) h
    simpa only [fourierRecurrenceBase_coeff, Polynomial.coeff_zero] using hh
  · intro h
    simp [fourierRecurrenceBase, h]

theorem fourierRecurrencePolynomial_zero_ne_zero {n : ℕ}
    (P : Fin (n+1) → Polynomial ℂ) (a : ℂ)
    (hlead : P (Fin.last n) = 1) : fourierRecurrencePolynomial P a 0 ≠ 0 := by
  intro h
  have hh := (fourierRecurrencePolynomial_eq_zero_iff P a 0).mp h (Fin.last n)
  simp [hlead] at hh

theorem fourierRecurrencePolynomial_eq_zero_above {n : ℕ}
    (P : Fin (n+1) → Polynomial ℂ) (a : ℂ) {U d : ℕ}
    (hU : ∀ j, (P j).natDegree ≤ U) (hd : U < d) :
    fourierRecurrencePolynomial P a d = 0 := by
  apply (fourierRecurrencePolynomial_eq_zero_iff P a d).mpr
  intro j
  exact Polynomial.coeff_eq_zero_of_natDegree_lt ((hU j).trans_lt hd)

theorem fourierRecurrence_uniform_balance_of_balance {n : ℕ}
    (P : Fin (n+1) → Polynomial ℂ) (a : ℂ) (c : ℤ → ℂ) (U : ℕ)
    (hU : ∀ j, (P j).natDegree ≤ U) (m : ℤ)
    (h : (∑ j : Fin (n+1), ∑ d ∈ Finset.range ((P j).natDegree+1),
      (P j).coeff d * (((m-d : ℤ) : ℂ)+a)^j.val * c (m-d)) = 0) :
    (∑ d ∈ Finset.range (U+1), (fourierRecurrencePolynomial P a d).eval ((m-d : ℤ) : ℂ) *
      c (m-d)) = 0 := by
  have hsum (j : Fin (n+1)) :
      (∑ d ∈ Finset.range ((P j).natDegree+1),
        (P j).coeff d * (((m-d : ℤ) : ℂ)+a)^j.val * c (m-d)) =
      ∑ d ∈ Finset.range (U+1),
        (P j).coeff d * (((m-d : ℤ) : ℂ)+a)^j.val * c (m-d) := by
    apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right (hU j) 1))
    intro d _ hd
    have hdeg : (P j).natDegree < d := by
      have hnot : (P j).natDegree+1 ≤ d := by simpa only [Finset.mem_range, not_lt] using hd
      omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hdeg, zero_mul, zero_mul]
  simp_rw [hsum] at h
  rw [Finset.sum_comm] at h
  simpa only [fourierRecurrencePolynomial_eval, Finset.sum_mul] using h

/-- For a monic equation, the actual Fourier recurrence has nonzero
polynomials at both endpoint shifts. -/
theorem exists_fourier_polynomial_recurrence_of_balance {n : ℕ}
    (P : Fin (n+1) → Polynomial ℂ) (a : ℂ) (hlead : P (Fin.last n) = 1)
    (c : ℤ → ℂ) (M : ℕ)
    (hbalance : ∀ m : ℤ, (M : ℤ) ≤ |m| →
      (∑ j : Fin (n+1), ∑ d ∈ Finset.range ((P j).natDegree+1),
        (P j).coeff d * (((m-d : ℤ) : ℂ)+a)^j.val * c (m-d)) = 0) :
    ∃ D : ℕ, ∃ Q : ℕ → Polynomial ℂ, Q 0 ≠ 0 ∧ Q D ≠ 0 ∧
      ∀ m : ℤ, (M : ℤ) ≤ |m| → (∑ d ∈ Finset.range (D+1), (Q d).eval ((m-d : ℤ) : ℂ) *
        c (m-d)) = 0 := by
  classical
  let U : ℕ := Finset.univ.sup (fun j : Fin (n+1) => (P j).natDegree)
  have hU : ∀ j, (P j).natDegree ≤ U := fun j => Finset.le_sup (f := fun j => (P j).natDegree)
    (Finset.mem_univ j)
  let Q : ℕ → Polynomial ℂ := fourierRecurrencePolynomial P a
  let s : Finset ℕ := (Finset.range (U+1)).filter (fun d => Q d ≠ 0)
  have hQ0 : Q 0 ≠ 0 := fourierRecurrencePolynomial_zero_ne_zero P a hlead
  have h0s : 0 ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hQ0⟩
  have hsn : s.Nonempty := ⟨0,h0s⟩
  let D : ℕ := s.max' hsn
  have hDs : D ∈ s := Finset.max'_mem s hsn
  have hDU : D ≤ U := by
    have hh := Finset.mem_range.mp (Finset.mem_filter.mp hDs).1
    omega
  refine ⟨D,Q,hQ0,(Finset.mem_filter.mp hDs).2,?_⟩
  intro m hm
  have hbal := fourierRecurrence_uniform_balance_of_balance P a c U hU m (hbalance m hm)
  have hsum : (∑ d ∈ Finset.range (D+1), (Q d).eval ((m-d : ℤ) : ℂ) *
      c (m-d)) =
      ∑ d ∈ Finset.range (U+1), (Q d).eval ((m-d : ℤ) : ℂ) *
        c (m-d) := by
    apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hDU 1))
    intro d hdU hdD
    have hdgt : D < d := by
      have hh : D+1 ≤ d := by simpa only [Finset.mem_range, not_lt] using hdD
      omega
    have hzero : Q d = 0 := by
      by_contra hne
      have hds : d ∈ s := Finset.mem_filter.mpr ⟨hdU,hne⟩
      exact (not_le_of_gt hdgt) (Finset.le_max' s d hds)
    rw [hzero, Polynomial.eval_zero, zero_mul]
  exact hsum.trans hbal

/-- The homogeneous recurrence follows directly from the actual monic ODE. -/
theorem exists_fourier_polynomial_recurrence {n : ℕ}
    (P : Fin (n+1) → Polynomial ℂ) (a : ℂ) (hlead : P (Fin.last n) = 1)
    {p : ℂ → ℂ} (hp : Differentiable ℂ p)
    (hper : Function.Periodic p exponentialPeriod)
    (hsol : Solves P (fun z => Complex.exp (a*z)*p z)) :
    ∃ D : ℕ, ∃ Q : ℕ → Polynomial ℂ, Q 0 ≠ 0 ∧ Q D ≠ 0 ∧
      ∀ m : ℤ, (∑ d ∈ Finset.range (D+1), (Q d).eval ((m-d : ℤ) : ℂ) *
        verticalFourierCoeff p (m-d)) = 0 := by
  obtain ⟨D,Q,hQ0,hQD,hrec⟩ := exists_fourier_polynomial_recurrence_of_balance P a hlead
    (verticalFourierCoeff p) 0 (fun m _ => verticalFourierCoeff_ode_balance P a hp hper hsol m)
  exact ⟨D,Q,hQ0,hQD,fun m => hrec m (abs_nonneg m)⟩

end LiWangWen

#print axioms LiWangWen.fourierRecurrenceBase_coeff
#print axioms LiWangWen.fourierRecurrencePolynomial_eval
#print axioms LiWangWen.fourierRecurrencePolynomial_eq_zero_iff
#print axioms LiWangWen.fourierRecurrencePolynomial_zero_ne_zero
#print axioms LiWangWen.fourierRecurrencePolynomial_eq_zero_above
#print axioms LiWangWen.fourierRecurrence_uniform_balance_of_balance
#print axioms LiWangWen.exists_fourier_polynomial_recurrence_of_balance
#print axioms LiWangWen.exists_fourier_polynomial_recurrence
