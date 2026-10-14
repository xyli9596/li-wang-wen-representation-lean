import LiWangWenFourierDecay
import LiWangWenFourierPolynomial
import LiWangWenFiniteOrderRecurrence
import LiWangWenFourierReconstruction

/-!
# Periodic finite-order solutions have finite Fourier support

This is the analytic core of the alternative proof of Lemma 5.1. Finite
order gives faster-than-factorial Fourier decay, while the actual ODE gives
a polynomial recurrence. Their incompatibility forces both Fourier tails
to vanish. The result includes inhomogeneous equations with a residual of
finite Fourier support and makes no Newton-branch assumption.
-/

set_option autoImplicit false
noncomputable section
open Filter Finset
open scoped Topology

namespace LiWangWen

/-- The actual eventual Fourier balance of a monic equation and finite
order force both Fourier tails of its periodic factor to vanish. -/
theorem periodic_finiteOrder_fourier_support_of_balance {n : ℕ}
    (P : Fin (n+1) → Polynomial ℂ) (a : ℂ) (hlead : P (Fin.last n) = 1)
    {p : ℂ → ℂ} (hp : Differentiable ℂ p)
    (hper : Function.Periodic p exponentialPeriod) (hfo : CRGOrder.FiniteOrder p)
    {M : ℕ} (hbalance : ∀ m : ℤ, (M : ℤ) ≤ |m| →
      (∑ j : Fin (n+1), ∑ d ∈ Finset.range ((P j).natDegree+1),
        (P j).coeff d * (((m-d : ℤ) : ℂ)+a)^j.val * verticalFourierCoeff p (m-d)) = 0) :
    ∃ N : ℕ, ∀ m : ℤ, (N : ℤ) ≤ |m| → verticalFourierCoeff p m = 0 := by
  obtain ⟨D,Q,hQ0,hQD,hrec⟩ := exists_fourier_polynomial_recurrence_of_balance
    P a hlead (verticalFourierCoeff p) M hbalance
  exact integer_polynomial_recurrence_finite_support Q hQ0 hQD hrec
    (verticalFourierCoeff_factorial_decay_pos hp hper hfo)
    (verticalFourierCoeff_factorial_decay_neg hp hper hfo)

/-- An entire periodic function of finite order has finite Fourier support
if its actual conjugated monic differential residual has finite support.
This supports the descending induction through a general Floquet block. -/
theorem periodic_finiteOrder_fourier_support_of_residual {n : ℕ}
    (P : Fin (n+1) → Polynomial ℂ) (a : ℂ) (hlead : P (Fin.last n) = 1)
    {p : ℂ → ℂ} (hp : Differentiable ℂ p)
    (hper : Function.Periodic p exponentialPeriod) (hfo : CRGOrder.FiniteOrder p)
    (hres : ∃ M : ℕ, ∀ m : ℤ, (M : ℤ) ≤ |m| →
      verticalFourierCoeff (fun z => ∑ j : Fin (n+1),
        (P j).eval (Complex.exp z)*((shiftedDeriv a)^[j.val] p) z) m = 0) :
    ∃ N : ℕ, ∀ m : ℤ, (N : ℤ) ≤ |m| → verticalFourierCoeff p m = 0 := by
  obtain ⟨M,hM⟩ := hres
  apply periodic_finiteOrder_fourier_support_of_balance P a hlead hp hper hfo (M := M)
  intro m hm
  rw [← verticalFourierCoeff_shiftedOperator P a hp hper]
  exact hM m hm

/-- The homogeneous periodic-factor case follows from the actual equation. -/
theorem periodic_finiteOrder_solution_fourier_support {n : ℕ}
    (P : Fin (n+1) → Polynomial ℂ) (a : ℂ) (hlead : P (Fin.last n) = 1)
    {p : ℂ → ℂ} (hp : Differentiable ℂ p)
    (hper : Function.Periodic p exponentialPeriod) (hfo : CRGOrder.FiniteOrder p)
    (hsol : Solves P (fun z => Complex.exp (a*z)*p z)) :
    ∃ N : ℕ, ∀ m : ℤ, (N : ℤ) ≤ |m| → verticalFourierCoeff p m = 0 := by
  exact periodic_finiteOrder_fourier_support_of_balance P a hlead hp hper hfo
    (M := 0) (fun m _ => verticalFourierCoeff_ode_balance P a hp hper hsol m)

/-- A bounded integer Fourier support is an actual finite set. -/
theorem finite_fourier_support_of_bound {p : ℂ → ℂ}
    (h : ∃ N : ℕ, ∀ m : ℤ, (N : ℤ) ≤ |m| → verticalFourierCoeff p m = 0) :
    (Function.support (verticalFourierCoeff p)).Finite := by
  obtain ⟨N,hN⟩ := h
  apply (Set.finite_Icc (-(N : ℤ)) (N : ℤ)).subset
  intro m hm
  have hlt : |m| < (N : ℤ) := lt_of_not_ge (fun h => hm (hN m h))
  exact ⟨(abs_lt.mp hlt).1.le, (abs_lt.mp hlt).2.le⟩

/-- The periodic scalar factor is an actual finite exponential Laurent sum,
not merely a sequence whose Fourier tail vanishes. -/
theorem periodic_finiteOrder_solution_isExponentialSum {n : ℕ}
    (P : Fin (n+1) → Polynomial ℂ) (a : ℂ) (hlead : P (Fin.last n) = 1)
    {p : ℂ → ℂ} (hp : Differentiable ℂ p)
    (hper : Function.Periodic p exponentialPeriod) (hfo : CRGOrder.FiniteOrder p)
    (hsol : Solves P (fun z => Complex.exp (a*z)*p z)) : IsExponentialSum p :=
  finite_fourier_support_isExponentialSum p hp hper
    (finite_fourier_support_of_bound
      (periodic_finiteOrder_solution_fourier_support P a hlead hp hper hfo hsol))

end LiWangWen

#print axioms LiWangWen.periodic_finiteOrder_fourier_support_of_balance
#print axioms LiWangWen.periodic_finiteOrder_fourier_support_of_residual
#print axioms LiWangWen.periodic_finiteOrder_solution_fourier_support
#print axioms LiWangWen.finite_fourier_support_of_bound
#print axioms LiWangWen.periodic_finiteOrder_solution_isExponentialSum
