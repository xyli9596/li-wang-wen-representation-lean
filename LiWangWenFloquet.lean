import LiWangWenPeriodicity
import InceFloquet

/-!
# Floquet decomposition for the actual exponential-sum equation

The finite-dimensional solution-space argument applies directly to every
entire solution, without a finite-order hypothesis. The leading coefficient
`X^gamma` is nonzero at `exp 0 = 1`, for every natural `gamma`.
Periodic coefficient functions in the conclusion need not be exponential
sums. Their further growth and algebraic classification remain separate.
-/

set_option autoImplicit false
noncomputable section

namespace LiWangWen

/-- The natural period for a nonzero complex frequency. -/
def frequencyPeriod (ω : ℂ) : ℂ := exponentialPeriod / ω

theorem frequencyPeriod_ne_zero {ω : ℂ} (hω : ω ≠ 0) : frequencyPeriod ω ≠ 0 :=
  div_ne_zero exponentialPeriod_ne_zero hω

theorem frequency_coefficients_periodic {n : ℕ}
    (P : Fin (n+1) → Polynomial ℂ) {ω : ℂ} (hω : ω ≠ 0) (j : Fin (n+1)) :
    Function.Periodic (fun z => (P j).eval (Complex.exp (ω*z))) (frequencyPeriod ω) := by
  intro z
  have hmul : ω * frequencyPeriod ω = exponentialPeriod := by
    unfold frequencyPeriod
    field_simp
  simp only [mul_add, hmul, exponentialPeriod, Complex.exp_add,
    Complex.exp_two_pi_mul_I, mul_one]

/-- Arbitrary entire solutions admit scalar Floquet sums at any nonzero
frequency, provided the leading coefficient is nonzero at the origin. -/
theorem frequency_entire_solution_floquet {n : ℕ}
    {P : Fin (n+1) → Polynomial ℂ} {ω : ℂ} (hω : ω ≠ 0)
    (hlead : (P (Fin.last n)).eval 1 ≠ 0) {f : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (hsol : ∀ z, ∑ j, (P j).eval (Complex.exp (ω*z)) * iteratedDeriv j.val f z = 0) :
    IncePeriodic.HasFloquetRepresentation (frequencyPeriod ω) f := by
  apply IncePeriodic.entire_solution_floquet
    (a := fun j z => (P j).eval (Complex.exp (ω*z)))
    (fun j => (P j).differentiable.comp
      (Complex.differentiable_exp.comp (differentiable_const ω |>.mul differentiable_id)))
    (by simpa using hlead) (frequencyPeriod_ne_zero hω)
    (frequency_coefficients_periodic P hω) hf hsol

/-- The paper's leading coefficient `X^gamma` supplies the nonvanishing
hypothesis for every natural `gamma`, including zero. -/
theorem frequency_entire_solution_floquet_of_leading_power {n γ : ℕ}
    {P : Fin (n+1) → Polynomial ℂ} {ω : ℂ} (hω : ω ≠ 0)
    (hlead : P (Fin.last n) = Polynomial.X^γ) {f : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (hsol : ∀ z, ∑ j, (P j).eval (Complex.exp (ω*z)) * iteratedDeriv j.val f z = 0) :
    IncePeriodic.HasFloquetRepresentation (frequencyPeriod ω) f := by
  exact frequency_entire_solution_floquet hω (by simp [hlead]) hf hsol

/-- The frequency-one equation used throughout the paper's core modules. -/
theorem paper_entire_solution_floquet {n γ : ℕ}
    {P : Fin (n+1) → Polynomial ℂ} (hlead : P (Fin.last n) = Polynomial.X^γ)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hsol : Solves P f) :
    IncePeriodic.HasFloquetRepresentation exponentialPeriod f := by
  simpa only [frequencyPeriod, div_one] using
    (frequency_entire_solution_floquet_of_leading_power (ω := 1) one_ne_zero hlead hf
      (by simpa only [one_mul, Solves] using hsol))

end LiWangWen

#print axioms LiWangWen.frequencyPeriod_ne_zero
#print axioms LiWangWen.frequency_coefficients_periodic
#print axioms LiWangWen.frequency_entire_solution_floquet
#print axioms LiWangWen.frequency_entire_solution_floquet_of_leading_power
#print axioms LiWangWen.paper_entire_solution_floquet
