import LiWangWenRepresentation

/-!
# Arbitrary nonzero complex frequency

The change of variable `w = omega*z` is performed on the actual function
and its iterated derivatives. Finite order and explicit exponential-sum
representations are preserved under this linear rescaling.
-/

set_option autoImplicit false
noncomputable section
open Polynomial
open scoped BigOperators

namespace LiWangWen

theorem PowerExponentialBound.comp_const_mul {f : ℂ → ℂ}
    (hf : PowerExponentialBound f) (c : ℂ) :
    PowerExponentialBound (fun z => f (c*z)) := by
  obtain ⟨k,A,hA,hbound⟩ := hf
  refine ⟨k,A*(1+‖c‖)^k, by positivity, fun z => ?_⟩
  apply (hbound (c*z)).trans
  apply Real.exp_le_exp.mpr
  have hnorm : 1+‖c*z‖ ≤ (1+‖c‖)*(1+‖z‖) := by
    rw [norm_mul]
    nlinarith [norm_nonneg c, norm_nonneg z]
  calc
    A*(1+‖c*z‖)^k ≤ A*((1+‖c‖)*(1+‖z‖))^k :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hnorm k) hA
    _ = _ := by rw [mul_pow]; ring

theorem finiteOrder_comp_const_mul {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hfo : CRGOrder.FiniteOrder f) (c : ℂ) :
    CRGOrder.FiniteOrder (fun z => f (c*z)) :=
  ((show PowerExponentialBound f from power_bound_of_finiteOrder hf hfo).comp_const_mul c).finiteOrder

theorem IsExponentialSum.comp_const_mul {f : ℂ → ℂ} (hf : IsExponentialSum f) (c : ℂ) :
    IsExponentialSum (fun z => f (c*z)) := by
  obtain ⟨N,p,a,hrep⟩ := hf
  refine ⟨N, (fun j => (p j).comp (C c * X)), (fun j => a j*c), fun z => ?_⟩
  dsimp only
  rw [hrep]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [eval_comp, eval_mul, eval_C, eval_X, mul_assoc]

/-- The differential coefficients after `w = omega*z`. -/
def frequencyScaledCoefficients {n : ℕ} (ω : ℂ) (P : Fin (n+1) → Polynomial ℂ) :
    Fin (n+1) → Polynomial ℂ := fun j => C (ω^j.val) * P j

theorem frequency_rescaled_leading_value {n : ℕ} {ω : ℂ} (hω : ω ≠ 0)
    {P : Fin (n+1) → Polynomial ℂ} (hlead : (P (Fin.last n)).eval 1 ≠ 0) :
    ((frequencyScaledCoefficients ω P) (Fin.last n)).eval 1 ≠ 0 := by
  simpa only [frequencyScaledCoefficients, eval_mul, eval_C, Fin.val_last] using
    mul_ne_zero (pow_ne_zero n hω) hlead

/-- The rescaled function satisfies the exact frequency-one equation. -/
theorem solves_frequency_rescale {n : ℕ} {ω : ℂ} (hω : ω ≠ 0)
    (P : Fin (n+1) → Polynomial ℂ) {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hsol : ∀ z, ∑ j : Fin (n+1), (P j).eval (Complex.exp (ω*z))*iteratedDeriv j.val f z = 0) :
    Solves (frequencyScaledCoefficients ω P) (fun w => f (ω⁻¹*w)) := by
  intro w
  have hz := hsol (ω⁻¹*w)
  have hcancel : ω*(ω⁻¹*w) = w := by rw [← mul_assoc, mul_inv_cancel₀ hω, one_mul]
  rw [hcancel] at hz
  calc
    (∑ j : Fin (n+1), (frequencyScaledCoefficients ω P j).eval (Complex.exp w)*
        iteratedDeriv j.val (fun w => f (ω⁻¹*w)) w) =
        ∑ j : Fin (n+1), (P j).eval (Complex.exp w)*iteratedDeriv j.val f (ω⁻¹*w) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [iteratedDeriv_comp_const_mul hf.contDiff]
      simp only [frequencyScaledCoefficients, eval_mul, eval_C]
      have hpow : ω^j.val * (ω⁻¹)^j.val = 1 := by
        rw [← mul_pow, mul_inv_cancel₀ hω, one_pow]
      calc
        _ = (ω^j.val * (ω⁻¹)^j.val)*
            ((P j).eval (Complex.exp w)*iteratedDeriv j.val f (ω⁻¹*w)) := by ring
        _ = _ := by rw [hpow, one_mul]
    _ = 0 := hz

/-- The full representation for every nonzero complex frequency and a
leading coefficient nonzero at `exp 0 = 1`. -/
theorem frequency_finiteOrder_solution_isExponentialSum {n : ℕ} {ω : ℂ}
    (hω : ω ≠ 0) {P : Fin (n+1) → Polynomial ℂ}
    (hlead : (P (Fin.last n)).eval 1 ≠ 0)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hfo : CRGOrder.FiniteOrder f)
    (hsol : ∀ z, ∑ j : Fin (n+1),
      (P j).eval (Complex.exp (ω*z))*iteratedDeriv j.val f z = 0) :
    IsExponentialSum f := by
  have hg : Differentiable ℂ (fun w => f (ω⁻¹*w)) :=
    hf.comp ((differentiable_const _).mul differentiable_id)
  have hgrepr := finiteOrder_solution_isExponentialSum_of_leading_eval
    (frequency_rescaled_leading_value hω hlead) hg
    (finiteOrder_comp_const_mul hf hfo ω⁻¹) (solves_frequency_rescale hω P hf hsol)
  have hfback : (fun z => f (ω⁻¹*(ω*z))) = f := by
    funext z
    rw [← mul_assoc, inv_mul_cancel₀ hω, one_mul]
  simpa only [hfback] using hgrepr.comp_const_mul ω

/-- Theorem 3.5's leading `X^gamma` and arbitrary nonzero frequency are
both covered by the actual finite-order representation theorem. -/
theorem frequency_finiteOrder_solution_isExponentialSum_of_leading_power {n γ : ℕ} {ω : ℂ}
    (hω : ω ≠ 0) {P : Fin (n+1) → Polynomial ℂ}
    (hlead : P (Fin.last n) = Polynomial.X^γ)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hfo : CRGOrder.FiniteOrder f)
    (hsol : ∀ z, ∑ j : Fin (n+1),
      (P j).eval (Complex.exp (ω*z))*iteratedDeriv j.val f z = 0) :
    IsExponentialSum f :=
  frequency_finiteOrder_solution_isExponentialSum hω (by simp [hlead]) hf hfo hsol

/-- For entire solutions of the equation, finite order is equivalent to
the explicit finite exponential-sum representation at every frequency. -/
theorem frequency_finiteOrder_iff_isExponentialSum {n γ : ℕ} {ω : ℂ}
    (hω : ω ≠ 0) {P : Fin (n+1) → Polynomial ℂ}
    (hlead : P (Fin.last n) = Polynomial.X^γ)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hsol : ∀ z, ∑ j : Fin (n+1),
      (P j).eval (Complex.exp (ω*z))*iteratedDeriv j.val f z = 0) :
    CRGOrder.FiniteOrder f ↔ IsExponentialSum f :=
  ⟨fun hfo => frequency_finiteOrder_solution_isExponentialSum_of_leading_power
      hω hlead hf hfo hsol,
    IsExponentialSum.finiteOrder⟩

end LiWangWen

#print axioms LiWangWen.PowerExponentialBound.comp_const_mul
#print axioms LiWangWen.finiteOrder_comp_const_mul
#print axioms LiWangWen.IsExponentialSum.comp_const_mul
#print axioms LiWangWen.frequency_rescaled_leading_value
#print axioms LiWangWen.solves_frequency_rescale
#print axioms LiWangWen.frequency_finiteOrder_solution_isExponentialSum
#print axioms LiWangWen.frequency_finiteOrder_solution_isExponentialSum_of_leading_power
#print axioms LiWangWen.frequency_finiteOrder_iff_isExponentialSum
