import LiWangWenTheorem35Direct
import LiWangWenFrequencyRepresentation

/-! Direct growth route for the arbitrary nonzero frequency in (3.1).
The rescaling identities are shared with the recurrence route; the actual
representation is obtained from the direct Wiman--Valiron bound. -/
set_option autoImplicit false
noncomputable section
open Polynomial
open scoped BigOperators
namespace LiWangWen

/-- The full representation for every nonzero complex frequency and a
leading coefficient nonzero at `exp 0 = 1`. -/
theorem frequency_finiteOrder_solution_isExponentialSum_direct {n : ℕ} {ω : ℂ}
    (hω : ω ≠ 0) {P : Fin (n+1) → Polynomial ℂ}
    (hlead : (P (Fin.last n)).eval 1 ≠ 0)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hfo : CRGOrder.FiniteOrder f)
    (hsol : ∀ z, ∑ j : Fin (n+1),
      (P j).eval (Complex.exp (ω*z))*iteratedDeriv j.val f z = 0) :
    IsExponentialSum f := by
  have hg : Differentiable ℂ (fun w => f (ω⁻¹*w)) :=
    hf.comp ((differentiable_const _).mul differentiable_id)
  have hgrepr := finiteOrder_solution_isExponentialSum_direct
    (frequency_rescaled_leading_value hω hlead) hg
    (finiteOrder_comp_const_mul hf hfo ω⁻¹) (solves_frequency_rescale hω P hf hsol)
  have hfback : (fun z => f (ω⁻¹*(ω*z))) = f := by
    funext z
    rw [← mul_assoc, inv_mul_cancel₀ hω, one_mul]
  simpa only [hfback] using hgrepr.comp_const_mul ω

/-- Theorem 3.5's leading `X^gamma` and arbitrary nonzero frequency are
both covered by the actual finite-order representation theorem. -/
theorem frequency_theorem_3_5_direct {n γ : ℕ} {ω : ℂ}
    (hω : ω ≠ 0) {P : Fin (n+1) → Polynomial ℂ}
    (hlead : P (Fin.last n) = Polynomial.X^γ)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hfo : CRGOrder.FiniteOrder f)
    (hsol : ∀ z, ∑ j : Fin (n+1),
      (P j).eval (Complex.exp (ω*z))*iteratedDeriv j.val f z = 0) :
    IsExponentialSum f :=
  frequency_finiteOrder_solution_isExponentialSum_direct hω (by simp [hlead]) hf hfo hsol

/-- For entire solutions of the equation, finite order is equivalent to
the explicit finite exponential-sum representation at every frequency. -/
theorem frequency_finiteOrder_iff_isExponentialSum_direct {n γ : ℕ} {ω : ℂ}
    (hω : ω ≠ 0) {P : Fin (n+1) → Polynomial ℂ}
    (hlead : P (Fin.last n) = Polynomial.X^γ)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hsol : ∀ z, ∑ j : Fin (n+1),
      (P j).eval (Complex.exp (ω*z))*iteratedDeriv j.val f z = 0) :
    CRGOrder.FiniteOrder f ↔ IsExponentialSum f :=
  ⟨fun hfo => frequency_theorem_3_5_direct
      hω hlead hf hfo hsol,
    IsExponentialSum.finiteOrder⟩


#print axioms frequency_finiteOrder_solution_isExponentialSum_direct
#print axioms frequency_theorem_3_5_direct
#print axioms frequency_finiteOrder_iff_isExponentialSum_direct
end LiWangWen
