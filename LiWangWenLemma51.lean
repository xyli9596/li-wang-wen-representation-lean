import LiWangWenFrequencyRepresentation
import LiWangWenExponentialSumGrowth

/-!
# Lemma 5.1: order one and finite positive type

This completed proof uses the independent Fourier-recurrence representation
argument. It does not claim that the paper's Wiman--Valiron paragraph follows
merely by excluding powers different from one. A direct repair preserving that
paragraph is a separate proof route.
-/

noncomputable section

namespace LiWangWen

/-- The actual statement of Lemma 5.1, including nonpolynomiality and mean type. -/
theorem lemma_5_1 {n : ℕ} {P : Fin (n+1) → Polynomial ℂ}
    (hlead : P (Fin.last n) = 1) {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hfo : CRGOrder.FiniteOrder f)
    (hnp : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z)
    (hsol : Solves P f) :
    CRGOrder.IsOrder f 1 ∧ LevinGrowth.FinitePositiveType f 1 := by
  have h := finiteOrder_solution_isExponentialSum hlead hf hfo hsol
  exact ⟨h.isOrder_one hnp, h.finitePositiveType_one hnp⟩

/-- The same growth conclusion holds for every leading power `X^gamma`. -/
theorem leading_power_solution_order_and_type {n γ : ℕ}
    {P : Fin (n+1) → Polynomial ℂ} (hlead : P (Fin.last n) = Polynomial.X^γ)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hfo : CRGOrder.FiniteOrder f)
    (hnp : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z) (hsol : Solves P f) :
    CRGOrder.IsOrder f 1 ∧ LevinGrowth.FinitePositiveType f 1 := by
  have h := finiteOrder_solution_isExponentialSum_of_leading_power hlead hf hfo hsol
  exact ⟨h.isOrder_one hnp, h.finitePositiveType_one hnp⟩

/-- Frequency rescaling preserves the full order-one, positive-type conclusion. -/
theorem frequency_solution_order_and_type {n γ : ℕ}
    {P : Fin (n+1) → Polynomial ℂ} {ω : ℂ} (hω : ω ≠ 0)
    (hlead : P (Fin.last n) = Polynomial.X^γ)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hfo : CRGOrder.FiniteOrder f)
    (hnp : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z)
    (hsol : ∀ z, ∑ j, (P j).eval (Complex.exp (ω*z)) * iteratedDeriv j.val f z = 0) :
    CRGOrder.IsOrder f 1 ∧ LevinGrowth.FinitePositiveType f 1 := by
  have h := frequency_finiteOrder_solution_isExponentialSum_of_leading_power
    hω hlead hf hfo hsol
  exact ⟨h.isOrder_one hnp, h.finitePositiveType_one hnp⟩

#print axioms lemma_5_1
#print axioms leading_power_solution_order_and_type
#print axioms frequency_solution_order_and_type
end LiWangWen
