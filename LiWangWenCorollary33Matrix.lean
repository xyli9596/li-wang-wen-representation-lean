import LiWangWenCorollary33
import LiWangWenTheorem31

/-! Corollary 3.3 in the literal Q M matrix notation, with two independently
proved routes to its nontrivial finite-order solution extraction. -/
set_option autoImplicit false
noncomputable section
open Polynomial
namespace LiWangWen

/-- Nontrivial finite-order solvability is equivalent to a normalized
nonzero polynomial solution of the printed Q M equation, with root exponent.
This proof uses the direct Wiman--Valiron route. -/
theorem corollary_3_3_matrix {n : ℕ} {P : Fin (n+1) → Polynomial ℂ}
    (hlead : P (Fin.last n) = 1) :
    (∃ f : ℂ → ℂ, Differentiable ℂ f ∧ CRGOrder.FiniteOrder f ∧
      Solves P f ∧ f ≠ 0) ↔
    (∃ a : ℂ, ∃ u : Polynomial ℂ, u.eval 0 ≠ 0 ∧
      paperMatrixOperator P a u = 0 ∧ indicial P a = 0) := by
  simpa only [paperMatrixOperator_eq_transformed] using corollary_3_3 hlead

/-- The same exact Q M equivalence via factorial recurrences, independently
of the direct Wiman--Valiron proof. -/
theorem corollary_3_3_matrix_recurrence {n : ℕ} {P : Fin (n+1) → Polynomial ℂ}
    (hlead : P (Fin.last n) = 1) :
    (∃ f : ℂ → ℂ, Differentiable ℂ f ∧ CRGOrder.FiniteOrder f ∧
      Solves P f ∧ f ≠ 0) ↔
    (∃ a : ℂ, ∃ u : Polynomial ℂ, u.eval 0 ≠ 0 ∧
      paperMatrixOperator P a u = 0 ∧ indicial P a = 0) := by
  simpa only [paperMatrixOperator_eq_transformed] using corollary_3_3_recurrence hlead

#print axioms corollary_3_3_matrix
#print axioms corollary_3_3_matrix_recurrence
end LiWangWen
