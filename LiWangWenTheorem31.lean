import LiWangWenMatrix31
import LiWangWenPolynomialNormalization

/-! Theorem 3.1 with its printed matrices and the normalization needed for
its indicial-root assertion. No finite-order or matrix correspondence is
assumed as a premise of the fixed polynomial-ansatz equivalence. -/
set_option autoImplicit false
noncomputable section
open Polynomial
namespace LiWangWen

/-- Theorem 3.1 for a fixed polynomial ansatz: the exact Q M equation is
necessary and sufficient for an entire finite-order solution. The statement
also permits nonmonic coefficient families, so contains P_n = 1. -/
theorem theorem_3_1 {n : ℕ} (P : Fin (n+1) → Polynomial ℂ)
    (a : ℂ) (u : Polynomial ℂ) :
    paperMatrixOperator P a u = 0 ↔
      Differentiable ℂ (lift a u) ∧ CRGOrder.FiniteOrder (lift a u) ∧
        Solves P (lift a u) := by
  constructor
  · intro h
    exact ⟨lift_entire a u, (bound_lift a u).finiteOrder,
      (paperMatrix_eq_zero_iff P a u).mp h⟩
  · intro h
    exact (paperMatrix_eq_zero_iff P a u).mpr h.2.2

/-- For a normalized ansatz, the exponent is an actual indicial root. -/
theorem paperMatrix_indicial_root_of_normalized {n : ℕ}
    (P : Fin (n+1) → Polynomial ℂ) (a : ℂ) (u : Polynomial ℂ)
    (hu : u.eval 0 ≠ 0) (hmat : paperMatrixOperator P a u = 0) :
    indicial P a = 0 :=
  indicial_eq_zero_of_normalized_solution P a u hu
    ((paperMatrix_eq_zero_iff P a u).mp hmat)

/-- Every nonzero polynomial matrix solution can absorb its zero at the
origin into the exponent; the resulting matrix equation has a root exponent.
This is the precise normalization of the paper's additional claim (3.4). -/
theorem normalize_paperMatrix_solution {n : ℕ}
    (P : Fin (n+1) → Polynomial ℂ) (a : ℂ) {u : Polynomial ℂ}
    (hu : u ≠ 0) (hmat : paperMatrixOperator P a u = 0) :
    ∃ k : ℕ, ∃ v : Polynomial ℂ, v.eval 0 ≠ 0 ∧
      lift a u = lift (a+(k : ℂ)) v ∧
      paperMatrixOperator P (a+(k : ℂ)) v = 0 ∧
      indicial P (a+(k : ℂ)) = 0 := by
  simpa only [paperMatrixOperator_eq_transformed] using
    normalize_polynomial_lift_solution P a hu
      ((paperMatrix_eq_zero_iff P a u).mp hmat)

#print axioms theorem_3_1
#print axioms paperMatrix_indicial_root_of_normalized
#print axioms normalize_paperMatrix_solution
end LiWangWen
