import LiWangWenGrowth

/-! Direct checks of the explicit solutions in Section 3. These checks alone
make no claim about the dimension of the entire finite-order solution space. -/
set_option autoImplicit false
noncomputable section
open Polynomial
open scoped BigOperators
namespace LiWangWen

def example36Coefficients : Fin 4 → Polynomial ℂ :=
  ![C (16/27) - X, C (-4/3) - 2*X, 3*X, 1]

theorem example36_polynomial_identity :
    transformedOperator example36Coefficients (-4/3) (1-7*X) = 0 := by
  norm_num [transformedOperator, example36Coefficients, Fin.sum_univ_succ,
    Function.iterate_succ_apply', shiftedEuler, derivative_sub, derivative_mul,
    derivative_add, derivative_C, derivative_X]
  apply Polynomial.funext
  intro t
  norm_num [pow_succ]
  ring

theorem example36_solution :
    Solves example36Coefficients (lift (-4/3) (1-7*X)) ∧
    Differentiable ℂ (lift (-4/3) (1-7*X)) ∧
    CRGOrder.FiniteOrder (lift (-4/3) (1-7*X)) :=
  ⟨(transformed_eq_zero_iff _ _ _).mp example36_polynomial_identity,
    lift_entire _ _, (bound_lift _ _).finiteOrder⟩

def example37Coefficients : Fin 4 → Polynomial ℂ :=
  ![C Complex.I * X + 1, C (1+Complex.I)*X+1, X+1, 1]

theorem example37_identity_negI :
    ∑ j, example37Coefficients j * C ((-Complex.I)^j.val) = 0 := by
  norm_num [example37Coefficients, Fin.sum_univ_succ, pow_succ, C_add, C_neg]
  apply Polynomial.funext
  intro t
  norm_num [pow_succ]
  ring_nf
  simp [Complex.I_sq]

theorem example37_identity_negOne :
    ∑ j, example37Coefficients j * C ((-1:ℂ)^j.val) = 0 := by
  norm_num [example37Coefficients, Fin.sum_univ_succ, C_add]
  ring

theorem example37_solution_negI :
    Solves example37Coefficients (fun z => Complex.exp (-Complex.I*z)) := by
  simpa using pure_exponential_solves example37Coefficients (-Complex.I) 1
    example37_identity_negI

theorem example37_solution_negOne :
    Solves example37Coefficients (fun z => Complex.exp (-z)) := by
  simpa using pure_exponential_solves example37Coefficients (-1) 1
    example37_identity_negOne

#print axioms example36_polynomial_identity
#print axioms example36_solution
#print axioms example37_identity_negI
#print axioms example37_identity_negOne
#print axioms example37_solution_negI
#print axioms example37_solution_negOne
end LiWangWen
