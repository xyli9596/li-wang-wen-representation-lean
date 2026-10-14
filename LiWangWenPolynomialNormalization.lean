import LiWangWenGrowth
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree

set_option autoImplicit false
noncomputable section
open Polynomial

namespace LiWangWen

/-- Factor the full zero at the origin; the remaining polynomial is normalized. -/
theorem polynomial_origin_factor {u : Polynomial ℂ} (hu : u ≠ 0) :
    ∃ k : ℕ, ∃ v : Polynomial ℂ, v.eval 0 ≠ 0 ∧ u = X^k*v := by
  let k := u.natTrailingDegree
  have hdiv : (X : Polynomial ℂ)^k ∣ u := X_pow_dvd_iff.mpr
    (fun d hd => coeff_eq_zero_of_lt_natTrailingDegree hd)
  obtain ⟨v,hv⟩ := hdiv
  refine ⟨k,v,?_,hv⟩
  have hc : u.coeff k ≠ 0 := coeff_natTrailingDegree_ne_zero.mpr hu
  rw [hv] at hc
  have he : ((X : Polynomial ℂ)^k*v).coeff k = v.coeff 0 := by
    simpa using coeff_X_pow_mul v k 0
  rw [he] at hc
  rwa [coeff_zero_eq_eval_zero] at hc

/-- An integer shift of the exponent absorbs a monomial in the exp variable. -/
theorem lift_origin_factor (a : ℂ) (k : ℕ) (v : Polynomial ℂ) :
    lift a (X^k*v) = lift (a+(k : ℂ)) v := by
  funext z
  simp only [lift, eval_mul, eval_pow, eval_X, add_mul, Complex.exp_add,
    Complex.exp_nat_mul]
  ring

/-- The same actual solution has a normalized polynomial ansatz whose exponent
is a root of the actual indicial polynomial. -/
theorem normalize_polynomial_lift_solution {n : ℕ}
    (P : Fin (n+1) → Polynomial ℂ) (a : ℂ) {u : Polynomial ℂ}
    (hu : u ≠ 0) (hsol : Solves P (lift a u)) :
    ∃ k : ℕ, ∃ v : Polynomial ℂ, v.eval 0 ≠ 0 ∧
      lift a u = lift (a+(k : ℂ)) v ∧
      transformedOperator P (a+(k : ℂ)) v = 0 ∧
      indicial P (a+(k : ℂ)) = 0 := by
  obtain ⟨k,v,hv0,huv⟩ := polynomial_origin_factor hu
  have he : lift a u = lift (a+(k : ℂ)) v := by rw [huv, lift_origin_factor]
  have hs : Solves P (lift (a+(k : ℂ)) v) := by rwa [← he]
  exact ⟨k,v,hv0,he,(transformed_eq_zero_iff P _ v).mpr hs,
    indicial_eq_zero_of_normalized_solution P _ v hv0 hs⟩

theorem lift_ne_zero_of_polynomial_ne_zero (a : ℂ) {u : Polynomial ℂ}
    (hu : u ≠ 0) : lift a u ≠ 0 := by
  intro h
  apply hu
  apply polynomial_eq_zero_of_exp_eval
  intro z
  have hz := congrFun h z
  change Complex.exp (a*z)*u.eval (Complex.exp z) = 0 at hz
  exact (mul_eq_zero.mp hz).resolve_left (Complex.exp_ne_zero _)

#print axioms polynomial_origin_factor
#print axioms lift_origin_factor
#print axioms normalize_polynomial_lift_solution
#print axioms lift_ne_zero_of_polynomial_ne_zero

end LiWangWen
