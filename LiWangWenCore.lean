import CRGOrder
import CRGExponentialCoefficients
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! Exact exponential substitution for Li--Wang--Wen, JDE 423 (2025).
The shifted Euler operator gives a basis-independent form of the polynomial
equation underlying (3.3). Its identification with the displayed Stirling and
falling-factorial matrices is a separate task. -/
set_option autoImplicit false
noncomputable section
open Polynomial
open scoped BigOperators

namespace LiWangWen

def lift (a : ℂ) (u : Polynomial ℂ) (z : ℂ) : ℂ :=
  Complex.exp (a * z) * u.eval (Complex.exp z)

def shiftedEuler (a : ℂ) (u : Polynomial ℂ) : Polynomial ℂ :=
  X * u.derivative + C a * u

def transformedOperator {n : ℕ} (P : Fin (n+1) → Polynomial ℂ)
    (a : ℂ) (u : Polynomial ℂ) : Polynomial ℂ :=
  ∑ j, P j * ((shiftedEuler a)^[j.val] u)

def Solves {n : ℕ} (P : Fin (n+1) → Polynomial ℂ) (f : ℂ → ℂ) : Prop :=
  ∀ z, ∑ j, (P j).eval (Complex.exp z) * iteratedDeriv j.val f z = 0

def indicial {n : ℕ} (P : Fin (n+1) → Polynomial ℂ) (a : ℂ) : ℂ :=
  ∑ j, (P j).eval 0 * a ^ j.val

theorem lift_hasDerivAt (a : ℂ) (u : Polynomial ℂ) (z : ℂ) :
    HasDerivAt (lift a u) (lift a (shiftedEuler a u) z) z := by
  have he := (Complex.hasDerivAt_exp (a*z)).comp z
    ((hasDerivAt_id z).const_mul a)
  have hu := (u.hasDerivAt (Complex.exp z)).comp z (Complex.hasDerivAt_exp z)
  have hd : HasDerivAt (lift a u)
      ((Complex.exp (a*z) * (a*1)) * u.eval (Complex.exp z) +
        Complex.exp (a*z) * (u.derivative.eval (Complex.exp z) * Complex.exp z)) z :=
    he.mul hu
  have hh : (Complex.exp (a*z) * (a*1)) * u.eval (Complex.exp z) +
        Complex.exp (a*z) * (u.derivative.eval (Complex.exp z) * Complex.exp z) =
      lift a (shiftedEuler a u) z := by
    simp only [lift, shiftedEuler, eval_add, eval_mul, eval_X, eval_C]
    ring
  rwa [hh] at hd

theorem lift_entire (a : ℂ) (u : Polynomial ℂ) : Differentiable ℂ (lift a u) :=
  fun z => (lift_hasDerivAt a u z).differentiableAt

theorem deriv_lift (a : ℂ) (u : Polynomial ℂ) :
    deriv (lift a u) = lift a (shiftedEuler a u) := by
  funext z
  exact (lift_hasDerivAt a u z).deriv

theorem iteratedDeriv_lift (j : ℕ) (a : ℂ) (u : Polynomial ℂ) :
    iteratedDeriv j (lift a u) = lift a ((shiftedEuler a)^[j] u) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ, ih, deriv_lift, Function.iterate_succ_apply']

theorem residual_lift {n : ℕ} (P : Fin (n+1) → Polynomial ℂ)
    (a : ℂ) (u : Polynomial ℂ) (z : ℂ) :
    (∑ j, (P j).eval (Complex.exp z) * iteratedDeriv j.val (lift a u) z) =
      Complex.exp (a*z) * (transformedOperator P a u).eval (Complex.exp z) := by
  simp only [transformedOperator, eval_finsetSum, eval_mul, Finset.mul_sum,
    iteratedDeriv_lift, lift]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem polynomial_eq_zero_of_exp_eval (p : Polynomial ℂ)
    (h : ∀ z, p.eval (Complex.exp z) = 0) : p = 0 := by
  apply p.eq_zero_of_infinite_isRoot
  apply (Set.infinite_univ.sdiff (Set.finite_singleton (0 : ℂ))).mono
  intro t ht
  have hn : t ≠ 0 := by simpa using ht.2
  change p.eval t = 0
  simpa only [Complex.exp_log hn] using h (Complex.log t)

/-- The polynomial equation is equivalent to the actual entire ODE under
the exact ansatz. No growth or asymptotic hypothesis is used. -/
theorem transformed_eq_zero_iff {n : ℕ} (P : Fin (n+1) → Polynomial ℂ)
    (a : ℂ) (u : Polynomial ℂ) :
    transformedOperator P a u = 0 ↔ Solves P (lift a u) := by
  constructor
  · intro h z
    rw [residual_lift, h, eval_zero, mul_zero]
  · intro h
    apply polynomial_eq_zero_of_exp_eval
    intro z
    have hz := h z
    rw [residual_lift] at hz
    exact (mul_eq_zero.mp hz).resolve_left (Complex.exp_ne_zero _)

theorem shiftedEuler_eval_zero (a : ℂ) (u : Polynomial ℂ) :
    (shiftedEuler a u).eval 0 = a * u.eval 0 := by
  simp [shiftedEuler]

theorem iterate_shiftedEuler_eval_zero (j : ℕ) (a : ℂ) (u : Polynomial ℂ) :
    ((shiftedEuler a)^[j] u).eval 0 = a^j * u.eval 0 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', shiftedEuler_eval_zero, ih, pow_succ]
    ring

theorem transformed_eval_zero {n : ℕ} (P : Fin (n+1) → Polynomial ℂ)
    (a : ℂ) (u : Polynomial ℂ) :
    (transformedOperator P a u).eval 0 = indicial P a * u.eval 0 := by
  simp only [transformedOperator, indicial, eval_finsetSum, eval_mul,
    iterate_shiftedEuler_eval_zero, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The indicial-root condition follows once the ansatz is normalized by
u(0) != 0. This condition makes the quantification of the exponent explicit. -/
theorem indicial_eq_zero_of_normalized_solution {n : ℕ}
    (P : Fin (n+1) → Polynomial ℂ) (a : ℂ) (u : Polynomial ℂ)
    (hu : u.eval 0 ≠ 0) (hf : Solves P (lift a u)) : indicial P a = 0 := by
  have ht := (transformed_eq_zero_iff P a u).mpr hf
  have he := congrArg (fun p : Polynomial ℂ => p.eval 0) ht
  rw [transformed_eval_zero, eval_zero] at he
  exact (mul_eq_zero.mp he).resolve_right hu

theorem shiftedEuler_C (a c : ℂ) : shiftedEuler a (C c) = C (a*c) := by
  simp [shiftedEuler]

theorem iterate_shiftedEuler_C (j : ℕ) (a c : ℂ) :
    (shiftedEuler a)^[j] (C c) = C (a^j*c) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, shiftedEuler_C, pow_succ]
    congr 1
    ring

/-- Algebraic part of Corollary 3.4, for every order n and scalar amplitude. -/
theorem pure_exponential_solves {n : ℕ} (P : Fin (n+1) → Polynomial ℂ)
    (a c : ℂ) (h : ∑ j, P j * C (a^j.val) = 0) :
    Solves P (fun z => c * Complex.exp (a*z)) := by
  have ht : transformedOperator P a (C c) = 0 := by
    simp only [transformedOperator, iterate_shiftedEuler_C, C_mul]
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul, h, zero_mul]
  have hh : (fun z => c * Complex.exp (a*z)) = lift a (C c) := by
    funext z
    simp [lift, mul_comm]
  rw [hh]
  exact (transformed_eq_zero_iff P a (C c)).mp ht


#print axioms lift_hasDerivAt
#print axioms lift_entire
#print axioms deriv_lift
#print axioms iteratedDeriv_lift
#print axioms residual_lift
#print axioms polynomial_eq_zero_of_exp_eval
#print axioms transformed_eq_zero_iff
#print axioms shiftedEuler_eval_zero
#print axioms iterate_shiftedEuler_eval_zero
#print axioms transformed_eval_zero
#print axioms indicial_eq_zero_of_normalized_solution
#print axioms shiftedEuler_C
#print axioms iterate_shiftedEuler_C
#print axioms pure_exponential_solves
end LiWangWen
