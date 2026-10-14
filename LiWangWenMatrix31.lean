import LiWangWenCore
import LiWangWenStirlingIdentity
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Exact matrices from Li--Wang--Wen (3.3). The superscript on lambda in
Q is a falling factorial, as stipulated in the paper, not an ordinary power.
Indices run from zero and M has the paper's row/column orientation. -/
set_option autoImplicit false
noncomputable section
open Polynomial
open scoped BigOperators
namespace LiWangWen

def paperM (n : ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
  fun i j => Nat.stirlingSecond j.val i.val

def paperQ (n : ℕ) (a : ℂ) : Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
  fun i j => (j.val.choose i.val : ℂ) * (descPochhammer ℂ (j.val-i.val)).eval a

theorem paperM_lower_zero {n : ℕ} (i j : Fin (n+1)) (h : j < i) :
    paperM n i j = 0 := by
  simp [paperM, Nat.stirlingSecond_eq_zero_of_lt h]

theorem paperQ_lower_zero {n : ℕ} (a : ℂ) (i j : Fin (n+1)) (h : j < i) :
    paperQ n a i j = 0 := by
  simp [paperQ, Nat.choose_eq_zero_of_lt h]

theorem descPochhammer_smeval_complex (x : ℂ) (k : ℕ) :
    (descPochhammer ℤ k).smeval x = (descPochhammer ℂ k).eval x := by
  rw [descPochhammer_smeval_eq_ascPochhammer,
    ascPochhammer_smeval_eq_eval, descPochhammer_eval_eq_ascPochhammer]

theorem falling_add (x y : ℂ) (k : ℕ) :
    (descPochhammer ℂ k).eval (x+y) =
      ∑ i ∈ Finset.range (k+1), (k.choose i : ℂ) *
        ((descPochhammer ℂ i).eval x * (descPochhammer ℂ (k-i)).eval y) := by
  simpa only [descPochhammer_smeval_complex,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] using
      Ring.descPochhammer_smeval_add k (Commute.all x y)

theorem falling_add_range (a : ℂ) (m k N : ℕ) (hk : k < N) :
    (descPochhammer ℂ k).eval (a+m) =
      ∑ i ∈ Finset.range N, (k.choose i : ℂ) *
        (descPochhammer ℂ (k-i)).eval a * (m.descFactorial i : ℂ) := by
  rw [add_comm, falling_add]
  calc
    _ = ∑ i ∈ Finset.range (k+1), (k.choose i : ℂ) *
        (descPochhammer ℂ (k-i)).eval a * (m.descFactorial i : ℂ) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [descPochhammer_eval_eq_descFactorial]
      ring
    _ = _ := by
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro i hi hni
      have hki : k < i := by simp only [Finset.mem_range] at *; omega
      simp [Nat.choose_eq_zero_of_lt hki]

theorem power_eq_stirling_range (x : ℂ) (j N : ℕ) (hj : j < N) :
    x^j = ∑ k ∈ Finset.range N, (Nat.stirlingSecond j k : ℂ) *
      (descPochhammer ℂ k).eval x := by
  rw [power_eq_stirling_descPochhammer]
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro k hk hnk
  have hjk : j < k := by simp only [Finset.mem_range] at *; omega
  simp [Nat.stirlingSecond_eq_zero_of_lt hjk]

def fallingEuler (i : ℕ) (u : Polynomial ℂ) : Polynomial ℂ :=
  X^i * Polynomial.derivative^[i] u

theorem fallingEuler_coeff (i m : ℕ) (u : Polynomial ℂ) :
    (fallingEuler i u).coeff m = (m.descFactorial i : ℂ) * u.coeff m := by
  unfold fallingEuler
  rw [coeff_X_pow_mul']
  split_ifs with h
  · rw [coeff_iterate_derivative, Nat.sub_add_cancel h, nsmul_eq_mul]
  · have hi : m < i := by omega
    simp [Nat.descFactorial_eq_zero_iff_lt.mpr hi]

theorem shiftedEuler_coeff (a : ℂ) (u : Polynomial ℂ) (m : ℕ) :
    (shiftedEuler a u).coeff m = (a+m)*u.coeff m := by
  cases m with
  | zero => simp [shiftedEuler]
  | succ m => simp [shiftedEuler, coeff_X_mul, coeff_derivative]; ring

theorem iterate_shiftedEuler_coeff (a : ℂ) (u : Polynomial ℂ) (j m : ℕ) :
    ((shiftedEuler a)^[j] u).coeff m = (a+m)^j * u.coeff m := by
  induction j with
  | zero => simp
  | succ j ih => rw [Function.iterate_succ_apply', shiftedEuler_coeff, ih, pow_succ']; ring

/-- Each column of Q M is exactly the shifted Euler iterate. -/
theorem shiftedEuler_eq_paperQM {n : ℕ} (a : ℂ) (u : Polynomial ℂ)
    (j : Fin (n+1)) :
    (shiftedEuler a)^[j.val] u =
      ∑ k : Fin (n+1), C (paperM n k j) *
        ∑ i : Fin (n+1), C (paperQ n a i k) * fallingEuler i.val u := by
  ext m
  rw [iterate_shiftedEuler_coeff]
  simp only [finsetSum_coeff, coeff_C_mul, fallingEuler_coeff]
  rw [power_eq_stirling_range (a+m) j.val (n+1) j.isLt, Finset.sum_mul]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  rw [falling_add_range a m k.val (n+1) k.isLt]
  simp only [paperM, paperQ]
  rw [mul_assoc, Finset.sum_mul, ← Fin.sum_univ_eq_sum_range]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The literal polynomial row-vector/matrix/column expression (3.3). -/
def paperMatrixOperator {n : ℕ} (P : Fin (n+1) → Polynomial ℂ)
    (a : ℂ) (u : Polynomial ℂ) : Polynomial ℂ :=
  dotProduct (Matrix.vecMul
    (Matrix.vecMul (fun i : Fin (n+1) => fallingEuler i.val u)
      ((paperQ n a).map C)) ((paperM n).map C)) P

theorem paperQM_column {n : ℕ} (a : ℂ) (u : Polynomial ℂ) (j : Fin (n+1)) :
    Matrix.vecMul
      (Matrix.vecMul (fun i : Fin (n+1) => fallingEuler i.val u)
        ((paperQ n a).map C)) ((paperM n).map C) j =
      (shiftedEuler a)^[j.val] u := by
  rw [shiftedEuler_eq_paperQM]
  simp only [Matrix.vecMul, dotProduct, Matrix.map_apply]
  apply Finset.sum_congr rfl
  intro k hk
  rw [mul_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  exact mul_comm _ _

/-- Exact identification with the basis-independent operator used by the ODE
formalization; no matrix identity or differential equation is assumed. -/
theorem paperMatrixOperator_eq_transformed {n : ℕ}
    (P : Fin (n+1) → Polynomial ℂ) (a : ℂ) (u : Polynomial ℂ) :
    paperMatrixOperator P a u = transformedOperator P a u := by
  unfold paperMatrixOperator dotProduct transformedOperator
  simp only [paperQM_column]
  apply Finset.sum_congr rfl
  intro j hj
  exact mul_comm _ _

/-- Equation (3.3) is equivalent to the actual ODE for e^(a z) u(e^z).
This holds for arbitrary polynomial coefficients, including the monic case
P_n = 1 of Theorem 3.1. -/
theorem paperMatrix_eq_zero_iff {n : ℕ}
    (P : Fin (n+1) → Polynomial ℂ) (a : ℂ) (u : Polynomial ℂ) :
    paperMatrixOperator P a u = 0 ↔ Solves P (lift a u) := by
  rw [paperMatrixOperator_eq_transformed, transformed_eq_zero_iff]

/-- The constant term of the paper's matrix equation is the ordinary-power
indicial polynomial times u(0). -/
theorem paperMatrix_eval_zero {n : ℕ}
    (P : Fin (n+1) → Polynomial ℂ) (a : ℂ) (u : Polynomial ℂ) :
    (paperMatrixOperator P a u).eval 0 = indicial P a * u.eval 0 := by
  rw [paperMatrixOperator_eq_transformed, transformed_eval_zero]

theorem iteratedDeriv_polynomial_eval (u : Polynomial ℂ) (i : ℕ) :
    iteratedDeriv i (fun t => u.eval t) =
      fun t => (Polynomial.derivative^[i] u).eval t := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [iteratedDeriv_succ, ih, Function.iterate_succ_apply']
    funext t
    exact Polynomial.deriv _

theorem fallingEuler_eval (u : Polynomial ℂ) (i : ℕ) (t : ℂ) :
    (fallingEuler i u).eval t = t^i * iteratedDeriv i (fun w => u.eval w) t := by
  simp [fallingEuler, iteratedDeriv_polynomial_eval]

/-- Evaluation yields the literal scalar differential expression printed
in (3.3), with analytic derivatives of the polynomial function. -/
theorem paperMatrixOperator_eval {n : ℕ}
    (P : Fin (n+1) → Polynomial ℂ) (a : ℂ) (u : Polynomial ℂ) (t : ℂ) :
    (paperMatrixOperator P a u).eval t =
      dotProduct (Matrix.vecMul
        (Matrix.vecMul (fun i : Fin (n+1) =>
          t^i.val * iteratedDeriv i.val (fun w => u.eval w) t)
          (paperQ n a)) (paperM n)) (fun j => (P j).eval t) := by
  simp only [paperMatrixOperator, Matrix.vecMul, dotProduct, Matrix.map_apply,
    eval_finsetSum, eval_mul, eval_C, fallingEuler_eval]

/-- The pointwise analytic reading of equation (3.3) is equivalent to the
original ODE under the fixed ansatz. No indicial-root claim is made for an
unnormalized polynomial u. -/
theorem paperMatrix_pointwise_iff {n : ℕ}
    (P : Fin (n+1) → Polynomial ℂ) (a : ℂ) (u : Polynomial ℂ) :
    (∀ t : ℂ, dotProduct (Matrix.vecMul
      (Matrix.vecMul (fun i : Fin (n+1) =>
        t^i.val * iteratedDeriv i.val (fun w => u.eval w) t)
        (paperQ n a)) (paperM n)) (fun j => (P j).eval t) = 0) ↔
      Solves P (lift a u) := by
  simp_rw [← paperMatrixOperator_eval]
  rw [← paperMatrix_eq_zero_iff]
  constructor
  · intro h
    exact Polynomial.funext (by simpa using h)
  · intro h t
    simp [h]

#print axioms iteratedDeriv_polynomial_eval
#print axioms fallingEuler_eval
#print axioms paperMatrixOperator_eval
#print axioms paperMatrix_pointwise_iff
#print axioms paperM_lower_zero
#print axioms paperQ_lower_zero
#print axioms falling_add
#print axioms shiftedEuler_eq_paperQM
#print axioms paperQM_column
#print axioms paperMatrixOperator_eq_transformed
#print axioms paperMatrix_eq_zero_iff
#print axioms paperMatrix_eval_zero
end LiWangWen
