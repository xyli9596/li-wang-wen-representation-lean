import WimanValironHigherDerivatives

/-!
# Quantitative conversion of centered moments to derivative errors

Uniform coefficient bounds for the centered falling-factorial polynomial
give explicit constants depending only on the fixed derivative order. The
resulting estimate controls the actual derivative ratio by the positive
centered moments and the reciprocal central index.

This module proves the finite algebraic estimate. It does not assume the
desired derivative error bound, and it does not construct the exceptional
radii or the moment estimates needed to apply it.
-/

set_option autoImplicit false
noncomputable section
open Polynomial

namespace WimanValiron

/-- A uniform bound for every coefficient on the closed unit disk in `t`. -/
def fallingCoefficientBound : ℕ → ℝ
  | 0 => 1
  | j + 1 => ((j : ℝ) + 2) * fallingCoefficientBound j

/-- A Lipschitz constant at zero for the constant coefficient. -/
def fallingConstantErrorBound : ℕ → ℝ
  | 0 => 0
  | j + 1 => (1 + (j : ℝ)) * fallingConstantErrorBound j + j

/-- The quantitative derivative constant depends only on the derivative order. -/
def derivativeMomentConstant (j : ℕ) : ℝ :=
  (j : ℝ) * fallingCoefficientBound j + fallingConstantErrorBound j

theorem fallingCoefficientBound_pos (j : ℕ) : 0 < fallingCoefficientBound j := by
  induction j with
  | zero => norm_num [fallingCoefficientBound]
  | succ j ih => simp only [fallingCoefficientBound]; positivity

theorem fallingConstantErrorBound_nonneg (j : ℕ) : 0 ≤ fallingConstantErrorBound j := by
  induction j with
  | zero => simp [fallingConstantErrorBound]
  | succ j ih => simp only [fallingConstantErrorBound]; positivity

theorem derivativeMomentConstant_nonneg (j : ℕ) : 0 ≤ derivativeMomentConstant j := by
  unfold derivativeMomentConstant
  exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) (fallingCoefficientBound_pos j).le)
    (fallingConstantErrorBound_nonneg j)

theorem norm_one_sub_nat_mul_le {t : ℂ} (ht : ‖t‖ ≤ 1) (j : ℕ) :
    ‖1 - (j : ℂ) * t‖ ≤ 1 + (j : ℝ) := by
  calc
    ‖1 - (j : ℂ) * t‖ ≤ ‖(1 : ℂ)‖ + ‖(j : ℂ) * t‖ := norm_sub_le _ _
    _ = 1 + (j : ℝ) * ‖t‖ := by simp
    _ ≤ 1 + (j : ℝ) := by nlinarith [Nat.cast_nonneg (α := ℝ) j]

theorem centeredFallingPolynomial_coeff_bound {t : ℂ} (ht : ‖t‖ ≤ 1) (j k : ℕ) :
    ‖(centeredFallingPolynomial t j).coeff k‖ ≤ fallingCoefficientBound j := by
  induction j generalizing k with
  | zero => cases k <;> simp [centeredFallingPolynomial, fallingCoefficientBound, coeff_one]
  | succ j ih =>
    have hB : 0 ≤ fallingCoefficientBound j := (fallingCoefficientBound_pos j).le
    cases k with
    | zero =>
      simp only [centeredFallingPolynomial, coeff_add, coeff_X_mul_zero, coeff_C_mul, zero_add,
        norm_mul, fallingCoefficientBound]
      calc
        _ ≤ (1 + (j : ℝ)) * fallingCoefficientBound j :=
          mul_le_mul (norm_one_sub_nat_mul_le ht j) (ih 0) (norm_nonneg _) (by positivity)
        _ ≤ ((j : ℝ) + 2) * fallingCoefficientBound j := by nlinarith
    | succ k =>
      simp only [centeredFallingPolynomial, coeff_add, coeff_X_mul, coeff_C_mul,
        fallingCoefficientBound]
      calc
        _ ≤ ‖(centeredFallingPolynomial t j).coeff k‖ +
            ‖(1 - (j : ℂ) * t) * (centeredFallingPolynomial t j).coeff (k+1)‖ :=
          norm_add_le _ _
        _ ≤ fallingCoefficientBound j + (1 + (j : ℝ)) * fallingCoefficientBound j := by
          apply add_le_add (ih k)
          rw [norm_mul]
          exact mul_le_mul (norm_one_sub_nat_mul_le ht j) (ih (k+1)) (norm_nonneg _)
            (by positivity)
        _ = ((j : ℝ) + 2) * fallingCoefficientBound j := by ring

theorem centeredFallingPolynomial_constant_error {t : ℂ} (ht : ‖t‖ ≤ 1) (j : ℕ) :
    ‖(centeredFallingPolynomial t j).coeff 0 - 1‖ ≤ fallingConstantErrorBound j * ‖t‖ := by
  induction j with
  | zero => simp [centeredFallingPolynomial, fallingConstantErrorBound]
  | succ j ih =>
    simp only [centeredFallingPolynomial, coeff_add, coeff_X_mul_zero, coeff_C_mul, zero_add,
      fallingConstantErrorBound]
    have heq : (1 - (j : ℂ) * t) * (centeredFallingPolynomial t j).coeff 0 - 1 =
        (1 - (j : ℂ) * t) * ((centeredFallingPolynomial t j).coeff 0 - 1) - (j : ℂ) * t := by ring
    rw [heq]
    calc
      _ ≤ ‖(1 - (j : ℂ) * t) * ((centeredFallingPolynomial t j).coeff 0 - 1)‖ +
          ‖(j : ℂ) * t‖ := norm_sub_le _ _
      _ = ‖1 - (j : ℂ) * t‖ * ‖(centeredFallingPolynomial t j).coeff 0 - 1‖ +
          (j : ℝ) * ‖t‖ := by simp
      _ ≤ (1 + (j : ℝ)) * (fallingConstantErrorBound j * ‖t‖) + (j : ℝ) * ‖t‖ := by
        exact add_le_add (mul_le_mul (norm_one_sub_nat_mul_le ht j) ih (norm_nonneg _)
          (by positivity)) le_rfl
      _ = ((1 + (j : ℝ)) * fallingConstantErrorBound j + j) * ‖t‖ := by ring

/-- A finite polynomial expectation estimate; the constant coefficient contributes
the reciprocal-index error and all remaining coefficients multiply centered moments. -/
theorem centered_polynomial_average_error {t : ℂ} (ht : ‖t‖ ≤ 1)
    {m : ℕ → ℂ} (hm0 : m 0 = 1) {A : ℝ} (hA : 0 ≤ A)
    (j : ℕ) (hm : ∀ k, 1 ≤ k → k ≤ j → ‖m k‖ ≤ A) :
    ‖(∑ k ∈ Finset.range (j+1), (centeredFallingPolynomial t j).coeff k * m k) - 1‖ ≤
      derivativeMomentConstant j * (A + ‖t‖) := by
  have heq : (∑ k ∈ Finset.range (j+1), (centeredFallingPolynomial t j).coeff k * m k) - 1 =
      ((centeredFallingPolynomial t j).coeff 0 - 1) +
        ∑ k ∈ Finset.range j, (centeredFallingPolynomial t j).coeff (k+1) * m (k+1) := by
    rw [Finset.sum_range_succ', hm0, mul_one]
    ring
  rw [heq]
  have hsum : ‖∑ k ∈ Finset.range j,
      (centeredFallingPolynomial t j).coeff (k+1) * m (k+1)‖ ≤
      (j : ℝ) * fallingCoefficientBound j * A := by
    calc
      _ ≤ ∑ k ∈ Finset.range j,
          ‖(centeredFallingPolynomial t j).coeff (k+1) * m (k+1)‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ Finset.range j, fallingCoefficientBound j * A := by
        apply Finset.sum_le_sum
        intro k hk
        rw [norm_mul]
        exact mul_le_mul (centeredFallingPolynomial_coeff_bound ht j (k+1))
          (hm (k+1) (by omega) (Nat.succ_le_of_lt (Finset.mem_range.mp hk)))
          (norm_nonneg _) (fallingCoefficientBound_pos j).le
      _ = (j : ℝ) * fallingCoefficientBound j * A := by simp; ring
  calc
    _ ≤ ‖(centeredFallingPolynomial t j).coeff 0 - 1‖ +
        ‖∑ k ∈ Finset.range j, (centeredFallingPolynomial t j).coeff (k+1) * m (k+1)‖ :=
      norm_add_le _ _
    _ ≤ fallingConstantErrorBound j * ‖t‖ + (j : ℝ) * fallingCoefficientBound j * A :=
      add_le_add (centeredFallingPolynomial_constant_error ht j) hsum
    _ ≤ derivativeMomentConstant j * (A + ‖t‖) := by
      unfold derivativeMomentConstant
      have hB := (fallingCoefficientBound_pos j).le
      have hL := fallingConstantErrorBound_nonneg j
      have h1 : 0 ≤ (j : ℝ) * fallingCoefficientBound j * ‖t‖ := by positivity
      have h2 : 0 ≤ fallingConstantErrorBound j * A := mul_nonneg hL hA
      nlinarith

/-- Quantitative conversion for the actual Taylor weights of an entire function. -/
theorem normalized_deriv_error_le_centered_moments {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {z v : ℂ} (hz : f z ≠ 0) (hv : v ≠ 0)
    (hsmall : ‖v⁻¹‖ ≤ 1) {A : ℝ} (hA : 0 ≤ A) (j : ℕ)
    (hm : ∀ k, 1 ≤ k → k ≤ j → ‖centeredMoment (taylorWeight f z) v k‖ ≤ A) :
    ‖z ^ j * iteratedDeriv j f z / (v ^ j * f z) - 1‖ ≤
      derivativeMomentConstant j * (A + ‖v⁻¹‖) := by
  have hne : f ≠ 0 := by intro h; exact hz (by simp [h])
  have heq := falling_average_eq_centered_moments hv j
    (fun k _ => summable_centered_taylorWeight hf hne z v k)
  rw [falling_taylorWeight_eq_normalized_deriv hf] at heq
  rw [heq]
  exact centered_polynomial_average_error hsmall (centered_taylorWeight_zero hf hz v) hA j hm

/-- Natural-index form, with an explicit `A + 1/N` error bound. -/
theorem normalized_deriv_error_le_nat_centered_moments {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {z : ℂ} (hz : f z ≠ 0) {N : ℕ} (hN : 1 ≤ N)
    {A : ℝ} (hA : 0 ≤ A) (j : ℕ)
    (hm : ∀ k, 1 ≤ k → k ≤ j → ‖centeredMoment (taylorWeight f z) (N : ℂ) k‖ ≤ A) :
    ‖z ^ j * iteratedDeriv j f z / ((N : ℂ) ^ j * f z) - 1‖ ≤
      derivativeMomentConstant j * (A + 1 / (N : ℝ)) := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hv : (N : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hN)
  have hnorm : ‖(N : ℂ)⁻¹‖ = 1 / (N : ℝ) := by simp [one_div]
  have hi : ‖(N : ℂ)⁻¹‖ ≤ 1 := by
    rw [hnorm]
    exact (div_le_one (zero_lt_one.trans_le hn)).mpr hn
  simpa only [hnorm] using normalized_deriv_error_le_centered_moments hf hz hv hi hA j hm

#print axioms fallingCoefficientBound_pos
#print axioms fallingConstantErrorBound_nonneg
#print axioms derivativeMomentConstant_nonneg
#print axioms norm_one_sub_nat_mul_le
#print axioms centeredFallingPolynomial_coeff_bound
#print axioms centeredFallingPolynomial_constant_error
#print axioms centered_polynomial_average_error
#print axioms normalized_deriv_error_le_centered_moments
#print axioms normalized_deriv_error_le_nat_centered_moments

end WimanValiron
