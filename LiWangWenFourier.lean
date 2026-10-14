import LiWangWenPeriodicity
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Fourier.AddCircle

/-!
# Fourier coefficients of entire functions with period `2*pi*I`

The coefficient is defined by an actual vertical contour integral. Cauchy's
rectangle theorem makes its weighted integral independent of the real part.
-/

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory intervalIntegral
open scoped Topology

namespace LiWangWen

def fourierWeight (p : ℂ → ℂ) (m : ℤ) (z : ℂ) : ℂ :=
  Complex.exp (-(m : ℂ)*z) * p z

def verticalFourierCoeff (p : ℂ → ℂ) (m : ℤ) : ℂ :=
  ((2*Real.pi : ℝ) : ℂ)⁻¹ *
    ∫ y : ℝ in 0..2*Real.pi, fourierWeight p m ((y : ℂ)*Complex.I)

theorem fourierWeight_entire {p : ℂ → ℂ} (hp : Differentiable ℂ p) (m : ℤ) :
    Differentiable ℂ (fourierWeight p m) :=
  (Complex.differentiable_exp.comp ((differentiable_const _).mul differentiable_id)).mul hp

theorem fourierWeight_periodic {p : ℂ → ℂ}
    (hp : Function.Periodic p exponentialPeriod) (m : ℤ) :
    Function.Periodic (fourierWeight p m) exponentialPeriod := by
  intro z
  have he : Complex.exp (-(m : ℂ)*exponentialPeriod) = 1 := by
    rw [show -(m : ℂ) = ((-m : ℤ) : ℂ) by simp, Complex.exp_int_mul]
    simp [exponentialPeriod, Complex.exp_two_pi_mul_I]
  simp only [fourierWeight, mul_add, Complex.exp_add, he, mul_one, hp z]

/-- The vertical integral of an entire periodic function is independent of
the horizontal position, by cancellation of the two horizontal edges. -/
theorem vertical_integral_eq {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hp : Function.Periodic g exponentialPeriod) (x : ℝ) :
    (∫ y : ℝ in 0..2*Real.pi, g ((x : ℂ)+(y : ℂ)*Complex.I)) =
      ∫ y : ℝ in 0..2*Real.pi, g ((y : ℂ)*Complex.I) := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    g 0 ((x : ℂ)+(2*Real.pi : ℝ)*Complex.I) hg.differentiableOn
  have hp' (t : ℝ) : g ((t : ℂ)+(2*Real.pi : ℝ)*Complex.I) = g t := by
    simpa [exponentialPeriod] using hp (t : ℂ)
  simp only [zero_re, zero_im, ofReal_re, ofReal_im, add_re, add_im,
    mul_re, mul_im, I_re, I_im, ofReal_zero, mul_zero, zero_mul, mul_one,
    add_zero, zero_add, hp', sub_self, smul_eq_mul] at h
  apply (mul_left_cancel₀ Complex.I_ne_zero)
  exact sub_eq_zero.mp h

theorem verticalFourierCoeff_eq (p : ℂ → ℂ) (hp : Differentiable ℂ p)
    (hper : Function.Periodic p exponentialPeriod) (m : ℤ) (x : ℝ) :
    verticalFourierCoeff p m = ((2*Real.pi : ℝ) : ℂ)⁻¹ *
      ∫ y : ℝ in 0..2*Real.pi,
        fourierWeight p m ((x : ℂ)+(y : ℂ)*Complex.I) := by
  rw [vertical_integral_eq (fourierWeight_entire hp m) (fourierWeight_periodic hper m)]
  rfl

/-- Moving the vertical contour supplies the exact exponential decay factor. -/
theorem norm_verticalFourierCoeff_le {p : ℂ → ℂ} (hp : Differentiable ℂ p)
    (hper : Function.Periodic p exponentialPeriod) (m : ℤ) (x B : ℝ)
    (hbound : ∀ y ∈ Set.Icc (0 : ℝ) (2*Real.pi),
      ‖p ((x : ℂ)+(y : ℂ)*Complex.I)‖ ≤ B) :
    ‖verticalFourierCoeff p m‖ ≤ Real.exp (-(m : ℝ)*x) * B := by
  have hpi : 0 < 2*Real.pi := by positivity
  have he (y : ℝ) : ‖Complex.exp (-(m : ℂ)*((x : ℂ)+(y : ℂ)*Complex.I))‖ =
      Real.exp (-(m : ℝ)*x) := by
    rw [Complex.norm_exp]
    congr 1
    simp
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 2*Real.pi) (C := Real.exp (-(m : ℝ)*x)*B)
    (f := fun y : ℝ => fourierWeight p m ((x : ℂ)+(y : ℂ)*Complex.I)) (by
      intro y hy
      rw [Set.uIoc_of_le hpi.le] at hy
      have hy' : y ∈ Set.Icc (0 : ℝ) (2*Real.pi) := ⟨hy.1.le, hy.2⟩
      simpa only [fourierWeight, norm_mul, he] using
        mul_le_mul_of_nonneg_left (hbound y hy') (Real.exp_pos _).le)
  rw [verticalFourierCoeff_eq p hp hper m x, norm_mul, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpi]
  have hh := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hpi.le)
  refine hh.trans_eq ?_
  rw [sub_zero, abs_of_pos hpi]
  field_simp

#print axioms fourierWeight_entire
#print axioms fourierWeight_periodic
#print axioms vertical_integral_eq
#print axioms verticalFourierCoeff_eq
#print axioms norm_verticalFourierCoeff_le
end LiWangWen
