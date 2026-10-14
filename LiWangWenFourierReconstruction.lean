import LiWangWenFourier
import LiWangWenGrowth

/-!
# Reconstruction from finitely many vertical Fourier coefficients

The Fourier uniqueness theorem on the circle is applied on every vertical
line. Contour translation identifies its coefficients with those on the
imaginary axis, so no unproved Laurent representation is assumed.
-/

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory intervalIntegral
open scoped Topology

namespace LiWangWen

local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩

theorem vertical_slice_periodic {p : ℂ → ℂ}
    (hper : Function.Periodic p exponentialPeriod) (x : ℝ) :
    Function.Periodic (fun y : ℝ => p ((x : ℂ)+(y : ℂ)*Complex.I)) (2*Real.pi) := by
  intro y
  simpa [exponentialPeriod, add_mul, add_assoc] using
    hper ((x : ℂ)+(y : ℂ)*Complex.I)

/-- The restriction to a vertical line, as a continuous function on a circle. -/
def verticalCircle (p : ℂ → ℂ) (hp : Differentiable ℂ p)
    (hper : Function.Periodic p exponentialPeriod) (x : ℝ) :
    C(AddCircle (2*Real.pi), ℂ) :=
  ⟨(vertical_slice_periodic hper x).lift,
    continuous_coinduced_dom.mpr (hp.continuous.comp
      (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)))⟩

theorem verticalCircle_coe (p : ℂ → ℂ) (hp : Differentiable ℂ p)
    (hper : Function.Periodic p exponentialPeriod) (x y : ℝ) :
    verticalCircle p hp hper x (y : AddCircle (2*Real.pi)) =
      p ((x : ℂ)+(y : ℂ)*Complex.I) := rfl

theorem fourier_two_pi (m : ℤ) (y : ℝ) :
    @fourier (2*Real.pi) m (y : AddCircle (2*Real.pi)) =
      Complex.exp ((m : ℂ)*(y : ℂ)*Complex.I) := by
  rw [fourier_coe_apply]
  congr 1
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp

theorem verticalCircle_fourierCoeff (p : ℂ → ℂ) (hp : Differentiable ℂ p)
    (hper : Function.Periodic p exponentialPeriod) (x : ℝ) (m : ℤ) :
    fourierCoeff (verticalCircle p hp hper x) m =
      Complex.exp ((m : ℂ)*(x : ℂ)) * verticalFourierCoeff p m := by
  rw [fourierCoeff_eq_intervalIntegral _ _ 0, verticalFourierCoeff_eq p hp hper m x]
  simp only [zero_add, one_div, Complex.real_smul, Complex.ofReal_inv,
    smul_eq_mul, fourier_two_pi, verticalCircle_coe]
  rw [← mul_assoc, mul_comm (Complex.exp _), mul_assoc]
  congr 1
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro y _
  dsimp only
  rw [fourierWeight, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- A finite support hypothesis on the actual contour-integral coefficients
gives the entire function's finite exponential Laurent expansion. -/
theorem finite_fourier_reconstruction (p : ℂ → ℂ) (hp : Differentiable ℂ p)
    (hper : Function.Periodic p exponentialPeriod) (s : Finset ℤ)
    (hs : ∀ m ∉ s, verticalFourierCoeff p m = 0) (z : ℂ) :
    p z = ∑ m ∈ s, verticalFourierCoeff p m * Complex.exp ((m : ℂ)*z) := by
  let F : C(AddCircle (2*Real.pi), ℂ) := verticalCircle p hp hper z.re
  have hcoeff (m : ℤ) : fourierCoeff F m =
      Complex.exp ((m : ℂ)*(z.re : ℂ)) * verticalFourierCoeff p m :=
    verticalCircle_fourierCoeff p hp hper z.re m
  have hzero : ∀ m ∉ s, fourierCoeff F m = 0 := by
    intro m hm
    rw [hcoeff, hs m hm, mul_zero]
  have hsum : Summable (fourierCoeff F) := summable_of_ne_finset_zero hzero
  have hfull := has_pointwise_sum_fourier_series_of_summable hsum
    (z.im : AddCircle (2*Real.pi))
  have hfinite : HasSum
      (fun m : ℤ => fourierCoeff F m • fourier m (z.im : AddCircle (2*Real.pi)))
      (∑ m ∈ s, fourierCoeff F m • fourier m (z.im : AddCircle (2*Real.pi))) :=
    hasSum_sum_of_ne_finset_zero (fun m hm => by rw [hzero m hm, zero_smul])
  have heq := hfull.unique hfinite
  have hF : F (z.im : AddCircle (2*Real.pi)) = p z := by
    change p ((z.re : ℂ)+(z.im : ℂ)*Complex.I) = p z
    rw [Complex.re_add_im]
  rw [hF] at heq
  rw [heq]
  apply Finset.sum_congr rfl
  intro m _
  rw [hcoeff, smul_eq_mul, fourier_two_pi]
  calc
    Complex.exp ((m : ℂ)*(z.re : ℂ)) * verticalFourierCoeff p m *
        Complex.exp ((m : ℂ)*(z.im : ℂ)*Complex.I) =
        verticalFourierCoeff p m * Complex.exp
          ((m : ℂ)*(z.re : ℂ)+(m : ℂ)*(z.im : ℂ)*Complex.I) := by
      rw [Complex.exp_add]
      ring
    _ = _ := by
      congr 2
      conv_rhs => rw [← Complex.re_add_im z]
      ring

theorem finite_fourier_support_representation (p : ℂ → ℂ) (hp : Differentiable ℂ p)
    (hper : Function.Periodic p exponentialPeriod)
    (hs : (Function.support (verticalFourierCoeff p)).Finite) :
    ∃ s : Finset ℤ, ∀ z : ℂ,
      p z = ∑ m ∈ s, verticalFourierCoeff p m * Complex.exp ((m : ℂ)*z) := by
  refine ⟨hs.toFinset, fun z => finite_fourier_reconstruction p hp hper hs.toFinset ?_ z⟩
  intro m hm
  exact not_not.mp (fun hne => hm (hs.mem_toFinset.mpr hne))

/-- The reconstructed Laurent sum is an exponential sum in the terminology
used in the statement of Theorem 1.1. -/
theorem finite_fourier_support_isExponentialSum (p : ℂ → ℂ) (hp : Differentiable ℂ p)
    (hper : Function.Periodic p exponentialPeriod)
    (hs : (Function.support (verticalFourierCoeff p)).Finite) : IsExponentialSum p := by
  classical
  obtain ⟨s,hsum⟩ := finite_fourier_support_representation p hp hper hs
  let e : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
  refine ⟨Fintype.card s, (fun j => Polynomial.C (verticalFourierCoeff p (e j))),
    (fun j => ((e j : ℤ) : ℂ)), ?_⟩
  intro z
  rw [hsum]
  simp only [Polynomial.eval_C]
  calc
    (∑ m ∈ s, verticalFourierCoeff p m * Complex.exp ((m : ℂ)*z)) =
        ∑ m : s, verticalFourierCoeff p m * Complex.exp ((m : ℂ)*z) :=
      (Finset.sum_coe_sort s (fun m : ℤ => verticalFourierCoeff p m *
        Complex.exp ((m : ℂ)*z))).symm
    _ = _ :=
      (e.sum_comp (fun m : s => verticalFourierCoeff p m * Complex.exp ((m : ℂ)*z))).symm

end LiWangWen

#print axioms LiWangWen.vertical_slice_periodic
#print axioms LiWangWen.verticalCircle_coe
#print axioms LiWangWen.fourier_two_pi
#print axioms LiWangWen.verticalCircle_fourierCoeff
#print axioms LiWangWen.finite_fourier_reconstruction
#print axioms LiWangWen.finite_fourier_support_representation
#print axioms LiWangWen.finite_fourier_support_isExponentialSum
