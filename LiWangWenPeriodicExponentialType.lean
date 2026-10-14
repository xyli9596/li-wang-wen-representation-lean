import LiWangWenFourierReconstruction
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Entire periodic functions of finite exponential type

Moving the vertical Fourier contour in the sign of the integer index
annihilates every coefficient outside a bounded interval. This proof uses
only the actual exponential bound, not an ODE recurrence.
-/

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Topology

namespace LiWangWen

/-- The elementary Fourier consequence of Gross's periodic exponential-type
result, with the actual Fourier coefficients and both tails. -/
theorem verticalFourierCoeff_eq_zero_of_exponential_bound
    {p : ℂ → ℂ} (hp : Differentiable ℂ p)
    (hper : Function.Periodic p exponentialPeriod)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbound : ∀ z, ‖p z‖ ≤ A * Real.exp (B * ‖z‖))
    {m : ℤ} (hm : B < |(m : ℝ)|) : verticalFourierCoeff p m = 0 := by
  let C : ℝ := A * Real.exp (B * (2 * Real.pi))
  let d : ℝ := |(m : ℝ)| - B
  have hd : 0 < d := sub_pos.mpr hm
  have hcoeff (t : ℝ) (ht : 0 ≤ t) :
      ‖verticalFourierCoeff p m‖ ≤ C * Real.exp (-d * t) := by
    let x : ℝ := if 0 ≤ (m : ℝ) then t else -t
    have hx : |x| = t := by
      dsimp only [x]
      split_ifs <;> simp [abs_of_nonneg ht]
    have hmx : (m : ℝ) * x = |(m : ℝ)| * t := by
      dsimp only [x]
      split_ifs with h
      · rw [abs_of_nonneg h]
      · rw [abs_of_neg (lt_of_not_ge h)]; ring
    have hpoint (y : ℝ) (hy : y ∈ Icc (0 : ℝ) (2 * Real.pi)) :
        ‖p ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤
          A * Real.exp (B * (t + 2 * Real.pi)) := by
      apply (hbound _).trans
      apply mul_le_mul_of_nonneg_left _ hA
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left _ hB
      calc
        ‖(x : ℂ) + (y : ℂ) * Complex.I‖ ≤
            ‖(x : ℂ)‖ + ‖(y : ℂ) * Complex.I‖ := norm_add_le _ _
        _ = |x| + |y| := by simp
        _ ≤ t + 2 * Real.pi := by rw [hx, abs_of_nonneg hy.1]; linarith [hy.2]
    have hc := norm_verticalFourierCoeff_le hp hper m x
      (A * Real.exp (B * (t + 2 * Real.pi))) hpoint
    apply hc.trans_eq
    dsimp only [C, d]
    rw [show -(m : ℝ) * x = -|(m : ℝ)| * t by linarith [hmx]]
    rw [show B * (t + 2 * Real.pi) = B * t + B * (2 * Real.pi) by ring,
      Real.exp_add]
    rw [show -(|(m : ℝ)| - B) * t = -|(m : ℝ)| * t + B * t by ring,
      Real.exp_add]
    ring
  have hdtop : Tendsto (fun t : ℝ => d * t) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hd).mpr tendsto_id
  have hlim : Tendsto (fun t : ℝ => C * Real.exp (-d * t)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_mul, mul_zero] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp hdtop).const_mul C
  have hzero : ‖verticalFourierCoeff p m‖ ≤ 0 :=
    ge_of_tendsto hlim ((eventually_ge_atTop (0 : ℝ)).mono hcoeff)
  exact norm_eq_zero.mp (le_antisymm hzero (norm_nonneg _))

/-- Every entire periodic function of finite exponential type has finite
actual Fourier support. -/
theorem periodic_exponentialBound_finiteFourier_support
    {p : ℂ → ℂ} (hp : Differentiable ℂ p)
    (hper : Function.Periodic p exponentialPeriod) (hb : ExponentialBound p) :
    (Function.support (verticalFourierCoeff p)).Finite := by
  obtain ⟨A,B,hA,hB,hbound⟩ := hb
  obtain ⟨N,hN⟩ := exists_nat_gt B
  apply (Set.finite_Icc (-(N : ℤ)) (N : ℤ)).subset
  intro m hm
  have hlt : |(m : ℝ)| < (N : ℝ) := by
    by_contra hn
    have hz := verticalFourierCoeff_eq_zero_of_exponential_bound hp hper hA hB hbound
      (hN.trans_le (le_of_not_gt hn))
    exact hm hz
  have hint : |m| < (N : ℤ) := by exact_mod_cast hlt
  exact ⟨(abs_lt.mp hint).1.le, (abs_lt.mp hint).2.le⟩

/-- Reconstruction gives the finite exponential Laurent sum itself. -/
theorem periodic_exponentialBound_isExponentialSum
    {p : ℂ → ℂ} (hp : Differentiable ℂ p)
    (hper : Function.Periodic p exponentialPeriod) (hb : ExponentialBound p) :
    IsExponentialSum p :=
  finite_fourier_support_isExponentialSum p hp hper
    (periodic_exponentialBound_finiteFourier_support hp hper hb)

#print axioms verticalFourierCoeff_eq_zero_of_exponential_bound
#print axioms periodic_exponentialBound_finiteFourier_support
#print axioms periodic_exponentialBound_isExponentialSum

end LiWangWen
