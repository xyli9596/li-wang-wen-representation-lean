import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic

/-!
# Angular Taylor estimates and second moments

The exponential on the imaginary axis has a global quadratic Taylor error
with constant one half. Summing this genuine analytic estimate controls an
angular exponential sum by its weighted second moment. The first-moment
estimate follows by balancing the rotation size against the quadratic error.

These statements supply the angular Taylor step in the central-index method.
They do not prove the exceptional-radius bounds on the weighted moments.
-/

set_option autoImplicit false
noncomputable section
open Filter MeasureTheory Set
open scoped Topology

namespace WimanValiron

/-- A global Taylor estimate on the imaginary axis; no small-angle assumption
is needed because the exponential has modulus one there. -/
theorem norm_exp_I_mul_sub_one_sub_le (x : ℝ) :
    ‖Complex.exp (Complex.I * (x : ℂ)) - 1 - Complex.I * (x : ℂ)‖ ≤ x ^ 2 / 2 := by
  let g : ℝ → ℂ := fun t =>
    Complex.exp (Complex.I * (x : ℂ) * (t : ℂ)) - 1 -
      Complex.I * (x : ℂ) * (t : ℂ)
  have hd (t : ℝ) : HasDerivAt g
      (Complex.I * (x : ℂ) * (Complex.exp (Complex.I * (x : ℂ) * (t : ℂ)) - 1)) t := by
    have hi : HasDerivAt (fun s : ℝ => Complex.I * (x : ℂ) * (s : ℂ))
        (Complex.I * (x : ℂ)) t := by
      simpa using Complex.ofRealCLM.hasDerivAt.const_mul (Complex.I * (x : ℂ))
    have h0 : HasDerivAt g
        (Complex.exp (Complex.I * (x : ℂ) * (t : ℂ)) * (Complex.I * (x : ℂ)) -
          Complex.I * (x : ℂ)) t := (hi.cexp.sub_const 1).sub hi
    convert h0 using 1
    ring
  have hbound : ∀ᵐ t : ℝ, t ∈ Ioo (0 : ℝ) 1 → ‖deriv g t‖ ≤ x ^ 2 * t := by
    apply Eventually.of_forall
    intro t ht
    rw [(hd t).deriv, norm_mul]
    have he : ‖Complex.exp (Complex.I * (x : ℂ) * (t : ℂ)) - 1‖ ≤ |x * t| := by
      simpa [Complex.ofReal_mul, mul_assoc, Real.norm_eq_abs] using
        (Real.norm_exp_I_mul_ofReal_sub_one_le (x := x*t))
    calc
      ‖Complex.I * (x : ℂ)‖ *
          ‖Complex.exp (Complex.I * (x : ℂ) * (t : ℂ)) - 1‖ ≤
          ‖Complex.I * (x : ℂ)‖ * |x*t| :=
        mul_le_mul_of_nonneg_left he (norm_nonneg _)
      _ = x ^ 2 * t := by
        simp only [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
          one_mul, abs_mul, abs_of_pos ht.1]
        rw [← mul_assoc, ← pow_two, sq_abs]
  have h := norm_sub_le_integral_of_norm_deriv_le_of_le
    (a := 0) (b := 1) (f := g) (B := fun t => x ^ 2 * t) zero_le_one
    (fun t _ => (hd t).continuousAt.continuousWithinAt)
    (fun t _ => (hd t).differentiableAt.differentiableWithinAt) hbound
    ((continuous_const.mul continuous_id).intervalIntegrable 0 1)
  have hint : (∫ t : ℝ in (0 : ℝ)..1, x ^ 2 * t) = x ^ 2 / 2 := by
    rw [intervalIntegral.integral_const_mul, integral_id]
    ring
  rw [hint] at h
  simpa [g] using h

/-- Quadratic angular remainder for a finite complex exponential sum. -/
theorem angular_sum_second_moment_bound {ι : Type*} (s : Finset ι)
    (b : ι → ℂ) (x : ι → ℝ) (t : ℝ) :
    ‖(∑ k ∈ s, b k * Complex.exp (Complex.I * ((t*x k : ℝ) : ℂ))) -
        (∑ k ∈ s, b k) -
        Complex.I * (t : ℂ) * (∑ k ∈ s, b k * (x k : ℂ))‖ ≤
      t ^ 2 / 2 * ∑ k ∈ s, ‖b k‖ * (x k) ^ 2 := by
  have heq :
      (∑ k ∈ s, b k * Complex.exp (Complex.I * ((t*x k : ℝ) : ℂ))) -
        (∑ k ∈ s, b k) -
        Complex.I * (t : ℂ) * (∑ k ∈ s, b k * (x k : ℂ)) =
      ∑ k ∈ s, b k *
        (Complex.exp (Complex.I * ((t*x k : ℝ) : ℂ)) - 1 -
          Complex.I * ((t*x k : ℝ) : ℂ)) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    push_cast
    ring
  rw [heq]
  calc
    ‖∑ k ∈ s, b k *
        (Complex.exp (Complex.I * ((t*x k : ℝ) : ℂ)) - 1 -
          Complex.I * ((t*x k : ℝ) : ℂ))‖ ≤
        ∑ k ∈ s, ‖b k‖ * ((t*x k)^2/2) := by
      apply (norm_sum_le ..).trans
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_exp_I_mul_sub_one_sub_le (t*x k))
        (norm_nonneg _)
    _ = t ^ 2 / 2 * ∑ k ∈ s, ‖b k‖ * (x k) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring

/-- A quadratic angular remainder controls the first moment by the chosen
positive rotation size. -/
theorem first_moment_bound_of_angular_error {S D : ℂ} {t M B : ℝ}
    (ht : 0 < t) (hS : ‖S‖ ≤ 2*M)
    (herror : ‖S - Complex.I * (t : ℂ) * D‖ ≤ t^2/2*B) :
    ‖D‖ ≤ 2*M/t + t*B/2 := by
  have htriangle : ‖Complex.I * (t : ℂ) * D‖ ≤ ‖S‖ +
      ‖S - Complex.I * (t : ℂ) * D‖ := by
    simpa [norm_sub_rev] using norm_le_insert S (Complex.I * (t : ℂ) * D)
  have hnorm : ‖Complex.I * (t : ℂ) * D‖ = t * ‖D‖ := by
    simp [abs_of_pos ht]
  rw [hnorm] at htriangle
  have hprod : t * ‖D‖ ≤ 2*M + t^2/2*B :=
    htriangle.trans (add_le_add hS herror)
  calc
    ‖D‖ ≤ (2*M + t^2/2*B)/t := (le_div_iff₀ ht).2 (by simpa [mul_comm] using hprod)
    _ = 2*M/t + t*B/2 := by field_simp

/-- The rotation size `2 * sqrt M / sqrt B` optimizes the elementary angular
bound. Both constants are strictly positive; no division by a vanishing moment
is hidden in this statement. -/
theorem first_moment_bound_optimized {D : ℂ} {M B : ℝ}
    (hM : 0 < M) (hB : 0 < B)
    (h : ∀ t : ℝ, 0 < t → ‖D‖ ≤ 2*M/t + t*B/2) :
    ‖D‖ ≤ 2 * Real.sqrt M * Real.sqrt B := by
  have hMs : 0 < Real.sqrt M := Real.sqrt_pos.2 hM
  have hBs : 0 < Real.sqrt B := Real.sqrt_pos.2 hB
  have hMratio : M / Real.sqrt M = Real.sqrt M := by
    apply (div_eq_iff hMs.ne').2
    nlinarith [Real.sq_sqrt hM.le]
  have hBratio : B / Real.sqrt B = Real.sqrt B := by
    apply (div_eq_iff hBs.ne').2
    nlinarith [Real.sq_sqrt hB.le]
  calc
    ‖D‖ ≤ 2*M/(2*Real.sqrt M/Real.sqrt B) +
        (2*Real.sqrt M/Real.sqrt B)*B/2 := h _ (by positivity)
    _ = (M/Real.sqrt M)*Real.sqrt B + Real.sqrt M*(B/Real.sqrt B) := by
      field_simp
    _ = 2 * Real.sqrt M * Real.sqrt B := by rw [hMratio, hBratio]; ring

/-- A uniform bound on all real rotations, together with a weighted second
moment bound, controls the first moment of a finite exponential sum. -/
theorem angular_sum_first_moment_bound {ι : Type*} (s : Finset ι)
    (b : ι → ℂ) (x : ι → ℝ) {M B : ℝ} (hM : 0 < M) (hB : 0 < B)
    (hmoment : (∑ k ∈ s, ‖b k‖ * (x k)^2) ≤ B)
    (hcircle : ∀ t : ℝ,
      ‖∑ k ∈ s, b k * Complex.exp (Complex.I * ((t*x k : ℝ) : ℂ))‖ ≤ M) :
    ‖∑ k ∈ s, b k * (x k : ℂ)‖ ≤ 2 * Real.sqrt M * Real.sqrt B := by
  apply first_moment_bound_optimized hM hB
  intro t ht
  apply first_moment_bound_of_angular_error ht
    (S := (∑ k ∈ s, b k * Complex.exp (Complex.I * ((t*x k : ℝ) : ℂ))) -
      ∑ k ∈ s, b k)
  · have hzero : ‖∑ k ∈ s, b k‖ ≤ M := by simpa using hcircle 0
    exact (norm_sub_le _ _).trans (by linarith [hcircle t])
  · exact (angular_sum_second_moment_bound s b x t).trans
      (mul_le_mul_of_nonneg_left hmoment (by positivity))

/-- Absolute summability and a summable second moment imply a summable first
moment; this is the inequality `|x| ≤ 1 + x²`. -/
theorem summable_first_moment_of_second {ι : Type*} (b : ι → ℂ) (x : ι → ℝ)
    (hb : Summable fun k => ‖b k‖)
    (hsecond : Summable fun k => ‖b k‖ * (x k)^2) :
    Summable fun k => b k * (x k : ℂ) := by
  apply (hb.add hsecond).of_norm_bounded
  intro k
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hx : |x k| ≤ 1 + (x k)^2 := by
    nlinarith [sq_nonneg (|x k| - 1), sq_abs (x k)]
  calc
    ‖b k‖ * |x k| ≤ ‖b k‖ * (1 + (x k)^2) :=
      mul_le_mul_of_nonneg_left hx (norm_nonneg _)
    _ = ‖b k‖ + ‖b k‖ * (x k)^2 := by ring

/-- The angular second-moment estimate passes to an absolutely convergent
series. All three series in the statement are justified by the hypotheses. -/
theorem angular_tsum_second_moment_bound {ι : Type*} (b : ι → ℂ) (x : ι → ℝ)
    (hb : Summable fun k => ‖b k‖)
    (hsecond : Summable fun k => ‖b k‖ * (x k)^2) (t : ℝ) :
    ‖(∑' k, b k * Complex.exp (Complex.I * ((t*x k : ℝ) : ℂ))) -
        (∑' k, b k) - Complex.I * (t : ℂ) * (∑' k, b k * (x k : ℂ))‖ ≤
      t ^ 2 / 2 * ∑' k, ‖b k‖ * (x k)^2 := by
  have hrot : Summable (fun k => b k * Complex.exp (Complex.I * ((t*x k : ℝ) : ℂ))) := by
    apply hb.of_norm_bounded
    intro k
    simp [Complex.norm_exp, Complex.mul_re]
  have hfirst := summable_first_moment_of_second b x hb hsecond
  exact le_of_tendsto_of_tendsto
    ((Tendsto.sub (Tendsto.sub hrot.hasSum hb.of_norm.hasSum)
      (tendsto_const_nhds.mul hfirst.hasSum)).norm)
    (tendsto_const_nhds.mul hsecond.hasSum)
    (Eventually.of_forall fun s => angular_sum_second_moment_bound s b x t)

/-- For an infinite angular series, a uniform circle bound and a second-moment
bound give the optimized first-moment estimate. -/
theorem angular_tsum_first_moment_bound {ι : Type*} (b : ι → ℂ) (x : ι → ℝ)
    (hb : Summable fun k => ‖b k‖)
    (hsecond : Summable fun k => ‖b k‖ * (x k)^2)
    {M B : ℝ} (hM : 0 < M) (hB : 0 < B)
    (hmoment : (∑' k, ‖b k‖ * (x k)^2) ≤ B)
    (hcircle : ∀ t : ℝ,
      ‖∑' k, b k * Complex.exp (Complex.I * ((t*x k : ℝ) : ℂ))‖ ≤ M) :
    ‖∑' k, b k * (x k : ℂ)‖ ≤ 2 * Real.sqrt M * Real.sqrt B := by
  apply first_moment_bound_optimized hM hB
  intro t ht
  apply first_moment_bound_of_angular_error ht
    (S := (∑' k, b k * Complex.exp (Complex.I * ((t*x k : ℝ) : ℂ))) - ∑' k, b k)
  · have hzero : ‖∑' k, b k‖ ≤ M := by simpa using hcircle 0
    exact (norm_sub_le _ _).trans (by linarith [hcircle t])
  · exact (angular_tsum_second_moment_bound b x hb hsecond t).trans
      (mul_le_mul_of_nonneg_left hmoment (by positivity))

/-- The form used when the second moment is at most `M * a²`: a rotation of
size `2 / a` gives first-moment error at most `2 * M * a`. In the central-index
application, `a` is a negative power of the central index. -/
theorem angular_tsum_first_moment_relative {ι : Type*} (b : ι → ℂ) (x : ι → ℝ)
    (hb : Summable fun k => ‖b k‖)
    (hsecond : Summable fun k => ‖b k‖ * (x k)^2)
    {M a : ℝ} (ha : 0 < a)
    (hmoment : (∑' k, ‖b k‖ * (x k)^2) ≤ M * a^2)
    (hcircle : ∀ t : ℝ,
      ‖∑' k, b k * Complex.exp (Complex.I * ((t*x k : ℝ) : ℂ))‖ ≤ M) :
    ‖∑' k, b k * (x k : ℂ)‖ ≤ 2 * M * a := by
  have hzero : ‖∑' k, b k‖ ≤ M := by simpa using hcircle 0
  have hdiff : ‖(∑' k, b k * Complex.exp (Complex.I * (((2/a)*x k : ℝ) : ℂ))) -
      ∑' k, b k‖ ≤ 2*M :=
    (norm_sub_le _ _).trans (by linarith [hcircle (2/a)])
  have herror := (angular_tsum_second_moment_bound b x hb hsecond (2/a)).trans
    (mul_le_mul_of_nonneg_left hmoment (by positivity))
  calc
    ‖∑' k, b k * (x k : ℂ)‖ ≤ 2*M/(2/a) + (2/a)*(M*a^2)/2 :=
      first_moment_bound_of_angular_error (by positivity) hdiff herror
    _ = 2*M*a := by field_simp; ring

end WimanValiron

#print axioms WimanValiron.norm_exp_I_mul_sub_one_sub_le
#print axioms WimanValiron.angular_sum_second_moment_bound
#print axioms WimanValiron.first_moment_bound_of_angular_error
#print axioms WimanValiron.first_moment_bound_optimized
#print axioms WimanValiron.angular_sum_first_moment_bound
#print axioms WimanValiron.summable_first_moment_of_second
#print axioms WimanValiron.angular_tsum_second_moment_bound
#print axioms WimanValiron.angular_tsum_first_moment_bound
#print axioms WimanValiron.angular_tsum_first_moment_relative
