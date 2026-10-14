import WimanValironHigherDerivatives
import WimanValironAngularEstimate
import Mathlib.Topology.Order.Compact

/-!
# Actual Taylor moments and the angular first-moment estimate

The circle bound in the angular argument is derived from the actual values
of the entire function on the circle. Absolute moments use the actual Taylor
coefficients. The second-moment bound remains an explicit input in this
module; the coefficient-estimate module supplies it at normal radii.
-/

set_option autoImplicit false
noncomputable section
open Filter Polynomial Set
open scoped Topology

namespace WimanValiron

/-- The actual maximum modulus on the circle, defined by its supremum. -/
def circleMaximum (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  sSup ((fun z => ‖f z‖) '' Metric.sphere (0 : ℂ) r)

theorem norm_le_circleMaximum {f : ℂ → ℂ} (hf : Continuous f) {r : ℝ} {z : ℂ}
    (hz : z ∈ Metric.sphere (0 : ℂ) r) : ‖f z‖ ≤ circleMaximum f r := by
  exact le_csSup (((isCompact_sphere (0 : ℂ) r).image hf.norm).bddAbove)
    ⟨z, hz, rfl⟩

/-- Compactness gives a point attaining the circle maximum. -/
theorem exists_norm_eq_circleMaximum {f : ℂ → ℂ} (hf : Continuous f)
    {r : ℝ} (hr : 0 ≤ r) :
    ∃ z ∈ Metric.sphere (0 : ℂ) r, ‖f z‖ = circleMaximum f r := by
  have hne : (Metric.sphere (0 : ℂ) r).Nonempty := by
    refine ⟨(r : ℂ), ?_⟩
    simp [Complex.norm_real, abs_of_nonneg hr]
  obtain ⟨z, hz, heq⟩ := (isCompact_sphere (0 : ℂ) r).exists_sSup_image_eq
    hne hf.norm.continuousOn
  exact ⟨z, hz, heq.symm⟩

theorem maximumTerm_le_circleMaximum {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {r : ℝ} (hr : 0 < r) : maximumTerm (taylorCoeff f) r ≤ circleMaximum f r :=
  maximumTerm_le_circle_bound hf hr (fun _ hz => norm_le_circleMaximum hf.continuous hz)

theorem circleMaximum_pos {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hne : f ≠ 0)
    {r : ℝ} (hr : 0 < r) : 0 < circleMaximum f r :=
  (maximumTerm_pos (taylor_admissible hf hne hr)).trans_le
    (maximumTerm_le_circleMaximum hf hr)

/-- The normalized distance of a Taylor index from its central index. -/
def realCenteredIndex (N n : ℕ) : ℝ := ((n : ℝ) - N) / N

theorem ofReal_realCenteredIndex (N n : ℕ) :
    (realCenteredIndex N n : ℂ) = ((n : ℂ) - N) / N := by
  simp [realCenteredIndex, Complex.ofReal_div, Complex.ofReal_sub]

/-- An unnormalized signed Taylor moment. -/
def rawTaylorMoment (f : ℂ → ℂ) (z : ℂ) (N k : ℕ) : ℂ :=
  ∑' n, (realCenteredIndex N n : ℂ)^k * taylorCoeff f n * z^n

/-- The corresponding absolute coefficient moment on the circle. -/
def absoluteTaylorMoment (f : ℂ → ℂ) (r : ℝ) (N k : ℕ) : ℝ :=
  ∑' n, |realCenteredIndex N n|^k * term (taylorCoeff f) r n

theorem summable_rawTaylorMoment {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hne : f ≠ 0) (z : ℂ) (N k : ℕ) :
    Summable (fun n => (realCenteredIndex N n : ℂ)^k * taylorCoeff f n * z^n) := by
  have hs := summable_polynomial_taylorCoeff hf hne z
    (((X - C (N : ℂ)) * C (N : ℂ)⁻¹)^k)
  simpa only [eval_pow, eval_mul, eval_sub, eval_X, eval_C,
    ofReal_realCenteredIndex, div_eq_mul_inv] using hs

theorem norm_rawTaylorMoment_term {f : ℂ → ℂ} {r : ℝ} {z : ℂ}
    (hz : ‖z‖ = r) (N k n : ℕ) :
    ‖(realCenteredIndex N n : ℂ)^k * taylorCoeff f n * z^n‖ =
      |realCenteredIndex N n|^k * term (taylorCoeff f) r n := by
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, hz, term]
  ring

theorem summable_absoluteTaylorMoment {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hne : f ≠ 0) {r : ℝ} (hr : 0 ≤ r) (N k : ℕ) :
    Summable (fun n => |realCenteredIndex N n|^k * term (taylorCoeff f) r n) := by
  have hs := (summable_rawTaylorMoment hf hne (r : ℂ) N k).norm
  simpa only [norm_rawTaylorMoment_term (show ‖(r : ℂ)‖ = r by
    simp [Complex.norm_real, abs_of_nonneg hr])] using hs

theorem norm_rawTaylorMoment_le {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hne : f ≠ 0) {r : ℝ} {z : ℂ} (hz : ‖z‖ = r) (N k : ℕ) :
    ‖rawTaylorMoment f z N k‖ ≤ absoluteTaylorMoment f r N k := by
  have h := norm_tsum_le_tsum_norm (summable_rawTaylorMoment hf hne z N k).norm
  simpa only [rawTaylorMoment, absoluteTaylorMoment, norm_rawTaylorMoment_term hz] using h

/-- Normalizing the signed moment is precisely division by the actual value of `f`. -/
theorem centeredMoment_eq_raw_div (f : ℂ → ℂ) (z : ℂ) (N k : ℕ) :
    centeredMoment (taylorWeight f z) (N : ℂ) k = rawTaylorMoment f z N k / f z := by
  simp only [centeredMoment, taylorWeight, rawTaylorMoment,
    ofReal_realCenteredIndex, ← mul_div_assoc, ← tsum_div_const, mul_assoc]

theorem angular_taylor_sum {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (z : ℂ) {N : ℕ} (hN : N ≠ 0) (t : ℝ) :
    (∑' n, (taylorCoeff f n * z^n) *
      Complex.exp (Complex.I * ((t * realCenteredIndex N n : ℝ) : ℂ))) =
      Complex.exp (-Complex.I * (t : ℂ)) *
        f (z * Complex.exp (Complex.I * ((t / (N : ℝ) : ℝ) : ℂ))) := by
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  have heq : ∀ n : ℕ,
      Complex.I * ((t * realCenteredIndex N n : ℝ) : ℂ) =
      -Complex.I * (t : ℂ) +
        (n : ℂ) * (Complex.I * ((t / (N : ℝ) : ℝ) : ℂ)) := by
    intro n
    simp only [Complex.ofReal_mul, ofReal_realCenteredIndex, Complex.ofReal_div,
      Complex.ofReal_natCast]
    field_simp
    ring
  have hseries :
      (fun n => (taylorCoeff f n * z^n) *
        Complex.exp (Complex.I * ((t * realCenteredIndex N n : ℝ) : ℂ))) =
      (fun n => Complex.exp (-Complex.I * (t : ℂ)) *
        (taylorCoeff f n *
          (z * Complex.exp (Complex.I * ((t / (N : ℝ) : ℝ) : ℂ)))^n)) := by
    funext n
    rw [heq n, Complex.exp_add, Complex.exp_nat_mul, mul_pow]
    ring
  rw [hseries]
  exact ((hasSum_taylorCoeff hf _).mul_left _).tsum_eq

/-- The angular series is bounded by the actual circle maximum, without
assuming a separate bound on a transformed series. -/
theorem norm_angular_taylor_sum_le {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {r : ℝ} {z : ℂ} (hz : ‖z‖ = r) {N : ℕ} (hN : N ≠ 0) (t : ℝ) :
    ‖∑' n, (taylorCoeff f n * z^n) *
      Complex.exp (Complex.I * ((t * realCenteredIndex N n : ℝ) : ℂ))‖ ≤
      circleMaximum f r := by
  rw [angular_taylor_sum hf z hN t, norm_mul]
  have hphase : ‖Complex.exp (-Complex.I * (t : ℂ))‖ = 1 := by
    simp [Complex.norm_exp, Complex.mul_re]
  rw [hphase, one_mul]
  apply norm_le_circleMaximum hf.continuous
  simp [Complex.norm_exp, Complex.mul_re, hz]

/-- The book's first signed moment bound, obtained from the actual Taylor
rotation and an absolute second moment bound. -/
theorem norm_rawTaylorMoment_one_le {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hne : f ≠ 0) {r : ℝ} {z : ℂ} (hz : ‖z‖ = r) {N : ℕ} (hN : 0 < N)
    {a : ℝ} (ha : 0 < a)
    (hsecond : absoluteTaylorMoment f r N 2 ≤ circleMaximum f r * a^2) :
    ‖rawTaylorMoment f z N 1‖ ≤ 2 * circleMaximum f r * a := by
  have hb := (summable_rawTaylorMoment hf hne z N 0).norm
  have hr : 0 ≤ r := hz ▸ norm_nonneg z
  have h2 := summable_absoluteTaylorMoment hf hne hr N 2
  have hsum : Summable (fun n => ‖taylorCoeff f n * z^n‖) := by
    simpa only [pow_zero, one_mul] using hb
  have hsum2 : Summable (fun n => ‖taylorCoeff f n * z^n‖ *
      (realCenteredIndex N n)^2) := by
    simpa only [norm_mul, norm_pow, hz, sq_abs, term, mul_comm, mul_left_comm,
      mul_assoc] using h2
  have hbound : (∑' n, ‖taylorCoeff f n * z^n‖ * (realCenteredIndex N n)^2) ≤
      circleMaximum f r * a^2 := by
    simpa only [absoluteTaylorMoment, norm_mul, norm_pow, hz, sq_abs, term,
      mul_comm, mul_left_comm, mul_assoc] using hsecond
  have h := angular_tsum_first_moment_relative
    (fun n => taylorCoeff f n * z^n) (realCenteredIndex N) hsum hsum2 ha hbound
    (norm_angular_taylor_sum_le hf hz (Nat.ne_zero_of_lt hN))
  simpa only [rawTaylorMoment, pow_one, mul_comm, mul_left_comm, mul_assoc] using h

/-- An actual raw-moment bound becomes a relative bound at near-maximum
points by dividing by the explicitly positive value of the function. -/
theorem norm_centeredMoment_bound_of_raw {f : ℂ → ℂ} {z : ℂ} {N k : ℕ}
    {M C e b : ℝ} (hN : 0 < N) (hM : 0 < M) (hC : 0 ≤ C)
    (hlower : M * (N : ℝ)^b ≤ ‖f z‖)
    (hraw : ‖rawTaylorMoment f z N k‖ ≤ C * M * (N : ℝ)^e) :
    ‖centeredMoment (taylorWeight f z) (N : ℂ) k‖ ≤ C * (N : ℝ)^(e-b) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hpos : 0 < M * (N : ℝ)^b := mul_pos hM (Real.rpow_pos_of_pos hn b)
  rw [centeredMoment_eq_raw_div, norm_div]
  calc
    ‖rawTaylorMoment f z N k‖ / ‖f z‖ ≤
        (C * M * (N : ℝ)^e) / (M * (N : ℝ)^b) :=
      div_le_div₀ (by positivity) hraw hpos hlower
    _ = C * (N : ℝ)^(e-b) := by
      rw [Real.rpow_sub hn]
      field_simp

/-- Absolute coefficient moments bound every signed moment at near-maximum points. -/
theorem norm_centeredMoment_bound_of_absolute {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hne : f ≠ 0) {r : ℝ} {z : ℂ}
    (hz : ‖z‖ = r) {N k : ℕ} {M C e b : ℝ}
    (hN : 0 < N) (hM : 0 < M) (hC : 0 ≤ C)
    (hlower : M * (N : ℝ)^b ≤ ‖f z‖)
    (habs : absoluteTaylorMoment f r N k ≤ C * M * (N : ℝ)^e) :
    ‖centeredMoment (taylorWeight f z) (N : ℂ) k‖ ≤ C * (N : ℝ)^(e-b) :=
  norm_centeredMoment_bound_of_raw hN hM hC hlower
    ((norm_rawTaylorMoment_le hf hne hz N k).trans habs)

/-- The square-root optimization in the angular estimate yields a concrete
power bound for the first moment from a concrete second-moment bound. -/
theorem norm_rawTaylorMoment_one_of_power_second {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hne : f ≠ 0) {r : ℝ} {z : ℂ}
    (hz : ‖z‖ = r) {N : ℕ} (hN : 0 < N) {C e : ℝ} (hC : 0 < C)
    (hsecond : absoluteTaylorMoment f r N 2 ≤ C * circleMaximum f r * (N : ℝ)^e) :
    ‖rawTaylorMoment f z N 1‖ ≤
      (2 * Real.sqrt C) * circleMaximum f r * (N : ℝ)^(e/2) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  let a : ℝ := Real.sqrt C * (N : ℝ)^(e/2)
  have ha : 0 < a := mul_pos (Real.sqrt_pos.mpr hC) (Real.rpow_pos_of_pos hn _)
  have ha2 : a^2 = C * (N : ℝ)^e := by
    dsimp only [a]
    rw [mul_pow, Real.sq_sqrt hC.le, ← Real.rpow_mul_natCast hn.le]
    norm_num only [Nat.cast_ofNat]
    rw [show e / 2 * (2 : ℝ) = e by ring]
  have hbound : absoluteTaylorMoment f r N 2 ≤ circleMaximum f r * a^2 := by
    rw [ha2]
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hsecond
  have h := norm_rawTaylorMoment_one_le hf hne hz hN ha hbound
  simpa only [a, mul_comm, mul_left_comm, mul_assoc] using h

/-- The quantitative first signed moment at a near-maximum point. -/
theorem norm_centeredMoment_one_of_power_second {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hne : f ≠ 0) {r : ℝ} (hr : 0 < r) {z : ℂ}
    (hz : ‖z‖ = r) {N : ℕ} (hN : 0 < N) {C e b : ℝ} (hC : 0 < C)
    (hlower : circleMaximum f r * (N : ℝ)^b ≤ ‖f z‖)
    (hsecond : absoluteTaylorMoment f r N 2 ≤ C * circleMaximum f r * (N : ℝ)^e) :
    ‖centeredMoment (taylorWeight f z) (N : ℂ) 1‖ ≤
      (2 * Real.sqrt C) * (N : ℝ)^(e/2-b) :=
  norm_centeredMoment_bound_of_raw hN (circleMaximum_pos hf hne hr) (by positivity)
    hlower (norm_rawTaylorMoment_one_of_power_second hf hne hz hN hC hsecond)

end WimanValiron

#print axioms WimanValiron.norm_le_circleMaximum
#print axioms WimanValiron.exists_norm_eq_circleMaximum
#print axioms WimanValiron.maximumTerm_le_circleMaximum
#print axioms WimanValiron.circleMaximum_pos
#print axioms WimanValiron.ofReal_realCenteredIndex
#print axioms WimanValiron.summable_rawTaylorMoment
#print axioms WimanValiron.norm_rawTaylorMoment_term
#print axioms WimanValiron.summable_absoluteTaylorMoment
#print axioms WimanValiron.norm_rawTaylorMoment_le
#print axioms WimanValiron.centeredMoment_eq_raw_div
#print axioms WimanValiron.angular_taylor_sum
#print axioms WimanValiron.norm_angular_taylor_sum_le
#print axioms WimanValiron.norm_rawTaylorMoment_one_le
#print axioms WimanValiron.norm_centeredMoment_bound_of_raw
#print axioms WimanValiron.norm_centeredMoment_bound_of_absolute
#print axioms WimanValiron.norm_rawTaylorMoment_one_of_power_second
#print axioms WimanValiron.norm_centeredMoment_one_of_power_second
