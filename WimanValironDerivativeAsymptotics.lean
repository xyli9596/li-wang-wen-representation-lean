import WimanValironCauchyTransfer
import WimanValironMaximumTerm
import Mathlib.Analysis.SpecialFunctions.Choose

/-!
# Normalization of Wiman--Valiron derivative estimates

A qualitative consequence of He Yuzan, Section 1.4, Theorem 1.16 is that
the normalized derivatives tend to one. The book also gives a quantitative
relative-error bound, which is not yet assembled here. This module proves
the normalization step, including the falling-factorial correction and a
Cauchy-transfer criterion. Producing the local monomial approximation on
radii outside a set of finite logarithmic measure is a separate analytic
obligation.

All limits are formulated over an arbitrary filter, so they also apply to
the good radii or good points used by the book. No existence of such a set
is assumed to have been proved here.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology

namespace WimanValiron

/-- The relative derivative ratio which tends to one in the WV theorem. -/
def derivativeRatio (f : ℂ → ℂ) (N j : ℕ) (z : ℂ) : ℂ :=
  z ^ j * iteratedDeriv j f z / ((N : ℂ) ^ j * f z)

/-- The correction from falling factorials to powers vanishes for fixed order. -/
theorem tendsto_descFactorial_div_pow (j : ℕ) :
    Tendsto (fun N : ℕ => (N.descFactorial j : ℂ) / (N : ℂ)^j)
      atTop (𝓝 1) := by
  have hn : ∀ᶠ N : ℕ in atTop, (N : ℝ)^j ≠ 0 := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    exact pow_ne_zero _ (by exact_mod_cast (Nat.ne_zero_of_lt hN))
  have h := (Asymptotics.isEquivalent_iff_tendsto_one hn).mp
    (isEquivalent_descFactorial j)
  have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp h
  simpa only [Function.comp_def, Pi.div_apply, Complex.ofReal_div,
    Complex.ofReal_pow, Complex.ofReal_natCast, Complex.ofReal_one] using hc

/-- The same correction along any central-index function tending to infinity. -/
theorem tendsto_descFactorial_div_pow_comp {α : Type*} {l : Filter α}
    {N : α → ℕ} (hN : Tendsto N l atTop) (j : ℕ) :
    Tendsto (fun x => ((N x).descFactorial j : ℂ) / (N x : ℂ)^j)
      l (𝓝 1) :=
  (tendsto_descFactorial_div_pow j).comp hN

/-- A vanishing relative error from the monomial derivative gives the desired
WV ratio, with no restriction on the filter of admissible points. -/
theorem derivativeRatio_tendsto_of_fallingFactorial_error
    {α : Type*} {l : Filter α} {f : ℂ → ℂ} {N : α → ℕ} {z : α → ℂ}
    (hN : Tendsto N l atTop) (j : ℕ)
    (herr : Tendsto (fun x =>
      (z x ^ j * iteratedDeriv j f (z x) / f (z x) -
        ((N x).descFactorial j : ℂ)) / (N x : ℂ)^j) l (𝓝 0)) :
    Tendsto (fun x => derivativeRatio f (N x) j (z x)) l (𝓝 1) := by
  have h := herr.add (tendsto_descFactorial_div_pow_comp hN j)
  simp only [zero_add] at h
  convert h using 1
  funext x
  dsimp only [derivativeRatio]
  rw [sub_div, sub_add_cancel, div_div]
  rw [mul_comm (f (z x))]

/-- The normalized ratio is exactly the coefficient of the multiplicative
error in the customary displayed derivative formula. -/
theorem derivative_eq_with_relative_error {f : ℂ → ℂ} {N j : ℕ} {z : ℂ}
    (hz : z ≠ 0) (hN : N ≠ 0) (hfz : f z ≠ 0) :
    iteratedDeriv j f z / f z = ((N : ℂ) / z)^j *
      (1 + (derivativeRatio f N j z - 1)) := by
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  simp only [derivativeRatio, div_pow]
  field_simp
  ring

/-- Quantitative normalization of a Cauchy-transfer bound. -/
theorem derivativeRatio_sub_descFactorial_bound {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {z : ℂ} (hz : z ≠ 0) (hfz : f z ≠ 0)
    {δ η : ℝ} (hδ : 0 < δ) (N j : ℕ) (hN : 0 < N)
    (herror : ∀ w ∈ Metric.sphere z δ, ‖f w / f z - (w / z) ^ N‖ ≤ η) :
    ‖derivativeRatio f N j z - (N.descFactorial j : ℂ) / (N : ℂ)^j‖ ≤
      (j.factorial : ℝ) * (‖z‖ / (δ * (N : ℝ)))^j * η := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have heq : derivativeRatio f N j z - (N.descFactorial j : ℂ) / (N : ℂ)^j =
      (z ^ j * iteratedDeriv j f z / f z - (N.descFactorial j : ℂ)) / (N : ℂ)^j := by
    simp only [derivativeRatio, sub_div, div_div]
    rw [mul_comm (f z)]
  rw [heq, norm_div, norm_pow, Complex.norm_natCast]
  have h := cauchy_transfer_of_monomial_circle_bound hf hz hfz hδ N j herror
  calc
    ‖z ^ j * iteratedDeriv j f z / f z - (N.descFactorial j : ℂ)‖ / (N : ℝ)^j ≤
        ((j.factorial : ℝ) * (‖z‖ / δ)^j * η) / (N : ℝ)^j :=
      div_le_div_of_nonneg_right h (pow_nonneg hn.le _)
    _ = (j.factorial : ℝ) * (‖z‖ / (δ * (N : ℝ)))^j * η := by
      simp only [div_pow, mul_pow]
      ring

/-- Local monomial approximation with a vanishing normalized Cauchy error
implies the derivative asymptotic along the same filter. -/
theorem derivativeRatio_tendsto_of_monomial_circle_bound
    {α : Type*} {l : Filter α} {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {N : α → ℕ} {z : α → ℂ} {δ η : α → ℝ}
    (hN : Tendsto N l atTop) (j : ℕ)
    (hlocal : ∀ᶠ x in l, z x ≠ 0 ∧ f (z x) ≠ 0 ∧ 0 < δ x ∧
      ∀ w ∈ Metric.sphere (z x) (δ x),
        ‖f w / f (z x) - (w / z x) ^ N x‖ ≤ η x)
    (hsmall : Tendsto (fun x => (‖z x‖ / (δ x * (N x : ℝ)))^j * η x)
      l (𝓝 0)) :
    Tendsto (fun x => derivativeRatio f (N x) j (z x)) l (𝓝 1) := by
  have hb : ∀ᶠ x in l,
      ‖derivativeRatio f (N x) j (z x) - ((N x).descFactorial j : ℂ) / (N x : ℂ)^j‖ ≤
        (j.factorial : ℝ) * ((‖z x‖ / (δ x * (N x : ℝ)))^j * η x) := by
    filter_upwards [hlocal, hN.eventually (eventually_gt_atTop (0 : ℕ))] with x hx hn
    simpa only [mul_assoc] using derivativeRatio_sub_descFactorial_bound
      hf hx.1 hx.2.1 hx.2.2.1 (N x) j hn hx.2.2.2
  have herr := squeeze_zero_norm' hb
    (by simpa only [mul_zero] using hsmall.const_mul (j.factorial : ℝ))
  have h := herr.add (tendsto_descFactorial_div_pow_comp hN j)
  simpa only [sub_add_cancel, zero_add] using h

/-- Dividing an absolute scaled-derivative error by a near-maximum lower
bound gives a relative error. The exponents are deliberately explicit. -/
theorem derivativeRatio_error_bound_of_near_maximum {f : ℂ → ℂ} {N j : ℕ} {z : ℂ}
    {M C a b : ℝ} (hN : 0 < N) (hM : 0 < M) (hC : 0 ≤ C)
    (hlower : M * (N : ℝ)^b ≤ ‖f z‖)
    (herror : ‖z ^ j * iteratedDeriv j f z / (N : ℂ)^j - f z‖ ≤
      C * M * (N : ℝ)^a) :
    ‖derivativeRatio f N j z - 1‖ ≤ C * (N : ℝ)^(a-b) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hpos : 0 < M * (N : ℝ)^b := mul_pos hM (Real.rpow_pos_of_pos hn b)
  have hfz : f z ≠ 0 := norm_pos_iff.mp (hpos.trans_le hlower)
  have heq : derivativeRatio f N j z - 1 =
      (z ^ j * iteratedDeriv j f z / (N : ℂ)^j - f z) / f z := by
    rw [sub_div, div_self hfz, div_div]
    rfl
  rw [heq, norm_div]
  calc
    ‖z ^ j * iteratedDeriv j f z / (N : ℂ)^j - f z‖ / ‖f z‖ ≤
        (C * M * (N : ℝ)^a) / (M * (N : ℝ)^b) :=
      div_le_div₀ (by positivity) herror hpos hlower
    _ = C * (N : ℝ)^(a-b) := by
      rw [Real.rpow_sub hn]
      field_simp

/-- The absolute estimate used in Theorems 1.15--1.16 gives the usual
relative derivative asymptotic whenever its power is below the allowed
near-maximum threshold. Construction of that estimate remains separate. -/
theorem derivativeRatio_tendsto_of_near_maximum
    {α : Type*} {l : Filter α} {f : ℂ → ℂ} {N : α → ℕ} {z : α → ℂ}
    {M : α → ℝ} {C a b : ℝ} (hN : Tendsto N l atTop)
    (hC : 0 ≤ C) (hab : a < b) (j : ℕ)
    (hlocal : ∀ᶠ x in l, 0 < M x ∧ M x * (N x : ℝ)^b ≤ ‖f (z x)‖ ∧
      ‖z x ^ j * iteratedDeriv j f (z x) / (N x : ℂ)^j - f (z x)‖ ≤
        C * M x * (N x : ℝ)^a) :
    Tendsto (fun x => derivativeRatio f (N x) j (z x)) l (𝓝 1) := by
  have hp : Tendsto (fun x => (N x : ℝ)^(a-b)) l (𝓝 0) := by
    have hn : Tendsto (fun x => (N x : ℝ)) l atTop :=
      tendsto_natCast_atTop_atTop.comp hN
    have h := (tendsto_rpow_neg_atTop (sub_pos.mpr hab)).comp hn
    simpa only [Function.comp_def, neg_sub] using h
  have hb : ∀ᶠ x in l, ‖derivativeRatio f (N x) j (z x) - 1‖ ≤ C * (N x : ℝ)^(a-b) := by
    filter_upwards [hlocal, hN.eventually (eventually_gt_atTop (0 : ℕ))] with x hx hn
    exact derivativeRatio_error_bound_of_near_maximum hn hx.1 hC hx.2.1 hx.2.2
  have he := squeeze_zero_norm' hb (by simpa only [mul_zero] using hp.const_mul C)
  simpa only [sub_add_cancel, zero_add] using he.add_const (1 : ℂ)

end WimanValiron

#print axioms WimanValiron.tendsto_descFactorial_div_pow
#print axioms WimanValiron.tendsto_descFactorial_div_pow_comp
#print axioms WimanValiron.derivativeRatio_tendsto_of_fallingFactorial_error
#print axioms WimanValiron.derivative_eq_with_relative_error
#print axioms WimanValiron.derivativeRatio_sub_descFactorial_bound
#print axioms WimanValiron.derivativeRatio_tendsto_of_monomial_circle_bound
#print axioms WimanValiron.derivativeRatio_error_bound_of_near_maximum
#print axioms WimanValiron.derivativeRatio_tendsto_of_near_maximum
