import WimanValironTheorem
import WimanValironGoodRadii
import Mathlib.Analysis.Asymptotics.Defs

/-!
# The customary Wiman--Valiron asymptotic formula

The quantitative theorem gives an actual relative error tending to zero.
These corollaries use the filter of radii outside the constructed exceptional
set. That filter is nontrivial, and maximum-modulus points satisfying the
near-maximum hypothesis exist arbitrarily far out.
-/

set_option autoImplicit false
noncomputable section
open Filter Set Asymptotics
open scoped Topology

namespace WimanValiron

/-- The central-index error power tends to zero on every subfilter of distant radii. -/
theorem centralIndex_error_power_tendsto_zero {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hnp : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z)
    {δ : ℝ} (hδupper : δ < 1/8) {l : Filter ℝ} (hl : l ≤ atTop) :
    Tendsto (fun r => (centralIndex (taylorCoeff f) r : ℝ)^(-1/8+δ)) l (𝓝 0) := by
  have hN : Tendsto (fun r => (centralIndex (taylorCoeff f) r : ℝ)) l atTop :=
    tendsto_natCast_atTop_atTop.comp ((taylor_centralIndex_tendsto_atTop hf hnp).mono_left hl)
  have hp := (tendsto_rpow_neg_atTop (show 0 < 1/8-δ by linarith)).comp hN
  have he : -((1 : ℝ)/8-δ) = -1/8+δ := by ring
  simpa only [Function.comp_def, he] using hp

/-- A quantitative normalized-derivative error gives the actual limiting ratio. -/
theorem derivativeRatio_tendsto_one_of_power_error {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hnp : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z)
    {δ : ℝ} (hδupper : δ < 1/8) {l : Filter ℝ} (hl : l ≤ atTop)
    {j : ℕ} {z : ℝ → ℂ} {C : ℝ}
    (hbound : ∀ᶠ r in l, ‖derivativeRatio f (centralIndex (taylorCoeff f) r) j (z r)-1‖ ≤
      C * (centralIndex (taylorCoeff f) r : ℝ)^(-1/8+δ)) :
    Tendsto (fun r => derivativeRatio f (centralIndex (taylorCoeff f) r) j (z r))
      l (𝓝 1) := by
  have hp := (centralIndex_error_power_tendsto_zero hf hnp hδupper hl).const_mul C
  have he := squeeze_zero_norm' hbound (by simpa only [mul_zero] using hp)
  simpa only [sub_add_cancel, zero_add] using he.add_const (1 : ℂ)

/-- The complete derivative asymptotic, including a Big-O error bound, for
any choice of near-maximum points outside one actual exceptional set. -/
theorem wimanValiron_asymptotic {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnp : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z)
    {δ : ℝ} (hδ : 0 < δ) (hδupper : δ < 1/8) :
    ∃ E : Set ℝ, MeasurableSet E ∧ HelmrathExceptionalSet.FiniteLogarithmicMeasure E ∧
      (atTop ⊓ 𝓟 Eᶜ).NeBot ∧
      ∀ (j : ℕ) (z : ℝ → ℂ),
        (∀ᶠ r in atTop ⊓ 𝓟 Eᶜ, ‖z r‖ = r ∧
          circleMaximum f r * (centralIndex (taylorCoeff f) r : ℝ)^(-1/8+δ) ≤ ‖f (z r)‖) →
        ((fun r => derivativeRatio f (centralIndex (taylorCoeff f) r) j (z r)-1)
          =O[atTop ⊓ 𝓟 Eᶜ]
            (fun r => (centralIndex (taylorCoeff f) r : ℝ)^(-1/8+δ))) ∧
        Tendsto (fun r => derivativeRatio f (centralIndex (taylorCoeff f) r) j (z r))
          (atTop ⊓ 𝓟 Eᶜ) (𝓝 1) := by
  obtain ⟨E, hEm, hE, hquant⟩ := wimanValiron_quantitative hf hnp hδ hδupper
  refine ⟨E, hEm, hE, good_radii_neBot hEm hE, ?_⟩
  intro j z hpoint
  obtain ⟨C, _hC, R, _hR, htail⟩ := hquant j
  have hR : ∀ᶠ r in atTop ⊓ 𝓟 Eᶜ, R ≤ r :=
    (eventually_ge_atTop R).filter_mono inf_le_left
  have hgood : ∀ᶠ r in atTop ⊓ 𝓟 Eᶜ, r ∉ E :=
    (show ∀ᶠ r in 𝓟 Eᶜ, r ∉ E from by simp).filter_mono inf_le_right
  have hbound : ∀ᶠ r in atTop ⊓ 𝓟 Eᶜ,
      ‖derivativeRatio f (centralIndex (taylorCoeff f) r) j (z r)-1‖ ≤
        C * (centralIndex (taylorCoeff f) r : ℝ)^(-1/8+δ) := by
    filter_upwards [hR, hgood, hpoint] with r hr hg hz
    exact (htail r hr hg).2 (z r) hz.1 hz.2
  refine ⟨IsBigO.of_bound C ?_,
    derivativeRatio_tendsto_one_of_power_error hf hnp hδupper inf_le_left hbound⟩
  simpa only [Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)] using hbound

/-- The exact displayed `f^(j)/f = (nu/z)^j * (1 + eta)` formula, with
`eta -> 0` and the quantitative Big-O rate on a nontrivial good-radius filter. -/
theorem wimanValiron_asymptotic_formula {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnp : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z)
    {δ : ℝ} (hδ : 0 < δ) (hδupper : δ < 1/8) :
    ∃ E : Set ℝ, MeasurableSet E ∧ HelmrathExceptionalSet.FiniteLogarithmicMeasure E ∧
      (atTop ⊓ 𝓟 Eᶜ).NeBot ∧
      ∀ (j : ℕ) (z : ℝ → ℂ),
        (∀ᶠ r in atTop ⊓ 𝓟 Eᶜ, ‖z r‖ = r ∧
          circleMaximum f r * (centralIndex (taylorCoeff f) r : ℝ)^(-1/8+δ) ≤ ‖f (z r)‖) →
        ∃ η : ℝ → ℂ, Tendsto η (atTop ⊓ 𝓟 Eᶜ) (𝓝 0) ∧
          (η =O[atTop ⊓ 𝓟 Eᶜ]
            (fun r => (centralIndex (taylorCoeff f) r : ℝ)^(-1/8+δ))) ∧
          ∀ᶠ r in atTop ⊓ 𝓟 Eᶜ,
            iteratedDeriv j f (z r) / f (z r) =
              ((centralIndex (taylorCoeff f) r : ℂ) / z r)^j * (1 + η r) := by
  obtain ⟨E, hEm, hE, hnebot, hasymp⟩ := wimanValiron_asymptotic hf hnp hδ hδupper
  refine ⟨E, hEm, hE, hnebot, ?_⟩
  intro j z hpoint
  obtain ⟨hbig, hlim⟩ := hasymp j z hpoint
  refine ⟨(fun r => derivativeRatio f (centralIndex (taylorCoeff f) r) j (z r)-1),
    ?_, hbig, ?_⟩
  · simpa only [sub_self] using hlim.sub_const (1 : ℂ)
  · have hidx : ∀ᶠ r in atTop ⊓ 𝓟 Eᶜ, 1 ≤ centralIndex (taylorCoeff f) r :=
      ((taylor_centralIndex_tendsto_atTop hf hnp).eventually (eventually_ge_atTop 1)).filter_mono
        inf_le_left
    have hpos : ∀ᶠ r in atTop ⊓ 𝓟 Eᶜ, 0 < r :=
      (eventually_gt_atTop (0 : ℝ)).filter_mono inf_le_left
    have hne : f ≠ 0 := by intro h; exact hnp ⟨0, by simp [h]⟩
    filter_upwards [hidx, hpos, hpoint] with r hN hr hz
    have hNr : (0 : ℝ) < centralIndex (taylorCoeff f) r := by exact_mod_cast hN
    have hfz : f (z r) ≠ 0 := norm_pos_iff.mp
      ((mul_pos (circleMaximum_pos hf hne hr) (Real.rpow_pos_of_pos hNr _)).trans_le hz.2)
    exact derivative_eq_with_relative_error (norm_pos_iff.mp (hz.1.symm ▸ hr))
      (Nat.ne_zero_of_lt hN) hfz

/-- There is an actual choice of maximum-modulus points for which every fixed
derivative has the normalized Wiman--Valiron limit. No good-point selection
or derivative comparison is assumed as input. -/
theorem wimanValiron_at_maximum_points {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnp : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z)
    {δ : ℝ} (hδ : 0 < δ) (hδupper : δ < 1/8) :
    ∃ E : Set ℝ, MeasurableSet E ∧ HelmrathExceptionalSet.FiniteLogarithmicMeasure E ∧
      (atTop ⊓ 𝓟 Eᶜ).NeBot ∧ ∃ z : ℝ → ℂ,
        (∀ r > 0, ‖z r‖ = r ∧ ‖f (z r)‖ = circleMaximum f r) ∧
        ∀ j : ℕ,
          ((fun r => derivativeRatio f (centralIndex (taylorCoeff f) r) j (z r)-1)
            =O[atTop ⊓ 𝓟 Eᶜ]
              (fun r => (centralIndex (taylorCoeff f) r : ℝ)^(-1/8+δ))) ∧
          Tendsto (fun r => derivativeRatio f (centralIndex (taylorCoeff f) r) j (z r))
            (atTop ⊓ 𝓟 Eᶜ) (𝓝 1) := by
  classical
  obtain ⟨E, hEm, hE, hnebot, hasymp⟩ := wimanValiron_asymptotic hf hnp hδ hδupper
  have hchoices : ∀ r : ℝ, ∃ z : ℂ,
      0 < r → ‖z‖ = r ∧ ‖f z‖ = circleMaximum f r := by
    intro r
    by_cases hr : 0 < r
    · obtain ⟨z, hz, hmax⟩ := exists_norm_eq_circleMaximum hf.continuous hr.le
      refine ⟨z, fun _ => ⟨?_, hmax⟩⟩
      simpa only [Metric.mem_sphere, dist_zero_right] using hz
    · exact ⟨0, fun h => False.elim (hr h)⟩
  choose z hz using hchoices
  refine ⟨E, hEm, hE, hnebot, z, hz, ?_⟩
  have hidx : ∀ᶠ r in atTop ⊓ 𝓟 Eᶜ, 1 ≤ centralIndex (taylorCoeff f) r :=
    ((taylor_centralIndex_tendsto_atTop hf hnp).eventually (eventually_ge_atTop 1)).filter_mono
      inf_le_left
  have hpos : ∀ᶠ r in atTop ⊓ 𝓟 Eᶜ, 0 < r :=
    (eventually_gt_atTop (0 : ℝ)).filter_mono inf_le_left
  have hne : f ≠ 0 := by intro h; exact hnp ⟨0, by simp [h]⟩
  have hpoint : ∀ᶠ r in atTop ⊓ 𝓟 Eᶜ, ‖z r‖ = r ∧
      circleMaximum f r * (centralIndex (taylorCoeff f) r : ℝ)^(-1/8+δ) ≤ ‖f (z r)‖ := by
    filter_upwards [hidx, hpos] with r hN hr
    refine ⟨(hz r hr).1, ?_⟩
    rw [(hz r hr).2]
    have hNr : (1 : ℝ) ≤ centralIndex (taylorCoeff f) r := by exact_mod_cast hN
    have hpower := Real.rpow_le_one_of_one_le_of_nonpos hNr
      (show -(1 : ℝ)/8+δ ≤ 0 by linarith)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hpower
      (circleMaximum_pos hf hne hr).le
  exact fun j => hasymp j z hpoint

end WimanValiron

#print axioms WimanValiron.centralIndex_error_power_tendsto_zero
#print axioms WimanValiron.derivativeRatio_tendsto_one_of_power_error
#print axioms WimanValiron.wimanValiron_asymptotic
#print axioms WimanValiron.wimanValiron_asymptotic_formula
#print axioms WimanValiron.wimanValiron_at_maximum_points
