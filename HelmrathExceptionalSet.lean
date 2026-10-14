import LevinDensity
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Removing a radial exceptional set from a monotone power asymptotic

This isolates the exceptional-set removal argument in Helmrath--Nikolaus,
Section 3 (pp. 394--395). We prove the conversion from finite logarithmic measure to zero radial
density using dominated convergence, followed by the monotone squeeze argument.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace HelmrathExceptionalSet

/-- Finite logarithmic measure on the positive tail, defined by the actual
Lebesgue integral of `dr / r`. Finite initial intervals are immaterial. -/
def FiniteLogarithmicMeasure (E : Set ℝ) : Prop :=
  (∫⁻ r : ℝ in E ∩ Ici 1, ENNReal.ofReal (r⁻¹)) < ⊤

/-- Finite logarithmic measure implies zero radial density. -/
theorem zero_density_of_finite_logarithmic_measure {E : Set ℝ}
    (hEm : MeasurableSet E) (hE : FiniteLogarithmicMeasure E) :
    LevinDensity.ZeroRadialDensity E := by
  let S := E ∩ Ici (1 : ℝ)
  let μ : Measure ℝ := volume.restrict S
  have hSm : MeasurableSet S := hEm.inter measurableSet_Ici
  have hmem : ∀ᵐ x : ℝ ∂μ, x ∈ S := ae_restrict_mem hSm
  have hnonneg : 0 ≤ᵐ[μ] (fun x : ℝ => x⁻¹) := by
    filter_upwards [hmem] with x hx
    exact inv_nonneg.mpr (zero_le_one.trans hx.2)
  have hint : Integrable (fun x : ℝ => x⁻¹) μ := by
    refine ⟨measurable_inv.aestronglyMeasurable, ?_⟩
    exact (hasFiniteIntegral_iff_ofReal hnonneg).mpr hE
  let F : ℝ → ℝ → ℝ := fun R => (Iic R).indicator (fun _ => R⁻¹)
  have hFmeas : ∀ᶠ R : ℝ in atTop, AEStronglyMeasurable (F R) μ := by
    exact Eventually.of_forall (fun R =>
      (measurable_const.indicator measurableSet_Iic).aestronglyMeasurable)
  have hbound : ∀ᶠ R : ℝ in atTop, ∀ᵐ x : ℝ ∂μ, ‖F R x‖ ≤ x⁻¹ := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    filter_upwards [hmem] with x hx
    have hxpos : 0 < x := zero_lt_one.trans_le hx.2
    have hRpos : 0 < R := zero_lt_one.trans_le hR
    by_cases hxR : x ≤ R
    · dsimp only [F]
      rw [Set.indicator_of_mem (show x ∈ Iic R from hxR),
        Real.norm_of_nonneg (inv_nonneg.mpr hRpos.le)]
      exact inv_anti₀ hxpos hxR
    · dsimp only [F]
      rw [Set.indicator_of_notMem (show x ∉ Iic R from hxR), norm_zero]
      exact inv_nonneg.mpr hxpos.le
  have hpoint : ∀ᵐ x : ℝ ∂μ, Tendsto (fun R => F R x) atTop (𝓝 0) := by
    apply Eventually.of_forall
    intro x
    apply tendsto_inv_atTop_zero.congr'
    filter_upwards [eventually_ge_atTop x] with R hR
    dsimp only [F]
    rw [Set.indicator_of_mem (show x ∈ Iic R from hR)]
  have hlim : Tendsto (fun R => ∫ x, F R x ∂μ) atTop (𝓝 0) := by
    simpa only [integral_zero] using
      (tendsto_integral_filter_of_dominated_convergence
        (fun x : ℝ => x⁻¹) hFmeas hbound hint hpoint)
  have hzero : LevinDensity.ZeroRadialDensity S := by
    apply (LevinDensity.zeroRadialDensity_iff_tendsto S).mpr
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    rw [show (∫ x, F R x ∂μ) = μ.real (Iic R) * R⁻¹ by
      simp only [F, integral_indicator_const _ measurableSet_Iic, smul_eq_mul]]
    rw [show μ.real (Iic R) = volume.real (Iic R ∩ S) from
      measureReal_restrict_apply measurableSet_Iic]
    have hsets : Iic R ∩ S = S ∩ Icc 0 R := by
      ext x
      constructor
      · rintro ⟨hxR, hxS⟩
        exact ⟨hxS, zero_le_one.trans hxS.2, hxR⟩
      · rintro ⟨hxS, _, hxR⟩
        exact ⟨hxR, hxS⟩
    rw [hsets]
    rfl
  apply (hzero.union (LevinDensity.zeroRadialDensity_Iic 1)).mono
  intro x hx
  by_cases hx1 : 1 ≤ x
  · exact Or.inl ⟨hx, hx1⟩
  · exact Or.inr (le_of_lt (lt_of_not_ge hx1))

/-- Every sufficiently distant fixed relative interval contains a good radius. -/
theorem exists_good_radius {E : Set ℝ} (hE : LevinDensity.ZeroRadialDensity E)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∀ᶠ r : ℝ in atTop, ∃ s ∈ Icc (a * r) (b * r), s ∉ E := by
  have hb : 0 < b := lt_of_le_of_lt ha hab
  have heps : 0 < (b - a) / (2 * b) := by positivity
  obtain ⟨R, _, hR⟩ := hE ((b - a) / (2 * b)) heps
  filter_upwards [eventually_ge_atTop (max 1 (R / b))] with r hr
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hr)
  have hbr : R ≤ b * r := by
    have := (div_le_iff₀ hb).mp ((le_max_right _ _).trans hr)
    nlinarith
  have hnot : ¬ Icc (a * r) (b * r) ⊆ E := by
    intro hs
    have hsub : Icc (a * r) (b * r) ⊆ E ∩ Icc 0 (b * r) := by
      intro x hx
      exact ⟨hs hx, (mul_nonneg ha hrpos.le).trans hx.1, hx.2⟩
    have hm := (measure_mono hsub).trans (hR (b * r) hbr)
    rw [Real.volume_Icc] at hm
    have hsmall : 0 ≤ (b - a) / (2 * b) * (b * r) := by positivity
    have hreal := (ENNReal.ofReal_le_ofReal_iff hsmall).mp hm
    have hcancel : (b - a) / (2 * b) * (b * r) = (b - a) * r / 2 := by
      field_simp
    rw [hcancel] at hreal
    nlinarith
  exact Set.not_subset.mp hnot

/-- A positive multiple of a real power can be approximated from radii below one. -/
theorem exists_scale_below {a d ρ : ℝ} (had : a < d) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ a < d * t ^ ρ := by
  have hc : Tendsto (fun t : ℝ => d * t ^ ρ) (𝓝 (1 : ℝ)) (𝓝 d) := by
    simpa only [Pi.mul_def, Real.one_rpow, mul_one] using (continuousAt_const.mul
      (Real.continuousAt_rpow_const 1 ρ (Or.inl one_ne_zero))).tendsto
  have hval := (hc.eventually (eventually_gt_nhds had)).filter_mono
    (show 𝓝[<] (1 : ℝ) ≤ 𝓝 1 from nhdsWithin_le_nhds)
  have hpos : ∀ᶠ t : ℝ in 𝓝[<] 1, 0 < t :=
    (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  have hlt : ∀ᶠ t : ℝ in 𝓝[<] 1, t < 1 := self_mem_nhdsWithin
  exact (hpos.and (hlt.and hval)).exists

/-- A positive multiple of a real power can be approximated from radii above one. -/
theorem exists_scale_above {d b ρ : ℝ} (hdb : d < b) :
    ∃ t : ℝ, 1 < t ∧ d * t ^ ρ < b := by
  have hc : Tendsto (fun t : ℝ => d * t ^ ρ) (𝓝 (1 : ℝ)) (𝓝 d) := by
    simpa only [Pi.mul_def, Real.one_rpow, mul_one] using (continuousAt_const.mul
      (Real.continuousAt_rpow_const 1 ρ (Or.inl one_ne_zero))).tendsto
  have hval := (hc.eventually (eventually_lt_nhds hdb)).filter_mono
    (show 𝓝[>] (1 : ℝ) ≤ 𝓝 1 from nhdsWithin_le_nhds)
  have hgt : ∀ᶠ t : ℝ in 𝓝[>] 1, 1 < t := self_mem_nhdsWithin
  exact (hgt.and hval).exists

/-- A monotone function's positive power asymptotic extends across any set of
zero radial density. No continuity of the monotone function is required. -/
theorem remove_zero_density_exception {E : Set ℝ} {ν : ℝ → ℝ} {ρ c : ℝ}
    (hE : LevinDensity.ZeroRadialDensity E)
    (hν : MonotoneOn ν (Ioi 0)) (hρ : 0 ≤ ρ) (hc : 0 < c)
    (hlim : Tendsto (fun r : ℝ => ν r / r ^ ρ)
      (atTop ⊓ 𝓟 Eᶜ) (𝓝 c)) :
    Tendsto (fun r : ℝ => ν r / r ^ ρ) atTop (𝓝 c) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    obtain ⟨d, hd, hdc⟩ := exists_between (max_lt ha hc)
    have had : a < d := (le_max_left _ _).trans_lt hd
    have hdpos : 0 < d := (le_max_right _ _).trans_lt hd
    obtain ⟨t, htpos, htone, hat⟩ := exists_scale_below (ρ := ρ) had
    have hout := (Filter.eventually_inf_principal.mp
      ((tendsto_order.mp hlim).1 d hdc))
    obtain ⟨R, hR⟩ := eventually_atTop.mp hout
    filter_upwards [exists_good_radius hE htpos.le htone,
      eventually_ge_atTop (max 1 (R / t))] with r hs hr
    have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hr)
    obtain ⟨s, hs, hsE⟩ := hs
    have hsr : s ≤ r := by simpa using hs.2
    have hspos : 0 < s := (mul_pos htpos hrpos).trans_le hs.1
    have hRs : R ≤ s := by
      have := (div_le_iff₀ htpos).mp ((le_max_right _ _).trans hr)
      nlinarith [hs.1]
    have hsd : d * s ^ ρ < ν s :=
      (lt_div_iff₀ (Real.rpow_pos_of_pos hspos ρ)).mp (hR s hRs hsE)
    have hpower := Real.rpow_le_rpow (mul_nonneg htpos.le hrpos.le) hs.1 hρ
    rw [Real.mul_rpow htpos.le hrpos.le] at hpower
    have hνsr := hν hspos hrpos hsr
    apply (lt_div_iff₀ (Real.rpow_pos_of_pos hrpos ρ)).mpr
    calc
      a * r ^ ρ < (d * t ^ ρ) * r ^ ρ :=
        mul_lt_mul_of_pos_right hat (Real.rpow_pos_of_pos hrpos ρ)
      _ = d * (t ^ ρ * r ^ ρ) := by ring
      _ ≤ d * s ^ ρ := mul_le_mul_of_nonneg_left hpower hdpos.le
      _ < ν s := hsd
      _ ≤ ν r := hνsr
  · intro b hb
    obtain ⟨d, hcd, hdb⟩ := exists_between hb
    have hdpos : 0 < d := hc.trans hcd
    obtain ⟨t, htone, htb⟩ := exists_scale_above (ρ := ρ) hdb
    have htpos : 0 < t := zero_lt_one.trans htone
    have hout := (Filter.eventually_inf_principal.mp
      ((tendsto_order.mp hlim).2 d hcd))
    obtain ⟨R, hR⟩ := eventually_atTop.mp hout
    filter_upwards [exists_good_radius hE (show (0 : ℝ) ≤ 1 by norm_num) htone,
      eventually_ge_atTop (max 1 R)] with r hs hr
    have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hr)
    obtain ⟨s, hs, hsE⟩ := hs
    have hrs : r ≤ s := by simpa using hs.1
    have hspos : 0 < s := hrpos.trans_le hrs
    have hRs : R ≤ s := ((le_max_right _ _).trans hr).trans hrs
    have hsd : ν s < d * s ^ ρ :=
      (div_lt_iff₀ (Real.rpow_pos_of_pos hspos ρ)).mp (hR s hRs hsE)
    have hpower := Real.rpow_le_rpow hspos.le hs.2 hρ
    rw [Real.mul_rpow htpos.le hrpos.le] at hpower
    have hνrs := hν hrpos hspos hrs
    apply (div_lt_iff₀ (Real.rpow_pos_of_pos hrpos ρ)).mpr
    calc
      ν r ≤ ν s := hνrs
      _ < d * s ^ ρ := hsd
      _ ≤ d * (t ^ ρ * r ^ ρ) := mul_le_mul_of_nonneg_left hpower hdpos.le
      _ = (d * t ^ ρ) * r ^ ρ := by ring
      _ < b * r ^ ρ := mul_lt_mul_of_pos_right htb (Real.rpow_pos_of_pos hrpos ρ)

/-- The finite-logarithmic-measure exceptional-set removal used in the
central-index argument. The logarithmic measure is an actual Lebesgue integral. -/
theorem remove_finite_logarithmic_exception {E : Set ℝ} {ν : ℝ → ℝ} {ρ c : ℝ}
    (hEm : MeasurableSet E) (hE : FiniteLogarithmicMeasure E)
    (hν : MonotoneOn ν (Ioi 0)) (hρ : 0 ≤ ρ) (hc : 0 < c)
    (hlim : Tendsto (fun r : ℝ => ν r / r ^ ρ)
      (atTop ⊓ 𝓟 Eᶜ) (𝓝 c)) :
    Tendsto (fun r : ℝ => ν r / r ^ ρ) atTop (𝓝 c) :=
  remove_zero_density_exception (zero_density_of_finite_logarithmic_measure hEm hE)
    hν hρ hc hlim

end HelmrathExceptionalSet

#print axioms HelmrathExceptionalSet.exists_good_radius

#print axioms HelmrathExceptionalSet.exists_scale_below
#print axioms HelmrathExceptionalSet.exists_scale_above
#print axioms HelmrathExceptionalSet.remove_zero_density_exception

#print axioms HelmrathExceptionalSet.zero_density_of_finite_logarithmic_measure

#print axioms HelmrathExceptionalSet.remove_finite_logarithmic_exception
