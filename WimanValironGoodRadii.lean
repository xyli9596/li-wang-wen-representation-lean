import WimanValironTaylorMoments
import HelmrathExceptionalSet

/-!
# Nonvacuity of the Wiman--Valiron domain

A measurable exceptional set of finite logarithmic measure leaves arbitrarily
large positive radii. For a transcendental entire function, maximum-modulus
points on sufficiently large good circles satisfy the strict near-maximum
condition. Thus restricting asymptotics to these radii does not give a bottom
filter, and the pointwise domain is nonempty arbitrarily far out.
-/

set_option autoImplicit false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology

namespace WimanValiron

/-- Finite logarithmic measure cannot remove an entire positive tail. -/
theorem exists_arbitrarily_large_good_radius {E : Set ℝ}
    (hEm : MeasurableSet E) (hE : HelmrathExceptionalSet.FiniteLogarithmicMeasure E)
    (R : ℝ) : ∃ r ≥ R, 0 < r ∧ r ∉ E := by
  have hdensity := HelmrathExceptionalSet.zero_density_of_finite_logarithmic_measure hEm hE
  have hgood := HelmrathExceptionalSet.exists_good_radius hdensity
    (a := 1) (b := 2) (by norm_num) (by norm_num)
  obtain ⟨t, ht, hlarge⟩ := (hgood.and (eventually_ge_atTop (max 1 R))).exists
  obtain ⟨r, hr, hnot⟩ := ht
  have htr : t ≤ r := by simpa only [one_mul] using hr.1
  have hR : R ≤ t := (le_max_right _ _).trans hlarge
  have htpos : 0 < t := zero_lt_one.trans_le ((le_max_left _ _).trans hlarge)
  exact ⟨r, hR.trans htr, htpos.trans_le htr, hnot⟩

/-- The filter used for asymptotics outside the exceptional set is nontrivial. -/
theorem good_radii_neBot {E : Set ℝ}
    (hEm : MeasurableSet E) (hE : HelmrathExceptionalSet.FiniteLogarithmicMeasure E) :
    (atTop ⊓ 𝓟 Eᶜ : Filter ℝ).NeBot := by
  apply frequently_mem_iff_neBot.mp
  apply frequently_atTop.mpr
  intro R
  obtain ⟨r, hr, _, hnot⟩ := exists_arbitrarily_large_good_radius hEm hE R
  exact ⟨r, hr, hnot⟩

/-- Once the actual central index is at least two, any point attaining the
circle maximum satisfies the strict near-maximum condition for `δ < 1/8`. -/
theorem exists_maximum_point_near_maximum {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hne : f ≠ 0) {r δ : ℝ} (hr : 0 < r)
    (hN : 2 ≤ centralIndex (taylorCoeff f) r) (hδ : δ < (1 : ℝ)/8) :
    ∃ z : ℂ, ‖z‖ = r ∧ ‖f z‖ = circleMaximum f r ∧ f z ≠ 0 ∧
      circleMaximum f r *
        (centralIndex (taylorCoeff f) r : ℝ)^(-(1 : ℝ)/8+δ) < ‖f z‖ := by
  obtain ⟨z, hz, hmax⟩ := exists_norm_eq_circleMaximum hf.continuous hr.le
  have hM : 0 < circleMaximum f r := circleMaximum_pos hf hne hr
  have hNr : (1 : ℝ) < centralIndex (taylorCoeff f) r := by
    exact_mod_cast (show 1 < centralIndex (taylorCoeff f) r by omega)
  have hpower := Real.rpow_lt_one_of_one_lt_of_neg hNr
    (show -(1 : ℝ)/8+δ < 0 by linarith)
  have hstrict : circleMaximum f r *
      (centralIndex (taylorCoeff f) r : ℝ)^(-(1 : ℝ)/8+δ) < circleMaximum f r := by
    simpa only [mul_one] using mul_lt_mul_of_pos_left hpower hM
  have hzrad : ‖z‖ = r := by simpa [Metric.mem_sphere] using hz
  refine ⟨z, hzrad, hmax, ?_, ?_⟩
  · exact norm_pos_iff.mp (by rw [hmax]; exact hM)
  · rwa [hmax]

/-- Transcendental entire functions have arbitrarily distant good circles
with actual nonzero maximum points satisfying the strict near-maximum bound.
Only the upper bound on `δ` is needed for this nonvacuity statement. -/
theorem exists_arbitrarily_large_good_maximum_point {f : ℂ → ℂ} {E : Set ℝ} {δ : ℝ}
    (hf : Differentiable ℂ f)
    (hnp : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z)
    (hEm : MeasurableSet E) (hE : HelmrathExceptionalSet.FiniteLogarithmicMeasure E)
    (hδ : δ < (1 : ℝ)/8) (R : ℝ) :
    ∃ r ≥ R, 0 < r ∧ r ∉ E ∧ 2 ≤ centralIndex (taylorCoeff f) r ∧
      ∃ z : ℂ, ‖z‖ = r ∧ ‖f z‖ = circleMaximum f r ∧ f z ≠ 0 ∧
        circleMaximum f r *
          (centralIndex (taylorCoeff f) r : ℝ)^(-(1 : ℝ)/8+δ) < ‖f z‖ := by
  have hne : f ≠ 0 := by
    intro hz
    exact hnp ⟨0, by simp [hz]⟩
  have hlarge : ∀ᶠ r : ℝ in atTop, 2 ≤ centralIndex (taylorCoeff f) r :=
    (taylor_centralIndex_tendsto_atTop hf hnp).eventually (eventually_ge_atTop 2)
  obtain ⟨S, hS⟩ := eventually_atTop.mp hlarge
  obtain ⟨r, hr, hrpos, hgood⟩ := exists_arbitrarily_large_good_radius hEm hE (max R S)
  have hN := hS r ((le_max_right _ _).trans hr)
  exact ⟨r, (le_max_left _ _).trans hr, hrpos, hgood, hN,
    exists_maximum_point_near_maximum hf hne hrpos hN hδ⟩

#print axioms exists_arbitrarily_large_good_radius
#print axioms good_radii_neBot
#print axioms exists_maximum_point_near_maximum
#print axioms exists_arbitrarily_large_good_maximum_point

end WimanValiron
