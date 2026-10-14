import WimanValironNormalRadii
import HelmrathExceptionalSet
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# The logarithmic measure of the gaps in Wiman's comparison construction

For positive radial scales `s n` and bounded increasing factors `q n`, the union
of the intervals `(s n * q n, s n * q (n+1))` has finite logarithmic measure.
This proves the measure-theoretic part of He Yuzan, Lemma 1.1, p. 24.
The separate assertion that these gaps cover all nonnormal radii is an explicit
hypothesis in the final corollaries, not hidden in a definition or proved here.
Countable endpoints are allowed: at a jump, the last-maximizer convention for
the central index can exclude an endpoint from the old-index normal interval.
-/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace WimanValiron

/-- The actual measure with density `dr/r` on the positive half-line. -/
def logarithmicMeasure : Measure ℝ :=
  volume.withDensity (fun r : ℝ => ENNReal.ofReal r⁻¹)

/-- Exact logarithmic measure of a positive half-open interval. -/
theorem logarithmicMeasure_Ioc {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    logarithmicMeasure (Ioc a b) = ENNReal.ofReal (Real.log (b / a)) := by
  have hb : 0 < b := ha.trans_le hab
  have hcont : ContinuousOn (fun x : ℝ => x⁻¹) (Icc a b) :=
    continuousOn_id.inv₀ (fun x hx => ne_of_gt (ha.trans_le hx.1))
  have hint : IntegrableOn (fun x : ℝ => x⁻¹) (Ioc a b) :=
    hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc a b)] (fun x : ℝ => x⁻¹) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact inv_nonneg.mpr (ha.trans hx.1).le
  rw [logarithmicMeasure, withDensity_apply _ measurableSet_Ioc,
    ← ofReal_integral_eq_lintegral_ofReal hint hnonneg,
    ← intervalIntegral.integral_of_le hab, integral_inv_of_pos ha hb]

/-- The open interval has at most its usual logarithmic length. -/
theorem logarithmicMeasure_Ioo_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    logarithmicMeasure (Ioo a b) ≤ ENNReal.ofReal (Real.log (b / a)) := by
  calc
    _ ≤ logarithmicMeasure (Ioc a b) := measure_mono Ioo_subset_Ioc_self
    _ = _ := logarithmicMeasure_Ioc ha hab

/-- The gaps produced when the auxiliary central index jumps. -/
def comparisonGap (s q : ℕ → ℝ) (n : ℕ) : Set ℝ :=
  Ioo (s n * q n) (s n * q (n + 1))

/-- Each gap has logarithmic measure bounded by the change of comparison factor. -/
theorem logarithmicMeasure_comparisonGap_le {s q : ℕ → ℝ}
    (hs : ∀ n, 0 < s n) (hq : ∀ n, 0 < q n) (hmono : Monotone q) (n : ℕ) :
    logarithmicMeasure (comparisonGap s q n) ≤
      ENNReal.ofReal (Real.log (q (n + 1) / q n)) := by
  have h := logarithmicMeasure_Ioo_le (mul_pos (hs n) (hq n))
    (mul_le_mul_of_nonneg_left (hmono (Nat.le_succ n)) (hs n).le)
  simpa only [comparisonGap, mul_div_mul_left _ _ (ne_of_gt (hs n))] using h

/-- Countable subadditivity and the telescope control the entire union of gaps. -/
theorem logarithmicMeasure_iUnion_comparisonGap_le {s q : ℕ → ℝ} {P : ℝ}
    (hs : ∀ n, 0 < s n) (hq : ∀ n, 0 < q n)
    (hmono : Monotone q) (hP : ∀ n, q n ≤ P) :
    logarithmicMeasure (⋃ n, comparisonGap s q n) ≤
      ENNReal.ofReal (Real.log P - Real.log (q 0)) := by
  obtain ⟨hsum, hbound⟩ := summable_log_gaps hq hmono hP
  have hn : ∀ n, 0 ≤ Real.log (q (n + 1) / q n) := by
    intro n
    exact Real.log_nonneg ((one_le_div (hq n)).mpr (hmono (Nat.le_succ n)))
  calc
    _ ≤ ∑' n, logarithmicMeasure (comparisonGap s q n) := measure_iUnion_le _
    _ ≤ ∑' n, ENNReal.ofReal (Real.log (q (n + 1) / q n)) :=
      ENNReal.tsum_le_tsum (logarithmicMeasure_comparisonGap_le hs hq hmono)
    _ = ENNReal.ofReal (∑' n, Real.log (q (n + 1) / q n)) :=
      (ENNReal.ofReal_tsum_of_nonneg hn hsum).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hbound

/-- The explicitly constructed union of gaps has finite logarithmic measure. -/
theorem finiteLogarithmicMeasure_iUnion_comparisonGap {s q : ℕ → ℝ} {P : ℝ}
    (hs : ∀ n, 0 < s n) (hq : ∀ n, 0 < q n)
    (hmono : Monotone q) (hP : ∀ n, q n ≤ P) :
    HelmrathExceptionalSet.FiniteLogarithmicMeasure (⋃ n, comparisonGap s q n) := by
  have hm : MeasurableSet (⋃ n, comparisonGap s q n) :=
    MeasurableSet.iUnion (fun _ => measurableSet_Ioo)
  have hbound := logarithmicMeasure_iUnion_comparisonGap_le hs hq hmono hP
  apply lt_of_le_of_lt (lintegral_mono_set inter_subset_left)
  rw [← withDensity_apply _ hm]
  exact lt_of_le_of_lt hbound ENNReal.ofReal_lt_top

/-- Any set covered, on the positive tail, by the comparison gaps has finite
logarithmic measure. Establishing the covering for nonnormal radii remains a
separate geometric step. -/
theorem finiteLogarithmicMeasure_of_comparisonGap_cover {E : Set ℝ}
    {s q : ℕ → ℝ} {P : ℝ}
    (hs : ∀ n, 0 < s n) (hq : ∀ n, 0 < q n)
    (hmono : Monotone q) (hP : ∀ n, q n ≤ P)
    (hcover : E ∩ Ici 1 ⊆ ⋃ n, comparisonGap s q n) :
    HelmrathExceptionalSet.FiniteLogarithmicMeasure E := by
  have hm : MeasurableSet (⋃ n, comparisonGap s q n) :=
    MeasurableSet.iUnion (fun _ => measurableSet_Ioo)
  have hbound := logarithmicMeasure_iUnion_comparisonGap_le hs hq hmono hP
  apply lt_of_le_of_lt (lintegral_mono_set hcover)
  rw [← withDensity_apply _ hm]
  exact lt_of_le_of_lt hbound ENNReal.ofReal_lt_top

/-- Countable endpoints are null for the actual logarithmic measure. -/
theorem logarithmicMeasure_countable {C : Set ℝ} (hC : C.Countable) :
    logarithmicMeasure C = 0 :=
  withDensity_absolutelyContinuous volume _ (hC.measure_zero volume)

/-- Adding countably many jump endpoints does not increase the gap-measure bound. -/
theorem logarithmicMeasure_comparisonGaps_union_countable_le
    {s q : ℕ → ℝ} {P : ℝ} {C : Set ℝ}
    (hs : ∀ n, 0 < s n) (hq : ∀ n, 0 < q n)
    (hmono : Monotone q) (hP : ∀ n, q n ≤ P) (hC : C.Countable) :
    logarithmicMeasure ((⋃ n, comparisonGap s q n) ∪ C) ≤
      ENNReal.ofReal (Real.log P - Real.log (q 0)) := by
  calc
    _ ≤ logarithmicMeasure (⋃ n, comparisonGap s q n) + logarithmicMeasure C :=
      measure_union_le _ _
    _ = logarithmicMeasure (⋃ n, comparisonGap s q n) := by
      rw [logarithmicMeasure_countable hC, add_zero]
    _ ≤ _ := logarithmicMeasure_iUnion_comparisonGap_le hs hq hmono hP

/-- A cover by comparison gaps and countable endpoints suffices for finite
logarithmic measure. The endpoint clause accommodates the last-maximizer
convention at jumps; the covering itself remains explicit. -/
theorem finiteLogarithmicMeasure_of_comparisonGap_cover_with_endpoints
    {E C : Set ℝ} {s q : ℕ → ℝ} {P : ℝ}
    (hs : ∀ n, 0 < s n) (hq : ∀ n, 0 < q n)
    (hmono : Monotone q) (hP : ∀ n, q n ≤ P) (hC : C.Countable)
    (hcover : E ∩ Ici 1 ⊆ (⋃ n, comparisonGap s q n) ∪ C) :
    HelmrathExceptionalSet.FiniteLogarithmicMeasure E := by
  have hm : MeasurableSet ((⋃ n, comparisonGap s q n) ∪ C) :=
    (MeasurableSet.iUnion (fun _ => measurableSet_Ioo)).union hC.measurableSet
  have hbound := logarithmicMeasure_comparisonGaps_union_countable_le hs hq hmono hP hC
  apply lt_of_le_of_lt (lintegral_mono_set hcover)
  rw [← withDensity_apply _ hm]
  exact lt_of_le_of_lt hbound ENNReal.ofReal_lt_top

#print axioms logarithmicMeasure_Ioc
#print axioms logarithmicMeasure_Ioo_le
#print axioms logarithmicMeasure_comparisonGap_le
#print axioms logarithmicMeasure_iUnion_comparisonGap_le
#print axioms finiteLogarithmicMeasure_iUnion_comparisonGap
#print axioms finiteLogarithmicMeasure_of_comparisonGap_cover

#print axioms logarithmicMeasure_countable
#print axioms logarithmicMeasure_comparisonGaps_union_countable_le
#print axioms finiteLogarithmicMeasure_of_comparisonGap_cover_with_endpoints

end WimanValiron
