import WimanValironLogarithmicMeasure
import Mathlib.Data.Nat.Find

/-!
# Normal radii outside an actual exceptional set

The monotonicity of the auxiliary central index gives a countable cover of all
nonnormal positive radii by comparison gaps and their endpoints. The cover is
proved here, rather than assumed. A generalized threshold for each integer
index avoids any assumption that all central-index jumps have size one.
-/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory

namespace WimanValiron

/-- An index lies between two values attained on the positive half-line. -/
def HasIndexCrossing (ν : ℝ → ℕ) (n : ℕ) : Prop :=
  ∃ lo hi : ℝ, 0 < lo ∧ 0 < hi ∧ ν lo ≤ n ∧ n < ν hi

/-- The threshold of the lower central-index set, with a harmless positive
value when the index is never crossed. -/
def indexThreshold (ν : ℝ → ℕ) (n : ℕ) : ℝ := by
  classical
  exact if HasIndexCrossing ν n then sSup {t : ℝ | 0 < t ∧ ν t ≤ n} else 1

/-- Monotonicity bounds the lower index set by any upper witness. -/
theorem index_lower_set_le {ν : ℝ → ℕ} {n : ℕ} {hi t : ℝ}
    (hν : MonotoneOn ν (Ioi 0)) (hhi : 0 < hi) (hn : n < ν hi)
    (ht : 0 < t ∧ ν t ≤ n) : t ≤ hi := by
  by_contra h
  have hle := hν hhi ht.1 (le_of_lt (lt_of_not_ge h))
  omega

/-- The threshold lies between every pair of witnesses that straddle an index. -/
theorem indexThreshold_between {ν : ℝ → ℕ} {n : ℕ} {lo hi : ℝ}
    (hν : MonotoneOn ν (Ioi 0)) (hlo : 0 < lo) (hhi : 0 < hi)
    (hlower : ν lo ≤ n) (hupper : n < ν hi) :
    lo ≤ indexThreshold ν n ∧ indexThreshold ν n ≤ hi := by
  have hcross : HasIndexCrossing ν n := ⟨lo, hi, hlo, hhi, hlower, hupper⟩
  have hne : ({t : ℝ | 0 < t ∧ ν t ≤ n} : Set ℝ).Nonempty :=
    ⟨lo, hlo, hlower⟩
  have hbound : BddAbove {t : ℝ | 0 < t ∧ ν t ≤ n} :=
    ⟨hi, fun _ ht => index_lower_set_le hν hhi hupper ht⟩
  rw [indexThreshold, if_pos hcross]
  exact ⟨le_csSup hbound ⟨hlo, hlower⟩,
    csSup_le hne (fun _ ht => index_lower_set_le hν hhi hupper ht)⟩

/-- Every threshold used as a radial scale is strictly positive. -/
theorem indexThreshold_pos {ν : ℝ → ℕ}
    (hν : MonotoneOn ν (Ioi 0)) (n : ℕ) : 0 < indexThreshold ν n := by
  by_cases h : HasIndexCrossing ν n
  · obtain ⟨lo, hi, hlo, hhi, hlower, hupper⟩ := h
    exact hlo.trans_le (indexThreshold_between hν hlo hhi hlower hupper).1
  · simp only [indexThreshold, if_neg h, zero_lt_one]

/-- A decreasing integer-valued rescaling either has a fixed index or crosses
one between two consecutive comparison factors. -/
theorem fixed_index_or_crossing {ν : ℝ → ℕ} {p : ℕ → ℝ} {r : ℝ}
    (hν : MonotoneOn ν (Ioi 0)) (hp : ∀ n, 0 < p n)
    (hmono : Monotone p) (hr : 0 < r) :
    (∃ N, ν (r / p N) = N) ∨
      ∃ N, ν (r / p (N + 1)) ≤ N ∧ N < ν (r / p N) := by
  classical
  let F : ℕ → ℕ := fun n => ν (r / p n)
  let K := F 0
  have hbound : ∀ n, F n ≤ K := by
    intro n
    exact hν (div_pos hr (hp n)) (div_pos hr (hp 0))
      (div_le_div_of_nonneg_left hr.le (hp 0) (hmono (Nat.zero_le n)))
  let N := Nat.findGreatest (fun n => n ≤ F n) K
  have hN : N ≤ F N := Nat.findGreatest_spec (P := fun n => n ≤ F n)
    (Nat.zero_le K) (Nat.zero_le (F 0))
  by_cases heq : F N = N
  · exact Or.inl ⟨N, heq⟩
  · right
    refine ⟨N, ?_, lt_of_le_of_ne hN (Ne.symm heq)⟩
    change F (N + 1) ≤ N
    by_contra h
    have hn : N + 1 ≤ F (N + 1) := Nat.succ_le_of_lt (lt_of_not_ge h)
    have hb : N + 1 ≤ K := hn.trans (hbound (N + 1))
    have hc : N + 1 ≤ N := Nat.le_findGreatest hb hn
    omega

/-- The actual radial cover, obtained from monotonicity with no covering input. -/
theorem normal_fixed_index_or_closed_gap {ν : ℝ → ℕ} {p : ℕ → ℝ} {r : ℝ}
    (hν : MonotoneOn ν (Ioi 0)) (hp : ∀ n, 0 < p n)
    (hmono : Monotone p) (hr : 0 < r) :
    (∃ N, ν (r / p N) = N) ∨
      ∃ N, r ∈ Icc (indexThreshold ν N * p N)
        (indexThreshold ν N * p (N + 1)) := by
  rcases fixed_index_or_crossing hν hp hmono hr with h | ⟨N, hlo, hhi⟩
  · exact Or.inl h
  · right
    have hbetween := indexThreshold_between hν
      (div_pos hr (hp (N + 1))) (div_pos hr (hp N)) hlo hhi
    exact ⟨N, (le_div_iff₀ (hp N)).mp hbetween.2,
      (div_le_iff₀ (hp (N + 1))).mp hbetween.1⟩

/-- The countable endpoint set needed for either convention at a jump. -/
def indexGapEndpoints (ν : ℝ → ℕ) (p : ℕ → ℝ) : Set ℝ :=
  Set.range (fun n => indexThreshold ν n * p n) ∪
    Set.range (fun n => indexThreshold ν n * p (n + 1))

/-- An explicit exceptional set built only from the actual index and factors. -/
def indexExceptionalSet (ν : ℝ → ℕ) (p : ℕ → ℝ) : Set ℝ :=
  (⋃ n, comparisonGap (indexThreshold ν) p n) ∪ indexGapEndpoints ν p

theorem indexGapEndpoints_countable (ν : ℝ → ℕ) (p : ℕ → ℝ) :
    (indexGapEndpoints ν p).Countable :=
  (Set.countable_range _).union (Set.countable_range _)

theorem indexExceptionalSet_measurable (ν : ℝ → ℕ) (p : ℕ → ℝ) :
    MeasurableSet (indexExceptionalSet ν p) :=
  (MeasurableSet.iUnion (fun _ => measurableSet_Ioo)).union
    (indexGapEndpoints_countable ν p).measurableSet

/-- Both endpoints and the interior of every closed gap are exceptional. -/
theorem closed_gap_subset_indexExceptionalSet (ν : ℝ → ℕ) (p : ℕ → ℝ) (N : ℕ) :
    Icc (indexThreshold ν N * p N) (indexThreshold ν N * p (N + 1)) ⊆
      indexExceptionalSet ν p := by
  intro r hr
  by_cases hl : r = indexThreshold ν N * p N
  · exact Or.inr (Or.inl ⟨N, hl.symm⟩)
  by_cases hu : r = indexThreshold ν N * p (N + 1)
  · exact Or.inr (Or.inr ⟨N, hu.symm⟩)
  exact Or.inl (Set.mem_iUnion.mpr ⟨N,
    lt_of_le_of_ne hr.1 (Ne.symm hl), lt_of_le_of_ne hr.2 hu⟩)

/-- Outside the constructed exceptional set, the rescaled index has a fixed point. -/
theorem fixed_index_outside_exceptional {ν : ℝ → ℕ} {p : ℕ → ℝ} {r : ℝ}
    (hν : MonotoneOn ν (Ioi 0)) (hp : ∀ n, 0 < p n)
    (hmono : Monotone p) (hr : 0 < r) (hgood : r ∉ indexExceptionalSet ν p) :
    ∃ N, ν (r / p N) = N := by
  rcases normal_fixed_index_or_closed_gap hν hp hmono hr with h | ⟨N, hN⟩
  · exact h
  · exact False.elim (hgood (closed_gap_subset_indexExceptionalSet ν p N hN))

/-- The actual exceptional set has finite logarithmic measure. -/
theorem finiteLogarithmicMeasure_indexExceptionalSet {ν : ℝ → ℕ} {p : ℕ → ℝ} {P : ℝ}
    (hν : MonotoneOn ν (Ioi 0)) (hp : ∀ n, 0 < p n)
    (hmono : Monotone p) (hP : ∀ n, p n ≤ P) :
    HelmrathExceptionalSet.FiniteLogarithmicMeasure (indexExceptionalSet ν p) := by
  exact finiteLogarithmicMeasure_of_comparisonGap_cover_with_endpoints
    (indexThreshold_pos hν) hp hmono hP (indexGapEndpoints_countable ν p) inter_subset_left

/-- Wiman's normal radii exist at every positive radius outside a measurable
exceptional set of finite logarithmic measure. No geometric cover is assumed. -/
theorem exists_exceptional_set_normal_radii {a : ℕ → ℂ} {p : ℕ → ℝ} {P : ℝ}
    (ha : ∀ r > 0, Admissible a r) (hp : ∀ n, 0 < p n)
    (hmono : Monotone p) (hP : ∀ n, p n ≤ P) :
    ∃ E : Set ℝ, MeasurableSet E ∧ HelmrathExceptionalSet.FiniteLogarithmicMeasure E ∧
      ∀ r > 0, r ∉ E → ∃ N, NormalRadiusAt a p r N := by
  let ν : ℝ → ℕ := centralIndex (comparisonCoeff a p)
  have hν : MonotoneOn ν (Ioi 0) := by
    intro r hr s hs hrs
    exact centralIndex_le (comparison_admissible ha hp hP hr)
      (comparison_admissible ha hp hP hs) hrs
  refine ⟨indexExceptionalSet ν p, indexExceptionalSet_measurable ν p,
    finiteLogarithmicMeasure_indexExceptionalSet hν hp hmono hP, ?_⟩
  intro r hr hgood
  obtain ⟨N, hN⟩ := fixed_index_outside_exceptional hν hp hmono hr hgood
  refine ⟨N, hr, ?_⟩
  have hcentral := centralIndex_spec (comparison_admissible ha hp hP (div_pos hr (hp N)))
  change IsCentralIndex (comparisonCoeff a p) (r / p N) (ν (r / p N)) at hcentral
  rwa [hN] at hcentral

#print axioms index_lower_set_le
#print axioms indexThreshold_between
#print axioms indexThreshold_pos
#print axioms fixed_index_or_crossing
#print axioms normal_fixed_index_or_closed_gap
#print axioms indexGapEndpoints_countable
#print axioms indexExceptionalSet_measurable
#print axioms closed_gap_subset_indexExceptionalSet
#print axioms fixed_index_outside_exceptional
#print axioms finiteLogarithmicMeasure_indexExceptionalSet
#print axioms exists_exceptional_set_normal_radii

end WimanValiron
