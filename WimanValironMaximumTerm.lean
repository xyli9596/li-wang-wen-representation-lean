import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Find
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic

/-!
# Maximum term and central index

The coefficient sequence of a nonzero entire power series has a largest
weighted coefficient at every positive radius. The central index is the
largest index attaining this maximum, and it is nondecreasing in the radius.

This module proves that elementary foundation of Wiman--Valiron theory.
It does not assert the derivative asymptotics or an exceptional-set theorem.
The hypotheses below are coefficient conditions, not a substitute for those
analytic conclusions.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology

namespace WimanValiron

/-- The modulus of the `n`th power-series term on the circle of radius `r`. -/
def term (a : ℕ → ℂ) (r : ℝ) (n : ℕ) : ℝ := ‖a n‖ * r ^ n

/-- The elementary coefficient conditions needed at one radius. -/
def Admissible (a : ℕ → ℂ) (r : ℝ) : Prop :=
  0 < r ∧ Tendsto (term a r) atTop (𝓝 0) ∧ ∃ n, a n ≠ 0

/-- A maximal index among all indices attaining the maximum value. -/
def IsCentralIndex (a : ℕ → ℂ) (r : ℝ) (n : ℕ) : Prop :=
  (∀ m, term a r m ≤ term a r n) ∧
    ∀ m, term a r m = term a r n → m ≤ n

theorem term_nonneg (a : ℕ → ℂ) {r : ℝ} (hr : 0 ≤ r) (n : ℕ) :
    0 ≤ term a r n := mul_nonneg (norm_nonneg _) (pow_nonneg hr _)

theorem term_pos {a : ℕ → ℂ} {r : ℝ} {n : ℕ} (hr : 0 < r) (ha : a n ≠ 0) :
    0 < term a r n := mul_pos (norm_pos_iff.mpr ha) (pow_pos hr _)

/-- A sequence tending to zero and having a positive term has a last maximum. -/
theorem exists_last_maximum {u : ℕ → ℝ} (hu : Tendsto u atTop (𝓝 0))
    (hpos : ∃ n, 0 < u n) :
    ∃ n, (∀ m, u m ≤ u n) ∧ ∀ m, u m = u n → m ≤ n := by
  classical
  obtain ⟨k, hk⟩ := hpos
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hu.eventually_lt_const hk)
  let K := max N k
  obtain ⟨j, hj, hjmax⟩ := (Finset.range (K + 1)).exists_max_image u
    ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ K)⟩
  have hkK : k ∈ Finset.range (K + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (le_max_right N k))
  have hglobal : ∀ m, u m ≤ u j := by
    intro m
    by_cases hm : m ≤ K
    · exact hjmax m (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))
    · exact (hN m ((le_max_left N k).trans (le_of_lt (lt_of_not_ge hm)))).le.trans
        (hjmax k hkK)
  have hbound : ∀ m, u m = u j → m ≤ K := by
    intro m hm
    by_contra h
    have hlt := hN m ((le_max_left N k).trans (le_of_lt (lt_of_not_ge h)))
    rw [hm] at hlt
    exact (not_lt_of_ge (hjmax k hkK)) hlt
  let n := Nat.findGreatest (fun m => u m = u j) K
  have hn : u n = u j := Nat.findGreatest_spec (P := fun m => u m = u j)
    (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) rfl
  refine ⟨n, ?_, ?_⟩
  · intro m
    rw [hn]
    exact hglobal m
  · intro m hm
    have hmj : u m = u j := hm.trans hn
    exact Nat.le_findGreatest (hbound m hmj) hmj

theorem exists_centralIndex {a : ℕ → ℂ} {r : ℝ} (h : Admissible a r) :
    ∃ n, IsCentralIndex a r n := by
  obtain ⟨k, hk⟩ := h.2.2
  exact exists_last_maximum h.2.1 ⟨k, term_pos h.1 hk⟩

/-- The last maximal index, with the harmless default zero outside its domain. -/
def centralIndex (a : ℕ → ℂ) (r : ℝ) : ℕ := by
  classical
  exact if h : ∃ n, IsCentralIndex a r n then Classical.choose h else 0

/-- The maximum term at an admissible radius. -/
def maximumTerm (a : ℕ → ℂ) (r : ℝ) : ℝ := term a r (centralIndex a r)

theorem centralIndex_spec {a : ℕ → ℂ} {r : ℝ} (h : Admissible a r) :
    IsCentralIndex a r (centralIndex a r) := by
  unfold centralIndex
  rw [dif_pos (exists_centralIndex h)]
  exact Classical.choose_spec (exists_centralIndex h)

theorem term_le_maximumTerm {a : ℕ → ℂ} {r : ℝ} (h : Admissible a r) (n : ℕ) :
    term a r n ≤ maximumTerm a r := (centralIndex_spec h).1 n

theorem maximumTerm_pos {a : ℕ → ℂ} {r : ℝ} (h : Admissible a r) :
    0 < maximumTerm a r := by
  obtain ⟨n, hn⟩ := h.2.2
  exact (term_pos h.1 hn).trans_le (term_le_maximumTerm h n)

theorem centralIndex_unique {a : ℕ → ℂ} {r : ℝ} {n m : ℕ}
    (hn : IsCentralIndex a r n) (hm : IsCentralIndex a r m) : n = m := by
  have heq : term a r n = term a r m := le_antisymm (hm.1 n) (hn.1 m)
  exact le_antisymm (hm.2 n heq) (hn.2 m heq.symm)

theorem coefficient_bound {a : ℕ → ℂ} {r : ℝ} (h : Admissible a r) (n : ℕ) :
    ‖a n‖ ≤ maximumTerm a r / r ^ n := by
  exact (le_div_iff₀ (pow_pos h.1 n)).mpr (term_le_maximumTerm h n)

theorem admissible_of_summable {a : ℕ → ℂ} {r : ℝ} (hr : 0 < r)
    (h : Summable (term a r)) (ha : ∃ n, a n ≠ 0) : Admissible a r :=
  ⟨hr, h.tendsto_atTop_zero, ha⟩

theorem term_change_radius (a : ℕ → ℂ) {r : ℝ} (hr : r ≠ 0) (s : ℝ) (n : ℕ) :
    term a s n = term a r n * (s / r) ^ n := by
  unfold term
  rw [div_pow]
  field_simp

/-- Increasing the radius cannot move a maximizing index to the left. -/
theorem centralIndex_le_of_lt {a : ℕ → ℂ} {r s : ℝ}
    (hr : Admissible a r) (hs : Admissible a s) (hrs : r < s) :
    centralIndex a r ≤ centralIndex a s := by
  by_contra h
  have hij : centralIndex a s < centralIndex a r := lt_of_not_ge h
  have hq : 1 < s / r := (one_lt_div hr.1).mpr hrs
  have hp : (s / r) ^ centralIndex a s < (s / r) ^ centralIndex a r :=
    pow_lt_pow_right₀ hq hij
  have hterm := term_le_maximumTerm hs (centralIndex a r)
  have hsmall := term_le_maximumTerm hr (centralIndex a s)
  have hpos := maximumTerm_pos hr
  have hstrict : term a s (centralIndex a s) < term a s (centralIndex a r) := by
    rw [term_change_radius a (ne_of_gt hr.1) s, term_change_radius a (ne_of_gt hr.1) s]
    calc
      term a r (centralIndex a s) * (s / r) ^ centralIndex a s
          ≤ term a r (centralIndex a r) * (s / r) ^ centralIndex a s :=
        mul_le_mul_of_nonneg_right hsmall (pow_nonneg (div_pos hs.1 hr.1).le _)
      _ < term a r (centralIndex a r) * (s / r) ^ centralIndex a r :=
        mul_lt_mul_of_pos_left hp hpos
  exact (not_lt_of_ge hterm) hstrict

theorem centralIndex_le {a : ℕ → ℂ} {r s : ℝ}
    (hr : Admissible a r) (hs : Admissible a s) (hrs : r ≤ s) :
    centralIndex a r ≤ centralIndex a s := by
  rcases lt_or_eq_of_le hrs with hlt | rfl
  · exact centralIndex_le_of_lt hr hs hlt
  · exact le_rfl

theorem maximumTerm_le {a : ℕ → ℂ} {r s : ℝ}
    (hr : Admissible a r) (hs : Admissible a s) (hrs : r ≤ s) :
    maximumTerm a r ≤ maximumTerm a s := by
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr.1.le hrs _) (norm_nonneg _)).trans
    (term_le_maximumTerm hs (centralIndex a r))

/-- Taylor coefficients at the origin, with the usual factorial normalization. -/
def taylorCoeff (f : ℂ → ℂ) (n : ℕ) : ℂ :=
  (n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0

theorem hasSum_taylorCoeff {f : ℂ → ℂ} (hf : Differentiable ℂ f) (z : ℂ) :
    HasSum (fun n => taylorCoeff f n * z ^ n) (f z) := by
  apply (Complex.hasSum_taylorSeries_of_entire hf 0 z).congr
  intro n
  simp only [taylorCoeff, sub_zero, smul_eq_mul, mul_comm, mul_left_comm]

theorem taylor_terms_tendsto_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {r : ℝ} (hr : 0 ≤ r) : Tendsto (term (taylorCoeff f) r) atTop (𝓝 0) := by
  have h := (hasSum_taylorCoeff hf (r : ℂ)).summable.tendsto_atTop_zero.norm
  change Tendsto (fun n => ‖taylorCoeff f n‖ * r ^ n) atTop (𝓝 0)
  simpa only [term, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hr, norm_zero] using h

theorem exists_taylorCoeff_ne_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hne : f ≠ 0) :
    ∃ n, taylorCoeff f n ≠ 0 := by
  by_contra h
  push Not at h
  apply hne
  funext z
  have hs := (hasSum_taylorCoeff hf z).tsum_eq
  simpa only [h, zero_mul, tsum_zero, Pi.zero_apply] using hs.symm

/-- The maximum term and central index really exist for each nonzero entire function. -/
theorem taylor_admissible {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hne : f ≠ 0)
    {r : ℝ} (hr : 0 < r) : Admissible (taylorCoeff f) r :=
  ⟨hr, taylor_terms_tendsto_zero hf hr.le, exists_taylorCoeff_ne_zero hf hne⟩

theorem taylor_centralIndex_monotone {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hne : f ≠ 0) :
    MonotoneOn (centralIndex (taylorCoeff f)) (Set.Ioi 0) := by
  intro r hr s hs hrs
  exact centralIndex_le (taylor_admissible hf hne hr) (taylor_admissible hf hne hs) hrs

/-- A higher nonzero coefficient eventually dominates every index up to `N`. -/
theorem centralIndex_gt_of_coefficient_bound {a : ℕ → ℂ} {r C : ℝ} {N m : ℕ}
    (hr : Admissible a r) (h1 : 1 ≤ r) (hm : N < m)
    (hC : ∀ n ≤ N, ‖a n‖ ≤ C) (hlarge : C < ‖a m‖ * r) :
    N < centralIndex a r := by
  by_contra h
  have hn : centralIndex a r ≤ N := le_of_not_gt h
  have hlow : maximumTerm a r ≤ C * r ^ N := by
    calc
      maximumTerm a r = ‖a (centralIndex a r)‖ * r ^ centralIndex a r := rfl
      _ ≤ ‖a (centralIndex a r)‖ * r ^ N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 hn) (norm_nonneg _)
      _ ≤ C * r ^ N := mul_le_mul_of_nonneg_right (hC _ hn) (pow_pos hr.1 _).le
  have hhigh : C * r ^ N < term a r m := by
    calc
      C * r ^ N < (‖a m‖ * r) * r ^ N :=
        mul_lt_mul_of_pos_right hlarge (pow_pos hr.1 _)
      _ = ‖a m‖ * r ^ (N + 1) := by rw [pow_succ]; ring
      _ ≤ term a r m := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ h1 (Nat.succ_le_of_lt hm)) (norm_nonneg _)
  exact (not_lt_of_ge ((term_le_maximumTerm hr m).trans hlow)) hhigh

/-- Infinite support forces the central index to tend to infinity. -/
theorem centralIndex_tendsto_atTop {a : ℕ → ℂ}
    (ha : ∀ r > 0, Admissible a r) (hsupport : ∀ N, ∃ m > N, a m ≠ 0) :
    Tendsto (centralIndex a) atTop atTop := by
  classical
  refine tendsto_atTop.2 fun N => ?_
  obtain ⟨m, hm, ham⟩ := hsupport N
  obtain ⟨j, _, hj⟩ := (Finset.range (N + 1)).exists_max_image (fun n => ‖a n‖)
    ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ N)⟩
  have hC : ∀ n ≤ N, ‖a n‖ ≤ ‖a j‖ := by
    intro n hn
    exact hj n (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))
  let R := max 1 ((‖a j‖ + 1) / ‖a m‖)
  filter_upwards [eventually_ge_atTop R] with r hr
  have h1 : 1 ≤ r := (le_max_left _ _).trans hr
  have hrpos : 0 < r := zero_lt_one.trans_le h1
  have hnorm : 0 < ‖a m‖ := norm_pos_iff.mpr ham
  have hlarge : ‖a j‖ < ‖a m‖ * r := by
    have hdiv : (‖a j‖ + 1) / ‖a m‖ ≤ r := (le_max_right _ _).trans hr
    have hprod := (div_le_iff₀ hnorm).mp hdiv
    nlinarith
  exact (centralIndex_gt_of_coefficient_bound (ha r hrpos) h1 hm hC hlarge).le

/-- A nonpolynomial entire function has nonzero Taylor coefficients at arbitrarily high indices. -/
theorem taylor_support_unbounded {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnp : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z) :
    ∀ N, ∃ m > N, taylorCoeff f m ≠ 0 := by
  classical
  intro N
  by_contra h
  push Not at h
  let p : Polynomial ℂ := ∑ n ∈ Finset.range (N + 1),
    Polynomial.monomial n (taylorCoeff f n)
  apply hnp
  refine ⟨p, fun z => ?_⟩
  calc
    f z = ∑' n, taylorCoeff f n * z ^ n := (hasSum_taylorCoeff hf z).tsum_eq.symm
    _ = ∑ n ∈ Finset.range (N + 1), taylorCoeff f n * z ^ n := by
      apply tsum_eq_sum
      intro n hn
      have hn' : N < n := Nat.lt_of_succ_le (by simpa only [Finset.mem_range, not_lt] using hn)
      rw [h n hn', zero_mul]
    _ = p.eval z := by simp [p, Polynomial.eval_finsetSum, Polynomial.eval_monomial]

/-- Central indices of transcendental entire functions tend to infinity. -/
theorem taylor_centralIndex_tendsto_atTop {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnp : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z) :
    Tendsto (centralIndex (taylorCoeff f)) atTop atTop := by
  have hne : f ≠ 0 := by
    intro h
    exact hnp ⟨0, by simp [h]⟩
  exact centralIndex_tendsto_atTop (fun _ hr => taylor_admissible hf hne hr)
    (taylor_support_unbounded hf hnp)

/-- Cauchy's estimate controls every weighted Taylor coefficient by a circle bound. -/
theorem taylor_term_le_circle_bound {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {r M : ℝ} (hr : 0 < r) (hb : ∀ z ∈ Metric.sphere (0 : ℂ) r, ‖f z‖ ≤ M)
    (n : ℕ) : term (taylorCoeff f) r n ≤ M := by
  have hd := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr
    hf.diffContOnCl hb
  have hn : (0 : ℝ) < n.factorial := by positivity
  have hrn : 0 < r ^ n := pow_pos hr _
  have hcoeff : ‖taylorCoeff f n‖ = (n.factorial : ℝ)⁻¹ * ‖iteratedDeriv n f 0‖ := by
    simp [taylorCoeff]
  unfold term
  rw [hcoeff]
  calc
    (n.factorial : ℝ)⁻¹ * ‖iteratedDeriv n f 0‖ * r ^ n
        ≤ (n.factorial : ℝ)⁻¹ * ((n.factorial : ℝ) * M / r ^ n) * r ^ n := by
      gcongr
    _ = M := by field_simp

/-- The maximum term is at most any upper bound for the maximum modulus. -/
theorem maximumTerm_le_circle_bound {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {r M : ℝ} (hr : 0 < r) (hb : ∀ z ∈ Metric.sphere (0 : ℂ) r, ‖f z‖ ≤ M) :
    maximumTerm (taylorCoeff f) r ≤ M :=
  taylor_term_le_circle_bound hf hr hb _

#print axioms term_nonneg
#print axioms term_pos
#print axioms exists_last_maximum
#print axioms exists_centralIndex
#print axioms centralIndex_spec
#print axioms term_le_maximumTerm
#print axioms maximumTerm_pos
#print axioms centralIndex_unique
#print axioms coefficient_bound
#print axioms admissible_of_summable
#print axioms term_change_radius
#print axioms centralIndex_le_of_lt
#print axioms centralIndex_le
#print axioms maximumTerm_le
#print axioms hasSum_taylorCoeff
#print axioms taylor_terms_tendsto_zero
#print axioms exists_taylorCoeff_ne_zero
#print axioms taylor_admissible
#print axioms taylor_centralIndex_monotone
#print axioms centralIndex_gt_of_coefficient_bound
#print axioms centralIndex_tendsto_atTop
#print axioms taylor_support_unbounded
#print axioms taylor_centralIndex_tendsto_atTop
#print axioms taylor_term_le_circle_bound
#print axioms maximumTerm_le_circle_bound

end WimanValiron
