import WimanValironMaximumTerm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Coefficient comparisons at Wiman normal radii

This is the coefficient-comparison part of He Yuzan, Chapter 1, Lemma 1.1,
printed pp. 23--24. A normal radius is defined by an actual central-index
condition for the weighted coefficients, not by the inequalities to be proved.
The assertion that the complement of these radii has finite logarithmic measure
is not proved in this module.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace WimanValiron

/-- The finite comparison weight `p₁ ⋯ pₙ`. -/
def comparisonWeight (p : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∏ j ∈ Finset.range n, p (j + 1)

/-- The coefficients of Wiman's auxiliary power series. -/
def comparisonCoeff (a : ℕ → ℂ) (p : ℕ → ℝ) (n : ℕ) : ℂ :=
  a n * (comparisonWeight p n : ℂ)

/-- A radius selected by the central index of the actual auxiliary coefficients. -/
def NormalRadiusAt (a : ℕ → ℂ) (p : ℕ → ℝ) (r : ℝ) (N : ℕ) : Prop :=
  0 < r ∧ IsCentralIndex (comparisonCoeff a p) (r / p N) N

theorem comparisonWeight_pos {p : ℕ → ℝ} (hp : ∀ j, 0 < p j) (n : ℕ) :
    0 < comparisonWeight p n := by
  exact Finset.prod_pos (fun j _ => hp (j + 1))

theorem comparisonWeight_add (p : ℕ → ℝ) (n k : ℕ) :
    comparisonWeight p (n + k) =
      comparisonWeight p n * ∏ j ∈ Finset.range k, p (n + j + 1) := by
  unfold comparisonWeight
  rw [Finset.prod_range_add]

/-- Bounded positive comparison factors give at most an exponential coefficient weight. -/
theorem comparisonWeight_le_pow {p : ℕ → ℝ} {P : ℝ}
    (hp : ∀ j, 0 < p j) (hP : ∀ j, p j ≤ P) (n : ℕ) :
    comparisonWeight p n ≤ P ^ n := by
  unfold comparisonWeight
  calc
    _ ≤ ∏ _j ∈ Finset.range n, P :=
      Finset.prod_le_prod (fun j _ => (hp _).le) (fun j _ => hP _)
    _ = _ := by simp

/-- Multiplying an entire coefficient sequence by bounded comparison weights
preserves admissibility at every positive radius. -/
theorem comparison_admissible {a : ℕ → ℂ} {p : ℕ → ℝ} {P : ℝ}
    (ha : ∀ r > 0, Admissible a r)
    (hp : ∀ j, 0 < p j) (hP : ∀ j, p j ≤ P) {r : ℝ} (hr : 0 < r) :
    Admissible (comparisonCoeff a p) r := by
  have hPpos : 0 < P := (hp 0).trans_le (hP 0)
  have houter := ha (P * r) (mul_pos hPpos hr)
  have hbound : ∀ n, term (comparisonCoeff a p) r n ≤ term a (P * r) n := by
    intro n
    simp only [term, comparisonCoeff, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (comparisonWeight_pos hp n), mul_pow]
    calc
      ‖a n‖ * comparisonWeight p n * r ^ n ≤ ‖a n‖ * P ^ n * r ^ n := by
        gcongr
        exact comparisonWeight_le_pow hp hP n
      _ = ‖a n‖ * (P ^ n * r ^ n) := by ring
  refine ⟨hr, squeeze_zero (fun n => term_nonneg _ hr.le n) hbound houter.2.1, ?_⟩
  obtain ⟨n, hn⟩ := houter.2.2
  refine ⟨n, mul_ne_zero hn ?_⟩
  exact_mod_cast (ne_of_gt (comparisonWeight_pos hp n))

/-- At a normal radius a nonzero coefficient sequence has a nonzero central coefficient. -/
theorem normal_coefficient_ne_zero {a : ℕ → ℂ} {p : ℕ → ℝ} {r : ℝ} {N : ℕ}
    (hp : ∀ j, 0 < p j) (hN : NormalRadiusAt a p r N)
    (ha : ∃ m, a m ≠ 0) : a N ≠ 0 := by
  obtain ⟨m, hm⟩ := ha
  have hcm : comparisonCoeff a p m ≠ 0 := by
    apply mul_ne_zero hm
    exact_mod_cast (ne_of_gt (comparisonWeight_pos hp m))
  have hpos := (term_pos (div_pos hN.1 (hp N)) hcm).trans_le (hN.2.1 m)
  intro hz
  simp [term, comparisonCoeff, hz] at hpos

/-- A central index of the auxiliary series produces an actual normal radius. -/
theorem normalRadiusAt_scaled {a : ℕ → ℂ} {p : ℕ → ℝ} {t : ℝ} {N : ℕ}
    (ht : 0 < t) (hp : 0 < p N)
    (hN : IsCentralIndex (comparisonCoeff a p) t N) :
    NormalRadiusAt a p (t * p N) N := by
  refine ⟨mul_pos ht hp, ?_⟩
  simpa only [mul_div_cancel_right₀ _ (ne_of_gt hp)] using hN

/-- The comparison construction yields normal radii for every positive
auxiliary radius, without assuming the coefficient comparison as input. -/
theorem exists_normal_radius {a : ℕ → ℂ} {p : ℕ → ℝ} {P t : ℝ}
    (ha : ∀ r > 0, Admissible a r)
    (hp : ∀ j, 0 < p j) (hP : ∀ j, p j ≤ P) (ht : 0 < t) :
    ∃ N, NormalRadiusAt a p (t * p N) N := by
  obtain ⟨N, hN⟩ := exists_centralIndex (comparison_admissible ha hp hP ht)
  exact ⟨N, normalRadiusAt_scaled ht (hp N) hN⟩

/-- Normal radii occur arbitrarily far out. The stronger assertion about their
exceptional complement is kept separate. -/
theorem exists_normal_radius_ge {a : ℕ → ℂ} {p : ℕ → ℝ} {P : ℝ}
    (ha : ∀ r > 0, Admissible a r)
    (hp : ∀ j, 0 < p j) (hmono : Monotone p) (hP : ∀ j, p j ≤ P) (R : ℝ) :
    ∃ r ≥ R, ∃ N, NormalRadiusAt a p r N := by
  let t := max 1 (R / p 0)
  have ht : 0 < t := zero_lt_one.trans_le (le_max_left _ _)
  obtain ⟨N, hN⟩ := exists_normal_radius ha hp hP ht
  refine ⟨t * p N, ?_, N, hN⟩
  have hRt : R ≤ t * p 0 := (div_le_iff₀ (hp 0)).mp (le_max_right _ _)
  exact hRt.trans (mul_le_mul_of_nonneg_left (hmono (Nat.zero_le N)) ht.le)

/-- Exact change of weights and radius. -/
theorem comparison_term {a : ℕ → ℂ} {p : ℕ → ℝ}
    (hp : ∀ j, 0 < p j) (r q : ℝ) (n : ℕ) :
    term (comparisonCoeff a p) (r / q) n =
      term a r n * comparisonWeight p n / q ^ n := by
  simp only [term, comparisonCoeff, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (comparisonWeight_pos hp n), div_pow]
  ring

/-- The common coefficient estimate from which both sides of (1.4.1) follow. -/
theorem normal_coefficient_ratio {a : ℕ → ℂ} {p : ℕ → ℝ} {r : ℝ} {N : ℕ}
    (hp : ∀ j, 0 < p j) (hN : NormalRadiusAt a p r N) (haN : a N ≠ 0)
    (m : ℕ) :
    term a r m / term a r N ≤
      (comparisonWeight p N / comparisonWeight p m) * ((p N) ^ m / (p N) ^ N) := by
  have hterm := hN.2.1 m
  rw [comparison_term hp r (p N), comparison_term hp r (p N)]
    at hterm
  have hpos : 0 < term a r N := term_pos hN.1 haN
  have hwm := comparisonWeight_pos hp m
  have hq := hp N
  have hden : 0 < term a r N * comparisonWeight p m / (p N) ^ m := by positivity
  calc
    term a r m / term a r N =
        (term a r m * comparisonWeight p m / (p N) ^ m) /
          (term a r N * comparisonWeight p m / (p N) ^ m) := by
      field_simp
    _ ≤ (term a r N * comparisonWeight p N / (p N) ^ N) /
          (term a r N * comparisonWeight p m / (p N) ^ m) :=
      div_le_div_of_nonneg_right hterm hden.le
    _ = (comparisonWeight p N / comparisonWeight p m) *
          ((p N) ^ m / (p N) ^ N) := by
      field_simp

/-- The left-hand coefficient comparison in He Yuzan (1.4.1), indexed without
truncated subtraction: the central index is `n + k`. -/
theorem normal_left_coefficient_ratio {a : ℕ → ℂ} {p : ℕ → ℝ} {r : ℝ} {n k : ℕ}
    (hp : ∀ j, 0 < p j) (hN : NormalRadiusAt a p r (n + k))
    (haN : a (n + k) ≠ 0) :
    term a r n / term a r (n + k) ≤
      (∏ j ∈ Finset.range k, p (n + j + 1)) / (p (n + k)) ^ k := by
  have h := normal_coefficient_ratio hp hN haN n
  rw [comparisonWeight_add, pow_add] at h
  have hw := comparisonWeight_pos hp n
  have hq := hp (n + k)
  convert h using 1
  field_simp

/-- The right-hand coefficient comparison in He Yuzan (1.4.1). -/
theorem normal_right_coefficient_ratio {a : ℕ → ℂ} {p : ℕ → ℝ} {r : ℝ} {N : ℕ}
    (hp : ∀ j, 0 < p j) (hN : NormalRadiusAt a p r N) (haN : a N ≠ 0)
    (k : ℕ) :
    term a r (N + k) / term a r N ≤
      (p N) ^ k / (∏ j ∈ Finset.range k, p (N + j + 1)) := by
  have h := normal_coefficient_ratio hp hN haN (N + k)
  rw [comparisonWeight_add, pow_add] at h
  have hw := comparisonWeight_pos hp N
  have hq := hp N
  have hprod : 0 < ∏ j ∈ Finset.range k, p (N + j + 1) :=
    Finset.prod_pos (fun j _ => hp _)
  convert h using 1
  field_simp

/-- Increasing comparison factors bound the left product by the central factor. -/
theorem left_comparison_product_le {p : ℕ → ℝ} (hp : ∀ j, 0 < p j)
    (hmono : Monotone p) (n k : ℕ) :
    (∏ j ∈ Finset.range k, p (n + j + 1)) ≤ (p (n + k)) ^ k := by
  calc
    _ ≤ ∏ _j ∈ Finset.range k, p (n + k) := by
      apply Finset.prod_le_prod
      · intro j _
        exact (hp _).le
      · intro j hj
        apply hmono
        have := Finset.mem_range.mp hj
        omega
    _ = _ := by simp

/-- Strictly increasing factors make every nonempty right product strictly larger. -/
theorem right_comparison_product_lt {p : ℕ → ℝ} (hp : ∀ j, 0 < p j)
    (hmono : StrictMono p) (N : ℕ) {k : ℕ} (hk : 0 < k) :
    (p N) ^ k < ∏ j ∈ Finset.range k, p (N + j + 1) := by
  calc
    _ = ∏ _j ∈ Finset.range k, p N := by simp
    _ < _ := by
      apply Finset.prod_lt_prod_of_nonempty
      · intro j _
        exact hp N
      · intro j _
        apply hmono
        omega
      · exact ⟨0, Finset.mem_range.mpr hk⟩

/-- The central index used to select a normal radius is also the original
power series' central index. -/
theorem normal_isCentralIndex {a : ℕ → ℂ} {p : ℕ → ℝ} {r : ℝ} {N : ℕ}
    (hp : ∀ j, 0 < p j) (hmono : StrictMono p)
    (hN : NormalRadiusAt a p r N) (haN : a N ≠ 0) :
    IsCentralIndex a r N := by
  have hpos : 0 < term a r N := term_pos hN.1 haN
  have hleft : ∀ m ≤ N, term a r m ≤ term a r N := by
    intro m hm
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    have hb := normal_left_coefficient_ratio hp hN haN
    have hpbound := left_comparison_product_le hp hmono.monotone m k
    have hratio : term a r m / term a r (m + k) ≤ 1 := by
      apply hb.trans
      exact (div_le_one (pow_pos (hp _) k)).mpr hpbound
    exact (div_le_one hpos).mp hratio
  have hright : ∀ m, N < m → term a r m < term a r N := by
    intro m hm
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm.le
    have hk : 0 < k := by omega
    have hb := normal_right_coefficient_ratio hp hN haN k
    have hpbound := right_comparison_product_lt hp hmono N hk
    have hprod : 0 < ∏ j ∈ Finset.range k, p (N + j + 1) :=
      Finset.prod_pos (fun j _ => hp _)
    have hratio : term a r (N + k) / term a r N < 1 :=
      hb.trans_lt ((div_lt_one hprod).mpr hpbound)
    exact (div_lt_one hpos).mp hratio
  constructor
  · intro m
    rcases le_or_gt m N with hm | hm
    · exact hleft m hm
    · exact (hright m hm).le
  · intro m hm
    by_contra hmn
    exact (hright m (lt_of_not_ge hmn)).ne hm

/-- The logarithmic length of a bad gap is independent of its common radial scale. -/
theorem log_scaled_gap {u v s : ℝ} (hu : 0 < u) (hv : 0 < v) (hs : 0 < s) :
    Real.log (s * v / (s * u)) = Real.log v - Real.log u := by
  rw [mul_div_mul_left _ _ (ne_of_gt hs), Real.log_div (ne_of_gt hv) (ne_of_gt hu)]

/-- Finite bad-gap logarithmic lengths telescope exactly. -/
theorem sum_log_gaps {q : ℕ → ℝ} (hq : ∀ n, 0 < q n) (N : ℕ) :
    ∑ n ∈ Finset.range N, Real.log (q (n + 1) / q n) =
      Real.log (q N) - Real.log (q 0) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Real.log_div (ne_of_gt (hq _)) (ne_of_gt (hq _))]
    ring

/-- A bounded nondecreasing sequence of comparison factors has summable bad-gap
logarithmic lengths. This proves the numerical telescoping estimate, independently
of the still-needed covering of all nonnormal radii by such gaps. -/
theorem summable_log_gaps {q : ℕ → ℝ} {P : ℝ}
    (hq : ∀ n, 0 < q n) (hmono : Monotone q) (hP : ∀ n, q n ≤ P) :
    Summable (fun n => Real.log (q (n + 1) / q n)) ∧
      (∑' n, Real.log (q (n + 1) / q n)) ≤ Real.log P - Real.log (q 0) := by
  have hn : ∀ n, 0 ≤ Real.log (q (n + 1) / q n) := by
    intro n
    apply Real.log_nonneg
    exact (one_le_div (hq n)).mpr (hmono (Nat.le_succ n))
  have hb : ∀ N, (∑ n ∈ Finset.range N, Real.log (q (n + 1) / q n)) ≤
      Real.log P - Real.log (q 0) := by
    intro N
    rw [sum_log_gaps hq]
    exact sub_le_sub_right (Real.log_le_log (hq N) (hP N)) _
  exact ⟨summable_of_sum_range_le hn hb, Real.tsum_le_of_sum_range_le hn hb⟩

#print axioms comparisonWeight_pos
#print axioms comparisonWeight_add
#print axioms comparison_term
#print axioms normal_coefficient_ratio
#print axioms normal_left_coefficient_ratio
#print axioms normal_right_coefficient_ratio

#print axioms left_comparison_product_le
#print axioms right_comparison_product_lt
#print axioms normal_isCentralIndex
#print axioms log_scaled_gap
#print axioms sum_log_gaps
#print axioms summable_log_gaps

#print axioms comparisonWeight_le_pow
#print axioms comparison_admissible
#print axioms normal_coefficient_ne_zero

#print axioms normalRadiusAt_scaled
#print axioms exists_normal_radius
#print axioms exists_normal_radius_ge

end WimanValiron
