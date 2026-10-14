import WimanValironNormalRadii
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Wiman's bounded comparison sequence and coefficient decay

The sequence `exp (sum_{k < n} (k+1)^(-alpha))`, for `alpha > 1`, is
positive, strictly increasing and bounded. This is the comparison sequence
used in He Yuzan, Section 1.4, after Lemma 1.1. Its finite differences give
the quadratic-exponential coefficient bounds used before the moment estimates.

These coefficient estimates hold at actual normal radii. The finite
logarithmic measure of the complement is not established here.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace WimanValiron

/-- The logarithm of the comparison factor. -/
def comparisonLog (α : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, ((k + 1 : ℕ) : ℝ)^(-α)

/-- The bounded increasing comparison factors used in the coefficient method. -/
def comparisonSequence (α : ℝ) (n : ℕ) : ℝ := Real.exp (comparisonLog α n)

theorem comparisonSequence_pos (α : ℝ) (n : ℕ) : 0 < comparisonSequence α n :=
  Real.exp_pos _

theorem comparisonLog_succ (α : ℝ) (n : ℕ) :
    comparisonLog α (n+1) = comparisonLog α n + ((n+1 : ℕ) : ℝ)^(-α) := by
  exact Finset.sum_range_succ _ _

theorem comparisonSequence_strictMono (α : ℝ) : StrictMono (comparisonSequence α) := by
  apply strictMono_nat_of_lt_succ
  intro n
  apply Real.exp_lt_exp.mpr
  rw [comparisonLog_succ]
  exact lt_add_of_pos_right _ (Real.rpow_pos_of_pos (by positivity) _)

/-- The comparison factors are bounded because the defining p-series converges. -/
theorem comparisonSequence_bounded {α : ℝ} (hα : 1 < α) :
    ∃ P : ℝ, ∀ n, comparisonSequence α n ≤ P := by
  have hs : Summable (fun k : ℕ => ((k+1 : ℕ) : ℝ)^(-α)) := by
    exact (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by linarith))
  refine ⟨Real.exp (∑' k : ℕ, ((k+1 : ℕ) : ℝ)^(-α)), fun n => ?_⟩
  apply Real.exp_le_exp.mpr
  exact hs.sum_le_tsum (Finset.range n) (fun _ _ => Real.rpow_nonneg (by positivity) _)

/-- Exact finite increment of the logarithmic comparison factors. -/
theorem comparisonLog_add (α : ℝ) (N k : ℕ) :
    comparisonLog α (N+k) - comparisonLog α N =
      ∑ j ∈ Finset.range k, ((N+j+1 : ℕ) : ℝ)^(-α) := by
  unfold comparisonLog
  rw [Finset.sum_range_add, add_sub_cancel_left]

/-- A lower bound for every increment by its smallest summand. -/
theorem comparisonLog_increment_lower {α : ℝ} (hα : 0 ≤ α) (N j k : ℕ)
    (hjk : j ≤ k) :
    (j : ℝ) * ((N+k : ℕ) : ℝ)^(-α) ≤
      comparisonLog α (N+j) - comparisonLog α N := by
  rw [comparisonLog_add]
  calc
    _ = ∑ _l ∈ Finset.range j, ((N+k : ℕ) : ℝ)^(-α) := by simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro l hl
      apply Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (neg_nonpos.mpr hα)
      exact_mod_cast (show N+l+1 ≤ N+k by have := Finset.mem_range.mp hl; omega)

/-- The triangular sum in the exponent is quadratic in the distance from the
central index. -/
theorem sum_range_succ_real (k : ℕ) :
    (∑ j ∈ Finset.range k, ((j+1 : ℕ) : ℝ)) = (k : ℝ) * (k+1) / 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- The right comparison product has a quadratic-exponential upper bound. -/
theorem comparison_right_gaussian {α : ℝ} (hα : 0 ≤ α) (N k : ℕ) :
    comparisonSequence α N ^ k /
      (∏ j ∈ Finset.range k, comparisonSequence α (N+j+1)) ≤
        Real.exp (-((k : ℝ) * (k+1) / 2) * ((N+k : ℕ) : ℝ)^(-α)) := by
  by_cases hk : k = 0
  · subst k
    simp
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  have hsum : ((k : ℝ) * (k+1) / 2) * ((N+k : ℕ) : ℝ)^(-α) ≤
      ∑ j ∈ Finset.range k, (comparisonLog α (N+j+1) - comparisonLog α N) := by
    rw [← sum_range_succ_real, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j hj
    simpa only [Nat.add_assoc] using comparisonLog_increment_lower hα N (j+1) k
      (Nat.succ_le_of_lt (Finset.mem_range.mp hj))
  have heq : comparisonSequence α N ^ k /
      (∏ j ∈ Finset.range k, comparisonSequence α (N+j+1)) =
      Real.exp (-(∑ j ∈ Finset.range k, (comparisonLog α (N+j+1) - comparisonLog α N))) := by
    simp only [comparisonSequence, ← Real.exp_nat_mul, ← Real.exp_sum, ← Real.exp_sub]
    congr 1
    rw [Finset.sum_sub_distrib]
    simp
  rw [heq]
  exact Real.exp_le_exp.mpr (by nlinarith)

/-- The resulting actual Taylor-coefficient bound at a normal radius. -/
theorem normal_right_gaussian {a : ℕ → ℂ} {α r : ℝ} {N : ℕ}
    (hα : 0 ≤ α) (hN : NormalRadiusAt a (comparisonSequence α) r N)
    (haN : a N ≠ 0) (k : ℕ) :
    term a r (N+k) / term a r N ≤
      Real.exp (-((k : ℝ) * (k+1) / 2) * ((N+k : ℕ) : ℝ)^(-α)) :=
  (normal_right_coefficient_ratio (comparisonSequence_pos α) hN haN k).trans
    (comparison_right_gaussian hα N k)

/-- The left comparison product has a quadratic-exponential bound. The
central index is `n + k`; its adjacent left coefficient has exponent zero. -/
theorem comparison_left_gaussian {α : ℝ} (hα : 0 ≤ α) (n k : ℕ) :
    (∏ j ∈ Finset.range k, comparisonSequence α (n+j+1)) /
      comparisonSequence α (n+k) ^ k ≤
        Real.exp (-((k : ℝ) * (k-1) / 2) * ((n+k : ℕ) : ℝ)^(-α)) := by
  have hsum : ((k : ℝ) * (k-1) / 2) * ((n+k : ℕ) : ℝ)^(-α) ≤
      ∑ j ∈ Finset.range k, (comparisonLog α (n+k) - comparisonLog α (n+j+1)) := by
    calc
      _ = (∑ j ∈ Finset.range k, ((k : ℝ) - ((j+1 : ℕ) : ℝ))) *
          ((n+k : ℕ) : ℝ)^(-α) := by
        rw [Finset.sum_sub_distrib, sum_range_succ_real]
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
      _ = ∑ j ∈ Finset.range k,
          ((k : ℝ) - ((j+1 : ℕ) : ℝ)) * ((n+k : ℕ) : ℝ)^(-α) :=
        Finset.sum_mul _ _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro j hj
        have hjk : j+1 ≤ k := Nat.succ_le_of_lt (Finset.mem_range.mp hj)
        have heq : n+j+1+(k-(j+1)) = n+k := by omega
        have h := comparisonLog_increment_lower hα (n+j+1) (k-(j+1)) (k-(j+1))
          le_rfl
        rw [heq, Nat.cast_sub hjk] at h
        exact h
  have heq : (∏ j ∈ Finset.range k, comparisonSequence α (n+j+1)) /
      comparisonSequence α (n+k) ^ k =
      Real.exp (-(∑ j ∈ Finset.range k,
        (comparisonLog α (n+k) - comparisonLog α (n+j+1)))) := by
    simp only [comparisonSequence, ← Real.exp_nat_mul, ← Real.exp_sum, ← Real.exp_sub]
    congr 1
    rw [Finset.sum_sub_distrib]
    simp
  rw [heq]
  exact Real.exp_le_exp.mpr (by nlinarith)

/-- The actual Taylor-coefficient bound to the left of a normal central index. -/
theorem normal_left_gaussian {a : ℕ → ℂ} {α r : ℝ} {n k : ℕ}
    (hα : 0 ≤ α) (hN : NormalRadiusAt a (comparisonSequence α) r (n+k))
    (haN : a (n+k) ≠ 0) :
    term a r n / term a r (n+k) ≤
      Real.exp (-((k : ℝ) * (k-1) / 2) * ((n+k : ℕ) : ℝ)^(-α)) :=
  (normal_left_coefficient_ratio (comparisonSequence_pos α) hN haN).trans
    (comparison_left_gaussian hα n k)

end WimanValiron

#print axioms WimanValiron.comparisonSequence_pos
#print axioms WimanValiron.comparisonLog_succ
#print axioms WimanValiron.comparisonSequence_strictMono
#print axioms WimanValiron.comparisonSequence_bounded
#print axioms WimanValiron.comparisonLog_add
#print axioms WimanValiron.comparisonLog_increment_lower
#print axioms WimanValiron.sum_range_succ_real
#print axioms WimanValiron.comparison_right_gaussian
#print axioms WimanValiron.normal_right_gaussian
#print axioms WimanValiron.comparison_left_gaussian
#print axioms WimanValiron.normal_left_gaussian
