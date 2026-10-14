import WimanValironMaximumTerm
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Comparing an entire function with its maximum term

Taylor coefficients bounded at an outer radius give a geometric majorant
inside that circle. These are elementary estimates used before the
Wiman--Valiron derivative asymptotic theorem.
-/

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace WimanValiron

theorem norm_powerSeries_term_le_geometric {a : ℕ → ℂ} {s : ℝ}
    (hs : Admissible a s) (z : ℂ) (n : ℕ) :
    ‖a n * z ^ n‖ ≤ maximumTerm a s * (‖z‖ / s) ^ n := by
  rw [norm_mul, norm_pow]
  calc
    ‖a n‖ * ‖z‖ ^ n = term a s n * (‖z‖ / s) ^ n :=
      term_change_radius a (ne_of_gt hs.1) ‖z‖ n
    _ ≤ maximumTerm a s * (‖z‖ / s) ^ n :=
      mul_le_mul_of_nonneg_right (term_le_maximumTerm hs n)
        (pow_nonneg (div_nonneg (norm_nonneg _) hs.1.le) _)

/-- The geometric-series comparison `|f(z)| ≤ μ(s) / (1 - |z|/s)`. -/
theorem norm_le_maximumTerm_div {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hne : f ≠ 0)
    {s : ℝ} {z : ℂ} (hz : ‖z‖ < s) :
    ‖f z‖ ≤ maximumTerm (taylorCoeff f) s / (1 - ‖z‖ / s) := by
  have hs : 0 < s := (norm_nonneg z).trans_lt hz
  have hq0 : 0 ≤ ‖z‖ / s := div_nonneg (norm_nonneg _) hs.le
  have hq1 : ‖z‖ / s < 1 := (div_lt_one hs).mpr hz
  have hsum := (hasSum_geometric_of_lt_one hq0 hq1).mul_left
    (maximumTerm (taylorCoeff f) s)
  have hbound := (hasSum_taylorCoeff hf z).norm_le_of_bounded hsum
    (norm_powerSeries_term_le_geometric (taylor_admissible hf hne hs) z)
  simpa only [div_eq_mul_inv] using hbound

/-- A uniform bound on an inner circle in terms of the outer maximum term. -/
theorem norm_le_maximumTerm_div_on_circle {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hne : f ≠ 0) {r s : ℝ} (hrs : r < s)
    {z : ℂ} (hz : z ∈ Metric.sphere (0 : ℂ) r) :
    ‖f z‖ ≤ maximumTerm (taylorCoeff f) s / (1 - r / s) := by
  have hnorm : ‖z‖ = r := by simpa only [Metric.mem_sphere, dist_zero_right] using hz
  have hbound := norm_le_maximumTerm_div hf hne (hnorm ▸ hrs)
  rw [hnorm] at hbound
  exact hbound

/-- Differentiation shifts Taylor coefficients and multiplies by a falling factorial. -/
theorem taylorCoeff_iteratedDeriv (f : ℂ → ℂ) (j n : ℕ) :
    taylorCoeff (iteratedDeriv j f) n =
      ((n + j).descFactorial j : ℂ) * taylorCoeff f (n + j) := by
  have hi : iteratedDeriv n (iteratedDeriv j f) = iteratedDeriv (n + j) f := by
    simp only [iteratedDeriv_eq_iterate, Function.iterate_add_apply]
  have hfac : (n.factorial : ℂ) * ((n + j).descFactorial j : ℂ) =
      ((n + j).factorial : ℂ) := by
    have h := Nat.factorial_mul_descFactorial (Nat.le_add_left j n)
    simpa only [Nat.add_sub_cancel_right, Nat.cast_mul] using congrArg (Nat.cast : ℕ → ℂ) h
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hnj : ((n + j).factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n + j)
  unfold taylorCoeff
  rw [hi]
  field_simp
  linear_combination -(iteratedDeriv (n + j) f 0) * hfac

/-- The Taylor expansion of an arbitrary iterated derivative of an entire function. -/
theorem hasSum_iteratedDeriv_taylorCoeff {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (j : ℕ) (z : ℂ) :
    HasSum (fun n => ((n + j).descFactorial j : ℂ) * taylorCoeff f (n + j) * z ^ n)
      (iteratedDeriv j f z) := by
  have hd : Differentiable ℂ (iteratedDeriv j f) :=
    hf.contDiff.differentiable_iteratedDeriv' j
  simpa only [taylorCoeff_iteratedDeriv] using hasSum_taylorCoeff hd z

/-- The exact coefficient identity underlying the Wiman--Valiron derivative estimates. -/
theorem hasSum_pow_mul_iteratedDeriv {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (j : ℕ) (z : ℂ) :
    HasSum (fun n => (n.descFactorial j : ℂ) * taylorCoeff f n * z ^ n)
      (z ^ j * iteratedDeriv j f z) := by
  have hs := (hasSum_iteratedDeriv_taylorCoeff hf j z).mul_left (z ^ j)
  have ht : HasSum
      (fun n => ((n + j).descFactorial j : ℂ) * taylorCoeff f (n + j) * z ^ (n + j))
      (z ^ j * iteratedDeriv j f z) := by
    apply hs.congr
    intro s
    apply Finset.sum_congr rfl
    intro n _
    dsimp only
    rw [pow_add]
    ring
  have hzero : ∑ n ∈ Finset.range j,
      (n.descFactorial j : ℂ) * taylorCoeff f n * z ^ n = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    simp only [Nat.descFactorial_of_lt (Finset.mem_range.mp hn), Nat.cast_zero, zero_mul]
  have hfull := (hasSum_nat_add_iff
    (f := fun n => (n.descFactorial j : ℂ) * taylorCoeff f n * z ^ n) j).mp ht
  simpa only [hzero, add_zero] using hfull

#print axioms norm_powerSeries_term_le_geometric
#print axioms norm_le_maximumTerm_div
#print axioms norm_le_maximumTerm_div_on_circle
#print axioms taylorCoeff_iteratedDeriv
#print axioms hasSum_iteratedDeriv_taylorCoeff
#print axioms hasSum_pow_mul_iteratedDeriv

end WimanValiron
