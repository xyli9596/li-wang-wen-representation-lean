import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic

/-!
# Cauchy transfer from a local monomial approximation

An actual uniform approximation on a circle around a nonzero point gives
quantitative derivative estimates at its center. This is the analytic
Cauchy-estimate step of a Wiman--Valiron argument. The uniform approximation
is an explicit hypothesis: this module does not construct it or its
exceptional set.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology

namespace WimanValiron

/-- The scaled derivatives of the normalized monomial are falling factorials,
including derivative orders above its degree. -/
theorem scaled_iteratedDeriv_normalized_monomial (N j : ℕ) {z : ℂ} (hz : z ≠ 0) :
    z ^ j * iteratedDeriv j (fun w : ℂ => (w / z) ^ N) z =
      (N.descFactorial j : ℂ) := by
  simp only [div_pow, iteratedDeriv_div_const, iteratedDeriv_pow]
  by_cases hj : j ≤ N
  · have hp : z ^ j * z ^ (N-j) = z ^ N := by
      rw [← pow_add, Nat.add_sub_of_le hj]
    calc
      z ^ j * ((N.descFactorial j : ℂ) * z ^ (N-j) / z ^ N) =
          (N.descFactorial j : ℂ) * (z ^ j * z ^ (N-j)) / z ^ N := by ring
      _ = (N.descFactorial j : ℂ) := by rw [hp]; field_simp
  · simp [Nat.descFactorial_eq_zero_iff_lt.mpr (Nat.lt_of_not_ge hj)]

/-- A uniform normalized monomial error on a circle controls every derivative
at its center. The radius is positive and both normalizing values are nonzero. -/
theorem cauchy_transfer_of_monomial_circle_bound {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {z : ℂ} (hz : z ≠ 0) (hfz : f z ≠ 0)
    {δ η : ℝ} (hδ : 0 < δ) (N j : ℕ)
    (herror : ∀ w ∈ Metric.sphere z δ, ‖f w / f z - (w / z) ^ N‖ ≤ η) :
    ‖z ^ j * iteratedDeriv j f z / f z - (N.descFactorial j : ℂ)‖ ≤
      (j.factorial : ℝ) * (‖z‖ / δ) ^ j * η := by
  have hη : 0 ≤ η := by
    have hs : z + (δ : ℂ) ∈ Metric.sphere z δ := by
      simp [abs_of_pos hδ]
    exact (norm_nonneg _).trans (herror _ hs)
  rcases j with _ | j
  · simpa [hfz] using hη
  · let g : ℂ → ℂ := fun w => f w / f z - (w / z) ^ N
    have hg : Differentiable ℂ g := by
      dsimp [g]
      exact (hf.div_const (f z)).sub ((differentiable_id.div_const z).pow N)
    have hderiv := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
      (j+1) hδ hg.diffContOnCl herror
    have heq : z ^ (j+1) * iteratedDeriv (j+1) g z =
        z ^ (j+1) * iteratedDeriv (j+1) f z / f z -
          (N.descFactorial (j+1) : ℂ) := by
      dsimp only [g]
      have hmono : ContDiffAt ℂ (j+1) (fun w : ℂ => (w/z)^N) z := by fun_prop
      rw [iteratedDeriv_fun_sub ((hf.div_const (f z)).contDiff.contDiffAt) hmono,
        iteratedDeriv_div_const, mul_sub,
        scaled_iteratedDeriv_normalized_monomial N (j+1) hz]
      ring
    rw [← heq, norm_mul, norm_pow]
    calc
      ‖z‖ ^ (j+1) * ‖iteratedDeriv (j+1) g z‖ ≤
          ‖z‖ ^ (j+1) * ((j+1).factorial * η / δ ^ (j+1)) :=
        mul_le_mul_of_nonneg_left hderiv (pow_nonneg (norm_nonneg _) _)
      _ = ((j+1).factorial : ℝ) * (‖z‖ / δ) ^ (j+1) * η := by
        rw [div_pow]
        ring

/-- Translation of the boundary hypothesis to increments centered at zero. -/
theorem cauchy_transfer_of_monomial_increment_bound {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {z : ℂ} (hz : z ≠ 0) (hfz : f z ≠ 0)
    {δ η : ℝ} (hδ : 0 < δ) (N j : ℕ)
    (herror : ∀ w : ℂ, ‖w‖ = δ →
      ‖f (z+w) / f z - (1+w/z) ^ N‖ ≤ η) :
    ‖z ^ j * iteratedDeriv j f z / f z - (N.descFactorial j : ℂ)‖ ≤
      (j.factorial : ℝ) * (‖z‖ / δ) ^ j * η := by
  apply cauchy_transfer_of_monomial_circle_bound hf hz hfz hδ N j
  intro w hw
  have hnorm : ‖w-z‖ = δ := by simpa [Metric.mem_sphere, dist_eq_norm] using hw
  have h := herror (w-z) hnorm
  have hmodel : 1 + (w-z)/z = w/z := by field_simp; ring
  simpa [hmodel] using h

end WimanValiron

#print axioms WimanValiron.scaled_iteratedDeriv_normalized_monomial
#print axioms WimanValiron.cauchy_transfer_of_monomial_circle_bound
#print axioms WimanValiron.cauchy_transfer_of_monomial_increment_bound
