import LiWangWenGrowth
import CRGPolynomialGrowth

/-! A composition criterion needed in Lemma 5.2. Unlike the full lemma,
this module handles one entire coefficient without cancellation between terms. -/
set_option autoImplicit false
noncomputable section
open Polynomial Metric
namespace LiWangWen

theorem norm_log_le_of_one_le {w : ℂ} (hw : 1 ≤ ‖w‖) :
    ‖Complex.log w‖ ≤ Real.log ‖w‖ + Real.pi := by
  calc
    ‖Complex.log w‖ ≤ |(Complex.log w).re| + |(Complex.log w).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = Real.log ‖w‖ + |w.arg| := by
      rw [Complex.log_re, Complex.log_im, abs_of_nonneg (Real.log_nonneg hw)]
    _ ≤ Real.log ‖w‖ + Real.pi := add_le_add_right (Complex.abs_arg_le_pi w) _

/-- If an entire coefficient becomes a function of finite exponential type
after composition with exp, that coefficient is a polynomial. -/
theorem polynomial_of_exp_bound {u : ℂ → ℂ} (hu : Differentiable ℂ u)
    (hf : ExponentialBound (fun z => u (Complex.exp z))) :
    ∃ p : Polynomial ℂ, ∀ w, u w = p.eval w := by
  obtain ⟨A, B, hA, hB, hf⟩ := hf
  obtain ⟨N, hN⟩ := exists_nat_ge B
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    hu.continuous.continuousOn
  let K := A * Real.exp (B * Real.pi)
  have hK : 0 ≤ K := mul_nonneg hA (Real.exp_pos _).le
  let C := max M K
  have hC : 0 ≤ C := hK.trans (le_max_right _ _)
  apply CRGPolynomialGrowth.exists_polynomial_of_growth hu N hC
  intro w
  by_cases hw : 1 ≤ ‖w‖
  · have hwpos : 0 < ‖w‖ := lt_of_lt_of_le zero_lt_one hw
    have hwne : w ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hwpos)
    have hlog : 0 ≤ Real.log ‖w‖ := Real.log_nonneg hw
    have hcomp := hf (Complex.log w)
    dsimp only at hcomp
    rw [Complex.exp_log hwne] at hcomp
    calc
      ‖u w‖ ≤ A * Real.exp (B * ‖Complex.log w‖) := hcomp
      _ ≤ A * Real.exp (B * (Real.log ‖w‖ + Real.pi)) := by
        apply mul_le_mul_of_nonneg_left _ hA
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (norm_log_le_of_one_le hw) hB)
      _ = K * Real.exp (B * Real.log ‖w‖) := by
        dsimp [K]
        rw [mul_add, Real.exp_add]
        ring
      _ ≤ K * Real.exp ((N:ℝ) * Real.log ‖w‖) := by
        apply mul_le_mul_of_nonneg_left _ hK
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hN hlog)
      _ = K * ‖w‖^N := by rw [Real.exp_nat_mul, Real.exp_log hwpos]
      _ ≤ C * (1+‖w‖)^N := mul_le_mul (le_max_right M K)
        (pow_le_pow_left₀ (norm_nonneg _) (by linarith) N) (by positivity) hC
  · have hmem : w ∈ closedBall (0 : ℂ) 1 := by
      simpa only [mem_closedBall, dist_zero_right] using (le_of_lt (lt_of_not_ge hw))
    calc
      ‖u w‖ ≤ M := hM w hmem
      _ ≤ C := le_max_left _ _
      _ ≤ C * (1+‖w‖)^N := by
        exact le_mul_of_one_le_right hC (one_le_pow₀ (by linarith [norm_nonneg w]))

#print axioms norm_log_le_of_one_le
#print axioms polynomial_of_exp_bound
end LiWangWen
