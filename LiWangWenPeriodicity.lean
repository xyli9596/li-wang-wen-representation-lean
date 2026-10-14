import LiWangWenGrowth
import IncePeriodic

/-! The exact connection from the paper's equation to Ince's periodic setting.
No finite-dimensionality or existence of a Floquet basis is assumed here. -/
set_option autoImplicit false
noncomputable section
open Polynomial
namespace LiWangWen

def exponentialPeriod : ℂ := 2 * Real.pi * Complex.I

theorem exponentialPeriod_ne_zero : exponentialPeriod ≠ 0 := by
  simp [exponentialPeriod, Real.pi_ne_zero, Complex.I_ne_zero]

theorem coefficients_periodic {n : ℕ} (P : Fin (n+1) → Polynomial ℂ) (j : Fin (n+1)) :
    Function.Periodic (fun z => (P j).eval (Complex.exp z)) exponentialPeriod := by
  intro z
  dsimp only [exponentialPeriod]
  rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

theorem paper_solves_translate {n : ℕ} {P : Fin (n+1) → Polynomial ℂ} {f : ℂ → ℂ}
    (hf : Solves P f) : Solves P (fun z => f (z+exponentialPeriod)) := by
  exact IncePeriodic.solves_translate (coefficients_periodic P) hf

theorem ExponentialBound.translate {f : ℂ → ℂ} (hf : ExponentialBound f) (h : ℂ) :
    ExponentialBound (fun z => f (z+h)) := by
  obtain ⟨A, B, hA, hB, hf⟩ := hf
  refine ⟨A * Real.exp (B*‖h‖), B, mul_nonneg hA (Real.exp_pos _).le, hB, ?_⟩
  intro z
  calc
    ‖f (z+h)‖ ≤ A * Real.exp (B*‖z+h‖) := hf (z+h)
    _ ≤ A * Real.exp (B*(‖z‖+‖h‖)) := by
      apply mul_le_mul_of_nonneg_left _ hA
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (norm_add_le _ _) hB)
    _ = (A * Real.exp (B*‖h‖)) * Real.exp (B*‖z‖) := by
      rw [mul_add, Real.exp_add]
      ring

#print axioms exponentialPeriod_ne_zero
#print axioms coefficients_periodic
#print axioms paper_solves_translate
#print axioms ExponentialBound.translate
end LiWangWen
