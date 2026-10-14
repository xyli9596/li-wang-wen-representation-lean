import LiWangWenFourier
import LiWangWenFiniteOrderBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Factorial decay of Fourier coefficients of finite-order periodic functions

Moving the contour a logarithmic distance proves decay faster than every
factorial power. No exponential-type assumption is used.
-/

noncomputable section
open Filter Set
open scoped Topology

namespace LiWangWen

theorem eventually_log_power_le_nat (A L B : ℝ) (hA : 0 ≤ A)
    (hL : 0 ≤ L) (hB : 0 ≤ B) (k : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      A*(1+L*Real.log ((n : ℝ)+1)+B)^k ≤ (n : ℝ) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hlo := (isLittleO_log_rpow_rpow_atTop (k : ℝ) zero_lt_one).const_mul_left
    (A*(1+L+B)^k)
  have hb := (hlo.bound (show (0 : ℝ) < 1/2 by norm_num)).filter_mono
    (show Filter.map (fun n : ℕ => (n : ℝ)+1) atTop ≤ atTop from ht)
  filter_upwards [hb, (Real.tendsto_log_atTop.comp ht).eventually_ge_atTop 1,
    eventually_ge_atTop (1 : ℕ)] with n hn hlog hn1
  change 1 ≤ Real.log ((n : ℝ)+1) at hlog
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  change ‖A*(1+L+B)^k * Real.log ((n : ℝ)+1)^(k : ℝ)‖ ≤
    (1/2)*‖((n : ℝ)+1)^(1 : ℝ)‖ at hn
  simp only [Real.rpow_natCast, Real.rpow_one, Real.norm_eq_abs] at hn
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)] at hn
  have hbase : 1+L*Real.log ((n : ℝ)+1)+B ≤
      (1+L+B)*Real.log ((n : ℝ)+1) := by nlinarith
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1+L*Real.log ((n : ℝ)+1)+B) hbase k
  calc
    A*(1+L*Real.log ((n : ℝ)+1)+B)^k ≤
        A*((1+L+B)*Real.log ((n : ℝ)+1))^k := mul_le_mul_of_nonneg_left hp hA
    _ = A*(1+L+B)^k*Real.log ((n : ℝ)+1)^k := by rw [mul_pow]; ring
    _ ≤ (1/2)*((n : ℝ)+1) := hn
    _ ≤ n := by linarith

theorem factorial_pow_le_exp_log (n K : ℕ) :
    (n.factorial : ℝ)^K ≤ Real.exp ((K : ℝ)*(n : ℝ)*Real.log ((n : ℝ)+1)) := by
  have hf : (n.factorial : ℝ) ≤ ((n : ℝ)+1)^n := by
    have h := n.factorial_le_pow
    have h' : (n.factorial : ℝ) ≤ (n : ℝ)^n := by exact_mod_cast h
    exact h'.trans (pow_le_pow_left₀ (by positivity) (by linarith) _)
  apply (pow_le_pow_left₀ (by positivity) hf K).trans_eq
  rw [mul_assoc, Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log (by positivity)]

/-- A signed integer index of modulus `n` has superfactorial decay. -/
theorem verticalFourierCoeff_factorial_decay {p : ℂ → ℂ}
    (hp : Differentiable ℂ p) (hper : Function.Periodic p exponentialPeriod)
    (hfo : CRGOrder.FiniteOrder p) (m : ℕ → ℤ)
    (hm : ∀ n, |(m n : ℝ)| = (n : ℝ)) (K : ℕ) :
    Tendsto (fun n => (n.factorial : ℝ)^K * ‖verticalFourierCoeff p (m n)‖)
      atTop (𝓝 0) := by
  obtain ⟨k, A, hA, hbound⟩ := power_bound_of_finiteOrder hp hfo
  let L : ℝ := (K : ℝ)+2
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have ht : Tendsto (fun n : ℕ => (n : ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ n : ℕ in atTop,
      (n.factorial : ℝ)^K * ‖verticalFourierCoeff p (m n)‖ ≤ Real.exp (-(n : ℝ)) := by
    filter_upwards [eventually_log_power_le_nat A L (2*Real.pi) hA hL (by positivity) k,
      (Real.tendsto_log_atTop.comp ht).eventually_ge_atTop 1] with n hsmall hlog
    change 1 ≤ Real.log ((n : ℝ)+1) at hlog
    let y : ℝ := L*Real.log ((n : ℝ)+1)
    let x : ℝ := if 0 ≤ (m n : ℝ) then y else -y
    have hy : 0 ≤ y := mul_nonneg hL (by linarith)
    have hx : |x| = y := by
      dsimp only [x]
      split_ifs <;> simp [abs_of_nonneg hy]
    have hmx : (m n : ℝ)*x = (n : ℝ)*y := by
      rw [← hm n]
      dsimp only [x]
      split_ifs with h
      · rw [abs_of_nonneg h]
      · rw [abs_of_neg (lt_of_not_ge h)]; ring
    have hpoint (t : ℝ) (ht' : t ∈ Icc (0 : ℝ) (2*Real.pi)) :
        ‖p ((x : ℂ)+(t : ℂ)*Complex.I)‖ ≤ Real.exp (n : ℝ) := by
      apply (hbound _).trans
      apply Real.exp_le_exp.mpr
      have hz : ‖(x : ℂ)+(t : ℂ)*Complex.I‖ ≤ y+2*Real.pi := by
        calc
          _ ≤ ‖(x : ℂ)‖+‖(t : ℂ)*Complex.I‖ := norm_add_le _ _
          _ = |x|+|t| := by simp
          _ ≤ y+2*Real.pi := by rw [hx, abs_of_nonneg ht'.1]; linarith [ht'.2]
      exact (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (by linarith :
          1+‖(x : ℂ)+(t : ℂ)*Complex.I‖ ≤ 1+y+2*Real.pi) k) hA).trans hsmall
    have hc := norm_verticalFourierCoeff_le hp hper (m n) x (Real.exp (n : ℝ)) hpoint
    have hexp : -(m n : ℝ)*x+(n : ℝ) = (n : ℝ)-(n : ℝ)*y := by linarith [hmx]
    rw [← Real.exp_add, hexp] at hc
    calc
      (n.factorial : ℝ)^K * ‖verticalFourierCoeff p (m n)‖ ≤
          Real.exp ((K : ℝ)*(n : ℝ)*Real.log ((n : ℝ)+1)) *
            Real.exp ((n : ℝ)-(n : ℝ)*y) :=
        mul_le_mul (factorial_pow_le_exp_log n K) hc (norm_nonneg _) (Real.exp_pos _).le
      _ = Real.exp ((n : ℝ)-2*(n : ℝ)*Real.log ((n : ℝ)+1)) := by
        rw [← Real.exp_add]
        congr 1
        dsimp [y, L]
        ring
      _ ≤ Real.exp (-(n : ℝ)) := by
        apply Real.exp_le_exp.mpr
        nlinarith [show (0 : ℝ) ≤ n by positivity]
  apply squeeze_zero' (Eventually.of_forall (fun n => by positivity)) hevent
  exact Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop

theorem verticalFourierCoeff_factorial_decay_pos {p : ℂ → ℂ}
    (hp : Differentiable ℂ p) (hper : Function.Periodic p exponentialPeriod)
    (hfo : CRGOrder.FiniteOrder p) (K : ℕ) :
    Tendsto (fun n : ℕ => (n.factorial : ℝ)^K * ‖verticalFourierCoeff p n‖)
      atTop (𝓝 0) :=
  verticalFourierCoeff_factorial_decay hp hper hfo (fun n => n)
    (fun n => by simp) K

theorem verticalFourierCoeff_factorial_decay_neg {p : ℂ → ℂ}
    (hp : Differentiable ℂ p) (hper : Function.Periodic p exponentialPeriod)
    (hfo : CRGOrder.FiniteOrder p) (K : ℕ) :
    Tendsto (fun n : ℕ => (n.factorial : ℝ)^K * ‖verticalFourierCoeff p (-(n : ℤ))‖)
      atTop (𝓝 0) :=
  verticalFourierCoeff_factorial_decay hp hper hfo (fun n => -(n : ℤ))
    (fun n => by simp) K

#print axioms eventually_log_power_le_nat
#print axioms factorial_pow_le_exp_log
#print axioms verticalFourierCoeff_factorial_decay
#print axioms verticalFourierCoeff_factorial_decay_pos
#print axioms verticalFourierCoeff_factorial_decay_neg
end LiWangWen
