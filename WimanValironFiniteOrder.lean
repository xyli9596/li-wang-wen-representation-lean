import WimanValironLinearType
import LiWangWenFiniteOrderBounds

/-! Polynomial growth of the genuine central index follows directly from
finite order by comparing maximum terms at radii `r` and `2*r`. -/

noncomputable section
open Filter Set
open scoped Topology

namespace WimanValiron

/-- Finite order bounds the actual central index by a fixed monomial. -/
theorem centralIndex_polynomial_bound {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hne : f ≠ 0) (hfo : CRGOrder.FiniteOrder f) :
    ∃ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 1 ≤ r →
      (centralIndex (taylorCoeff f) r : ℝ) ≤ C*r^k := by
  obtain ⟨k,A,hA,hbound⟩ := LiWangWen.power_bound_of_finiteOrder hf hfo
  let μ := maximumTerm (taylorCoeff f) 1
  have hμ : 0 < μ := maximumTerm_pos (taylor_admissible hf hne zero_lt_one)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let C := (A*3^k+|Real.log μ|)/Real.log 2
  refine ⟨k,C,by dsimp [C]; positivity,fun r hr => ?_⟩
  have hrpos : 0 < r := zero_lt_one.trans_le hr
  have ha := taylor_admissible hf hne hrpos
  have ha2 := taylor_admissible hf hne (show 0 < 2*r by positivity)
  obtain ⟨z,hzn,hzM⟩ := exists_norm_eq_circleMaximum hf.continuous (show 0 ≤ 2*r by positivity)
  have hzr : ‖z‖ = 2*r := by simpa only [Metric.mem_sphere, dist_zero_right] using hzn
  have hμr : μ ≤ maximumTerm (taylorCoeff f) r :=
    maximumTerm_le (taylor_admissible hf hne zero_lt_one) ha hr
  have hexp : Real.exp (Real.log μ + (centralIndex (taylorCoeff f) r : ℝ)*Real.log 2)
      ≤ Real.exp (A*(1+2*r)^k) := by
    calc
      _ = μ*(2 : ℝ)^centralIndex (taylorCoeff f) r := by
        rw [Real.exp_add, Real.exp_log hμ, Real.exp_nat_mul,
          Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ ≤ maximumTerm (taylorCoeff f) r * (2 : ℝ)^centralIndex (taylorCoeff f) r :=
        mul_le_mul_of_nonneg_right hμr (by positivity)
      _ ≤ maximumTerm (taylorCoeff f) (2*r) := by
        simpa [hrpos.ne'] using maximumTerm_ge_radius_ratio ha ha2
      _ ≤ circleMaximum f (2*r) := maximumTerm_le_circleMaximum hf (by positivity)
      _ = ‖f z‖ := hzM.symm
      _ ≤ Real.exp (A*(1+2*r)^k) := by simpa only [hzr] using hbound z
  have hN := Real.exp_le_exp.mp hexp
  have hp : (1+2*r)^k ≤ 3^k*r^k := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) k
  have hrk : 1 ≤ r^k := one_le_pow₀ hr
  have hlogμ : -Real.log μ ≤ |Real.log μ| * r^k :=
    (neg_le_abs _).trans (le_mul_of_one_le_right (abs_nonneg _) hrk)
  have hN' : (centralIndex (taylorCoeff f) r : ℝ)*Real.log 2 ≤
      (A*3^k+|Real.log μ|)*r^k := by
    nlinarith [mul_le_mul_of_nonneg_left hp hA]
  dsimp [C]
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ hlog).mpr hN'

/-- The constant can be absorbed in one additional integer power. -/
theorem centralIndex_eventually_le_power {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hne : f ≠ 0) (hfo : CRGOrder.FiniteOrder f) :
    ∃ k : ℕ, 1 ≤ k ∧ ∀ᶠ r : ℝ in atTop,
      (centralIndex (taylorCoeff f) r : ℝ) ≤ r^k := by
  obtain ⟨k,C,hC,hbound⟩ := centralIndex_polynomial_bound hf hne hfo
  refine ⟨k+1,by omega,?_⟩
  filter_upwards [eventually_ge_atTop (max 1 C)] with r hr
  have hr1 : 1 ≤ r := (le_max_left _ _).trans hr
  calc
    (centralIndex (taylorCoeff f) r : ℝ) ≤ C*r^k := hbound r hr1
    _ ≤ r*r^k := mul_le_mul_of_nonneg_right ((le_max_right _ _).trans hr) (by positivity)
    _ = r^(k+1) := by ring

#print axioms centralIndex_polynomial_bound
#print axioms centralIndex_eventually_le_power
end WimanValiron
