import WimanValironGrowthBridge
import WimanValironTaylorMoments

/-!
# Two-sided central-index bounds suffice for order one and mean type

No convergence of the ratio `nu(r)/r` is needed. The lower bound follows by
comparing maximum terms at `r` and `2*r`; the upper bound uses the existing
growth bridge.
-/

noncomputable section
open Filter Set
open scoped Topology

namespace WimanValiron

theorem maximumTerm_ge_radius_ratio {a : ℕ → ℂ} {r s : ℝ}
    (hr : Admissible a r) (hs : Admissible a s) :
    maximumTerm a r * (s/r)^centralIndex a r ≤ maximumTerm a s := by
  change term a r (centralIndex a r) * (s/r)^centralIndex a r ≤ maximumTerm a s
  rw [← term_change_radius a hr.1.ne' s]
  exact term_le_maximumTerm hs _

theorem positiveType_of_centralIndex_eventually_ge {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hne : f ≠ 0) {c : ℝ} (hc : 0 < c)
    (hν : ∀ᶠ r : ℝ in atTop, c*r ≤ (centralIndex (taylorCoeff f) r : ℝ)) :
    ∃ b : ℝ, 0 < b ∧ ∀ R : ℝ, ∃ z : ℂ,
      max R 1 ≤ ‖z‖ ∧ Real.exp (b*‖z‖^(1 : ℝ)) ≤ ‖f z‖ := by
  let μ := maximumTerm (taylorCoeff f) 1
  have hμ : 0 < μ := maximumTerm_pos (taylor_admissible hf hne zero_lt_one)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let b := c*Real.log 2/4
  have hb : 0 < b := by dsimp [b]; positivity
  have hevent : ∀ᶠ r : ℝ in atTop,
      Real.exp (b*(2*r)) ≤ circleMaximum f (2*r) := by
    filter_upwards [hν, eventually_ge_atTop (1 : ℝ),
      eventually_ge_atTop (-(Real.log μ)/ (2*b))] with r hνr hr hlarge
    have hrp : 0 < r := zero_lt_one.trans_le hr
    have ha := taylor_admissible hf hne hrp
    have ha2 := taylor_admissible hf hne (show 0 < 2*r by positivity)
    have hμr : μ ≤ maximumTerm (taylorCoeff f) r :=
      maximumTerm_le (taylor_admissible hf hne zero_lt_one) ha hr
    have hpow : Real.exp (c*r*Real.log 2) ≤ (2 : ℝ)^centralIndex (taylorCoeff f) r := by
      rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      simpa only [Real.log_exp] using mul_le_mul_of_nonneg_right hνr hlog.le
    have hμexp : Real.exp (b*(2*r)) ≤ μ*Real.exp (c*r*Real.log 2) := by
      rw [← Real.exp_log hμ, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hmul := (div_le_iff₀ (by positivity : 0 < 2*b)).mp hlarge
      have hcb : c*Real.log 2 = 4*b := by dsimp [b]; ring
      rw [mul_right_comm c r (Real.log 2), hcb]
      linarith
    calc
      Real.exp (b*(2*r)) ≤ μ*Real.exp (c*r*Real.log 2) := hμexp
      _ ≤ maximumTerm (taylorCoeff f) r * (2 : ℝ)^centralIndex (taylorCoeff f) r :=
        mul_le_mul hμr hpow (Real.exp_pos _).le (maximumTerm_pos ha).le
      _ ≤ maximumTerm (taylorCoeff f) (2*r) := by
        simpa [hrp.ne'] using maximumTerm_ge_radius_ratio ha ha2
      _ ≤ circleMaximum f (2*r) := maximumTerm_le_circleMaximum hf (by positivity)
  obtain ⟨T,hT⟩ := eventually_atTop.mp hevent
  refine ⟨b,hb,fun R => ?_⟩
  let r := max T (max 1 R)
  have hr : 0 < r := zero_lt_one.trans_le ((le_max_left 1 R).trans (le_max_right T _))
  obtain ⟨z,hzn,hzM⟩ := exists_norm_eq_circleMaximum hf.continuous (show 0 ≤ 2*r by positivity)
  have hzn' : ‖z‖ = 2*r := by simpa only [Metric.mem_sphere, dist_zero_right] using hzn
  refine ⟨z, ?_, ?_⟩
  · rw [hzn']
    apply max_le <;> dsimp [r] <;> linarith [le_max_right T (max 1 R),
      le_max_left (1 : ℝ) R, le_max_right (1 : ℝ) R]
  · rw [hzn', hzM, Real.rpow_one]
    exact hT r (le_max_left _ _)

/-- A lower bound outside a zero-density exceptional set extends to all
large radii, with half the original constant. -/
theorem centralIndex_eventually_ge_of_zero_density_exception {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hne : f ≠ 0) {E : Set ℝ}
    (hE : LevinDensity.ZeroRadialDensity E) {c : ℝ} (hc : 0 ≤ c)
    (hν : ∀ᶠ r : ℝ in atTop ⊓ 𝓟 Eᶜ,
      c*r ≤ (centralIndex (taylorCoeff f) r : ℝ)) :
    ∀ᶠ r : ℝ in atTop, (c/2)*r ≤ (centralIndex (taylorCoeff f) r : ℝ) := by
  obtain ⟨R, hR⟩ := eventually_atTop.mp (Filter.eventually_inf_principal.mp hν)
  filter_upwards [HelmrathExceptionalSet.exists_good_radius hE
    (show (0 : ℝ) ≤ 1/2 by norm_num) (show (1/2 : ℝ) < 1 by norm_num),
    eventually_ge_atTop (max 1 (2*R))] with r hs hr
  obtain ⟨s, hs, hsE⟩ := hs
  have hrpos : 0 < r := zero_lt_one.trans_le ((le_max_left _ _).trans hr)
  have hspos : 0 < s := by linarith [hs.1]
  have hsr : s ≤ r := by simpa using hs.2
  have hRs : R ≤ s := by linarith [hs.1, (le_max_right _ _).trans hr]
  have hmono : (centralIndex (taylorCoeff f) s : ℝ) ≤ centralIndex (taylorCoeff f) r := by
    exact_mod_cast centralIndex_le (taylor_admissible hf hne hspos)
      (taylor_admissible hf hne hrpos) hsr
  calc
    (c/2)*r ≤ c*s := by nlinarith [mul_le_mul_of_nonneg_left hs.1 hc]
    _ ≤ centralIndex (taylorCoeff f) s := hR s hRs hsE
    _ ≤ centralIndex (taylorCoeff f) r := hmono

/-- The two-sided linear estimate gives finite positive exponential type.
This result makes no assumption that the ratio of central index and radius
converges, and uses no classification of the entire function. -/
theorem finitePositiveType_of_centralIndex_linear_bounds {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hne : f ≠ 0) {c C : ℝ}
    (hc : 0 < c) (hC : 0 ≤ C)
    (hν : ∀ᶠ r : ℝ in atTop,
      c*r ≤ (centralIndex (taylorCoeff f) r : ℝ) ∧
      (centralIndex (taylorCoeff f) r : ℝ) ≤ C*r) :
    LevinGrowth.FinitePositiveType f 1 := by
  refine ⟨?_, positiveType_of_centralIndex_eventually_ge hf hne hc
    (hν.mono fun _ h => h.1)⟩
  obtain ⟨A,B,hA,hB,hbound⟩ := exponentialBound_of_centralIndex_eventually_le hf hC
    (hν.mono fun _ h => h.2)
  refine ⟨A+B+1, by positivity, 1, zero_lt_one, fun z hz => ?_⟩
  rw [Real.rpow_one]
  calc
    ‖f z‖ ≤ A*Real.exp (B*‖z‖) := hbound z
    _ ≤ Real.exp A * Real.exp (B*‖z‖) :=
      mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp A]) (Real.exp_pos _).le
    _ = Real.exp (A+B*‖z‖) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((A+B+1)*‖z‖) := Real.exp_le_exp.mpr (by nlinarith)

/-- In particular these bounds have exact order one. -/
theorem order_and_type_of_centralIndex_linear_bounds {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hne : f ≠ 0) {c C : ℝ}
    (hc : 0 < c) (hC : 0 ≤ C)
    (hν : ∀ᶠ r : ℝ in atTop,
      c*r ≤ (centralIndex (taylorCoeff f) r : ℝ) ∧
      (centralIndex (taylorCoeff f) r : ℝ) ≤ C*r) :
    CRGOrder.IsOrder f 1 ∧ LevinGrowth.FinitePositiveType f 1 := by
  have h := finitePositiveType_of_centralIndex_linear_bounds hf hne hc hC hν
  exact ⟨CRGOrder.finitePositiveType_isOrder zero_le_one h,h⟩

#print axioms maximumTerm_ge_radius_ratio
#print axioms positiveType_of_centralIndex_eventually_ge
#print axioms centralIndex_eventually_ge_of_zero_density_exception
#print axioms finitePositiveType_of_centralIndex_linear_bounds
#print axioms order_and_type_of_centralIndex_linear_bounds
end WimanValiron
