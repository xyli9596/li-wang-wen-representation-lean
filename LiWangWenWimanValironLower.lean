import WimanValironLocalAngular
import LiWangWenCore
import LiWangWenWimanValironStrip

/-!
# The small-logarithmic-derivative contradiction

These are direct Wiman--Valiron lemmas, independent of the representation
theorem. A displacement into the left half-plane makes every positive
exponential frequency smaller than every fixed power of the logarithmic
derivative. The remaining constant-frequency group has a nonzero limit
after division by its lowest derivative power.
-/

set_option autoImplicit false
noncomputable section
open Filter Finset Polynomial
open scoped Topology

namespace LiWangWen

/-- A nonnegative function is eventually bounded below by a positive
constant if no nontrivial refinement of the filter makes it tend to zero. -/
theorem exists_eventually_pos_le_of_no_zero_subfilter {α : Type*}
    {l : Filter α} {q : α → ℝ} (hq : ∀ᶠ x in l, 0 ≤ q x)
    (hno : ∀ (g : Filter α) [NeBot g], g ≤ l → ¬ Tendsto q g (𝓝 0)) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x in l, c ≤ q x := by
  by_contra hn
  push Not at hn
  have hfreq (ε : ℝ) (hε : 0 < ε) : ∃ᶠ x in l, q x < ε := by
    simpa only [Filter.not_eventually,not_le] using hn ε hε
  have hcluster : MapClusterPt 0 l q := by
    apply (Metric.nhds_basis_ball.mapClusterPt_iff_frequently).mpr
    intro ε hε
    apply ((hfreq ε hε).and_eventually hq).mono
    intro x hx
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg hx.2] using hx.1
  let g := Filter.comap q (𝓝 0) ⊓ l
  have : NeBot g := Filter.neBot_inf_comap_iff_map'.mpr hcluster
  apply hno g inf_le_right
  exact (Filter.map_mono inf_le_left).trans Filter.map_comap_le

/-- Exponential decay along the actual angular displacement dominates every
fixed power of the radius. -/
theorem angular_decay_mul_pow_tendsto_zero (k : ℕ) :
    Tendsto (fun r : ℝ => Real.exp (-(r^((1 : ℝ)/8))/8)*r^k)
      atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    ((k : ℝ)*8) (1/8) (by norm_num)).comp
    (tendsto_rpow_atTop (show (0 : ℝ) < 1/8 by norm_num))
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
  simp only [Function.comp_def]
  rw [← Real.rpow_mul hr]
  have he : (1/8 : ℝ)*((k : ℝ)*8) = (k : ℝ) := by ring
  rw [he, Real.rpow_natCast]
  have he' : -(1/8 : ℝ)*r^(1/8 : ℝ) = -r^(1/8 : ℝ)/8 := by ring
  rw [he']
  exact mul_comm _ _

/-- A lower bound `1/r` for the logarithmic derivative suffices to absorb
all the negative powers introduced by normalization. -/
theorem exp_div_pow_tendsto_zero_of_left_displacement {α : Type*}
    {l : Filter α} {r : α → ℝ} {z w : α → ℂ}
    (hr : Tendsto r l atTop)
    (hw : ∀ᶠ x in l, 1 / r x ≤ ‖w x‖)
    (hz : ∀ᶠ x in l, (z x).re ≤ -(r x)^((1 : ℝ)/8)/8)
    (k : ℕ) :
    Tendsto (fun x => Complex.exp (z x)/(w x)^k) l (𝓝 0) := by
  apply squeeze_zero_norm' _ ((angular_decay_mul_pow_tendsto_zero k).comp hr)
  filter_upwards [hr.eventually (eventually_gt_atTop (0 : ℝ)),hw,hz] with x hx hxw hxz
  have hwpos : 0 < ‖w x‖ := lt_of_lt_of_le (one_div_pos.mpr hx) hxw
  have hpow : 1 ≤ ‖w x‖^k * (r x)^k := by
    rw [← mul_pow]
    exact one_le_pow₀ ((div_le_iff₀ hx).mp hxw)
  have hinv : (‖w x‖^k)⁻¹ ≤ (r x)^k := by
    apply (inv_le_iff_one_le_mul₀ (pow_pos hwpos k)).mpr
    simpa only [mul_comm] using hpow
  rw [norm_div, Complex.norm_exp, norm_pow, div_eq_mul_inv]
  exact mul_le_mul (Real.exp_le_exp.mpr hxz) hinv (inv_nonneg.mpr (pow_nonneg hwpos.le k))
    (Real.exp_pos _).le

/-- The nonconstant part of a polynomial coefficient is negligible after
division by any fixed power of the small logarithmic derivative. -/
theorem polynomial_exp_perturbation_normalized_tendsto_zero {α : Type*}
    {l : Filter α} {r : α → ℝ} {z w a : α → ℂ}
    (hr : Tendsto r l atTop)
    (hwlo : ∀ᶠ x in l, 1 / r x ≤ ‖w x‖)
    (hz : ∀ᶠ x in l, (z x).re ≤ -(r x)^((1 : ℝ)/8)/8)
    (hw : Tendsto w l (𝓝 0)) (ha : Tendsto a l (𝓝 1))
    (P : Polynomial ℂ) (j k : ℕ) :
    Tendsto (fun x => ((P.eval (Complex.exp (z x))-P.eval 0)*a x*(w x)^j)/(w x)^k)
      l (𝓝 0) := by
  have hediv := exp_div_pow_tendsto_zero_of_left_displacement hr hwlo hz k
  have he : Tendsto (fun x => Complex.exp (z x)) l (𝓝 0) := by
    simpa only [pow_zero,div_one] using
      exp_div_pow_tendsto_zero_of_left_displacement hr hwlo hz 0
  have hp := ((P.divX.continuous.tendsto (0 : ℂ)).comp he)
  have hh := ((hediv.mul hp).mul ha).mul (hw.pow j)
  simp only [zero_mul] at hh
  apply hh.congr'
  filter_upwards with x
  have hid : P.eval (Complex.exp (z x))-P.eval 0 =
      Complex.exp (z x)*P.divX.eval (Complex.exp (z x)) := by
    have h := congrArg (fun Q : Polynomial ℂ => Q.eval (Complex.exp (z x)))
      (Polynomial.X_mul_divX_add P)
    simp only [eval_add,eval_mul,eval_X,eval_C] at h
    rw [← coeff_zero_eq_eval_zero]
    linear_combination -h
  rw [hid]
  dsimp only [Function.comp_def]
  ring

/-- An exact ODE balance cannot persist with a small logarithmic derivative
at the left-displaced near-maximum points. The least nonzero constant
coefficient is specified explicitly in this auxiliary lemma. -/
theorem small_logDerivative_balance_impossible {α ι : Type*}
    [Fintype ι] [DecidableEq ι] {l : Filter α} [NeBot l]
    (index : ι → ℕ) (hinj : Function.Injective index)
    (P : ι → Polynomial ℂ) (i₀ : ι) (hi₀ : (P i₀).eval 0 ≠ 0)
    (hmin : ∀ j, (P j).eval 0 ≠ 0 → index i₀ ≤ index j)
    {r : α → ℝ} {z w : α → ℂ} {a : α → ι → ℂ}
    (hr : Tendsto r l atTop)
    (hwlo : ∀ᶠ x in l, 1 / r x ≤ ‖w x‖)
    (hz : ∀ᶠ x in l, (z x).re ≤ -(r x)^((1 : ℝ)/8)/8)
    (hw : Tendsto w l (𝓝 0))
    (ha : ∀ j, Tendsto (fun x => a x j) l (𝓝 1))
    (hbalance : ∀ᶠ x in l,
      ∑ j, (P j).eval (Complex.exp (z x))*a x j*(w x)^(index j) = 0) : False := by
  have hwne : ∀ᶠ x in l, w x ≠ 0 := by
    filter_upwards [hr.eventually (eventually_gt_atTop (0 : ℝ)),hwlo] with x hx hxw
    exact norm_pos_iff.mp (lt_of_lt_of_le (one_div_pos.mpr hx) hxw)
  have hmain := perturbed_polynomial_min_normalized index hinj
    (fun j => (P j).eval 0) i₀ hmin ha hw hwne
  have hsmall := tendsto_finsetSum Finset.univ (fun j _ =>
    polynomial_exp_perturbation_normalized_tendsto_zero
      hr hwlo hz hw (ha j) (P j) (index j) (index i₀))
  simp only [Finset.sum_const_zero] at hsmall
  have htotal : Tendsto (fun x =>
      (∑ j, (P j).eval (Complex.exp (z x))*a x j*(w x)^(index j))/(w x)^(index i₀))
      l (𝓝 ((P i₀).eval 0)) := by
    have hh := hmain.add hsmall
    rw [add_zero] at hh
    apply hh.congr'
    filter_upwards with x
    rw [Finset.sum_div, ← Finset.sum_add_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hzero : Tendsto (fun x =>
      (∑ j, (P j).eval (Complex.exp (z x))*a x j*(w x)^(index j))/(w x)^(index i₀))
      l (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hbalance] with x hx
    simp only [hx,zero_div]
  exact hi₀ (tendsto_nhds_unique htotal hzero)

/-- The same contradiction, choosing the least nonzero constant
coefficient from the actual differential operator. -/
theorem small_logDerivative_ode_balance_impossible {α : Type*} {n : ℕ}
    {l : Filter α} [NeBot l] (P : Fin (n+1) → Polynomial ℂ)
    (hne : ∃ j, (P j).eval 0 ≠ 0)
    {r : α → ℝ} {z w : α → ℂ} {a : α → Fin (n+1) → ℂ}
    (hr : Tendsto r l atTop)
    (hwlo : ∀ᶠ x in l, 1 / r x ≤ ‖w x‖)
    (hz : ∀ᶠ x in l, (z x).re ≤ -(r x)^((1 : ℝ)/8)/8)
    (hw : Tendsto w l (𝓝 0))
    (ha : ∀ j, Tendsto (fun x => a x j) l (𝓝 1))
    (hbalance : ∀ᶠ x in l,
      ∑ j, (P j).eval (Complex.exp (z x))*a x j*(w x)^j.val = 0) : False := by
  classical
  let s := Finset.univ.filter (fun j => (P j).eval 0 ≠ 0)
  have hs : s.Nonempty := by
    obtain ⟨j,hj⟩ := hne
    exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩⟩
  let i₀ := s.min' hs
  have hi₀ : (P i₀).eval 0 ≠ 0 := (Finset.mem_filter.mp (Finset.min'_mem s hs)).2
  have hmin (j : Fin (n+1)) (hj : (P j).eval 0 ≠ 0) : i₀.val ≤ j.val := by
    exact Finset.min'_le s j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩)
  exact small_logDerivative_balance_impossible Fin.val Fin.val_injective P i₀ hi₀ hmin
    hr hwlo hz hw ha hbalance

/-- The exact coefficient balance obtained from an actual differential
equation and the actual normalized derivative ratios. -/
theorem ode_balance_of_derivativeRatio {n : ℕ}
    {P : Fin (n+1) → Polynomial ℂ} {f : ℂ → ℂ}
    (hsol : Solves P f) {z : ℂ} {N : ℕ}
    (hz : z ≠ 0) (hN : N ≠ 0) (hfz : f z ≠ 0) :
    ∑ j, (P j).eval (Complex.exp z)*
      WimanValiron.derivativeRatio f N j.val z*((N : ℂ)/z)^j.val = 0 := by
  have h := congrArg (fun v : ℂ => v/f z) (hsol z)
  rw [Finset.sum_div,zero_div] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro j _
  have hd := WimanValiron.derivative_eq_with_relative_error (j := j.val) hz hN hfz
  simp only [add_sub_cancel] at hd
  rw [mul_div_assoc,hd]
  ring

/-- A direct contradiction for actual ODE solutions on any nontrivial
sequence or filter of left-displaced WV points. The WV ratio convergence
is explicit; no representation or growth conclusion is a hypothesis. -/
theorem no_small_logDerivative_at_left_WV_points {α : Type*} {n : ℕ}
    {l : Filter α} [NeBot l] {P : Fin (n+1) → Polynomial ℂ} {f : ℂ → ℂ}
    (hne : ∃ j, (P j).eval 0 ≠ 0) (hsol : Solves P f)
    {r : α → ℝ} {z : α → ℂ} {N : α → ℕ}
    (hr : Tendsto r l atTop)
    (hz : ∀ᶠ x in l, ‖z x‖ = r x)
    (hN : ∀ᶠ x in l, 1 ≤ N x)
    (hfz : ∀ᶠ x in l, f (z x) ≠ 0)
    (hleft : ∀ᶠ x in l, (z x).re ≤ -(r x)^((1 : ℝ)/8)/8)
    (hsmall : Tendsto (fun x => (N x : ℝ)/r x) l (𝓝 0))
    (hWV : ∀ j : Fin (n+1), Tendsto
      (fun x => WimanValiron.derivativeRatio f (N x) j.val (z x)) l (𝓝 1)) : False := by
  let w : α → ℂ := fun x => (N x : ℂ)/z x
  have hpos := hr.eventually (eventually_gt_atTop (0 : ℝ))
  have hwlo : ∀ᶠ x in l, 1 / r x ≤ ‖w x‖ := by
    filter_upwards [hpos,hz,hN] with x hx hxz hxN
    simp only [w,norm_div,Complex.norm_natCast,hxz]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hxN) hx.le
  have hw : Tendsto w l (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply hsmall.congr'
    filter_upwards [hz] with x hxz
    simp only [w,norm_div,Complex.norm_natCast,hxz]
  apply small_logDerivative_ode_balance_impossible P hne hr hwlo hleft hw hWV
  filter_upwards [hpos,hz,hN,hfz] with x hx hxz hxN hxf
  exact ode_balance_of_derivativeRatio hsol
    (norm_pos_iff.mp (hxz.symm ▸ hx)) (Nat.ne_zero_of_lt hxN) hxf

/-- In the monic case the constant-frequency group is automatically
nonzero, because the top derivative has coefficient one. -/
theorem monic_no_small_logDerivative_at_left_WV_points {α : Type*} {n : ℕ}
    {l : Filter α} [NeBot l] {P : Fin (n+1) → Polynomial ℂ} {f : ℂ → ℂ}
    (hlead : P (Fin.last n) = 1) (hsol : Solves P f)
    {r : α → ℝ} {z : α → ℂ} {N : α → ℕ}
    (hr : Tendsto r l atTop)
    (hz : ∀ᶠ x in l, ‖z x‖ = r x)
    (hN : ∀ᶠ x in l, 1 ≤ N x)
    (hfz : ∀ᶠ x in l, f (z x) ≠ 0)
    (hleft : ∀ᶠ x in l, (z x).re ≤ -(r x)^((1 : ℝ)/8)/8)
    (hsmall : Tendsto (fun x => (N x : ℝ)/r x) l (𝓝 0))
    (hWV : ∀ j : Fin (n+1), Tendsto
      (fun x => WimanValiron.derivativeRatio f (N x) j.val (z x)) l (𝓝 1)) : False := by
  exact no_small_logDerivative_at_left_WV_points
    ⟨Fin.last n,by simp [hlead]⟩ hsol hr hz hN hfz hleft hsmall hWV

/-- Complete direct lower-growth contradiction once the grouped equation
has placed the actual maximum points in a logarithmic strip. The theorem
constructs its exceptional set and proves the required WV ratios at the
rotated points; those ratios are not hypotheses. -/
theorem direct_small_logDerivative_impossible_of_strip {n : ℕ}
    {P : Fin (n+1) → Polynomial ℂ} {f : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (hnp : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z)
    (hne : ∃ j, (P j).eval 0 ≠ 0) (hsol : Solves P f) :
    ∃ E : Set ℝ, MeasurableSet E ∧
      HelmrathExceptionalSet.FiniteLogarithmicMeasure E ∧
      ∀ (l : Filter ℝ) [NeBot l], l ≤ atTop →
        ∀ (z : ℝ → ℂ) (A B : ℝ),
        (∀ᶠ r in l, r ∉ E) →
        (∀ᶠ r in l, ‖z r‖ = r ∧
          ‖f (z r)‖ = WimanValiron.circleMaximum f r ∧
          |(z r).re| ≤ A+B*Real.log r) →
        ¬ Tendsto (fun r => (WimanValiron.centralIndex
          (WimanValiron.taylorCoeff f) r : ℝ)/r) l (𝓝 0) := by
  classical
  obtain ⟨E₁,hE₁m,hE₁,hrotate⟩ :=
    WimanValiron.exists_eventually_left_nearMaximum hf hnp
  obtain ⟨E₂,hE₂m,hE₂,hquant⟩ :=
    WimanValiron.wimanValiron_quantitative hf hnp
      (δ := (1 : ℝ)/16) (by norm_num) (by norm_num)
  have hEu : HelmrathExceptionalSet.FiniteLogarithmicMeasure (E₁ ∪ E₂) := by
    unfold HelmrathExceptionalSet.FiniteLogarithmicMeasure at *
    rw [Set.union_inter_distrib_right]
    exact lt_of_le_of_lt (MeasureTheory.lintegral_union_le _ _ _)
      (ENNReal.add_lt_top.mpr ⟨hE₁,hE₂⟩)
  refine ⟨E₁ ∪ E₂,hE₁m.union hE₂m,hEu,?_⟩
  intro l _ hl z A B hgood hpoint hsmall
  let N : ℝ → ℕ := WimanValiron.centralIndex (WimanValiron.taylorCoeff f)
  let ζ : ℝ → ℂ := fun r => z r * Complex.exp
    (Complex.I*(WimanValiron.leftAngularStep (z r) r : ℂ))
  have hr : Tendsto (fun r : ℝ => r) l atTop := tendsto_id.mono_left hl
  have hrpos := hr.eventually (eventually_gt_atTop (0 : ℝ))
  have hgood₁ : ∀ᶠ r in l, r ∉ E₁ := hgood.mono (fun _ h => fun hx => h (Or.inl hx))
  have hgood₂ : ∀ᶠ r in l, r ∉ E₂ := hgood.mono (fun _ h => fun hx => h (Or.inr hx))
  have hNsmall : ∀ᶠ r in l, (N r : ℝ) ≤ r := by
    filter_upwards [hrpos,hsmall.eventually_lt_const zero_lt_one] with r hr hq
    exact ((div_lt_one hr).mp hq).le
  have hrot : ∀ᶠ r in l, ‖ζ r‖ = r ∧
      WimanValiron.circleMaximum f r/2 ≤ ‖f (ζ r)‖ ∧
      (ζ r).re ≤ -r^((1 : ℝ)/8)/8 := by
    apply hrotate l hl z A B hgood₁
    filter_upwards [hpoint,hNsmall] with r hz hN
    exact ⟨hz.1,hz.2.1,hN,hz.2.2⟩
  have hN : ∀ᶠ r in l, 1 ≤ N r :=
    ((WimanValiron.taylor_centralIndex_tendsto_atTop hf hnp).eventually
      (eventually_ge_atTop 1)).filter_mono hl
  have hfne : f ≠ 0 := by intro h; exact hnp ⟨0,by simp [h]⟩
  have hfζ : ∀ᶠ r in l, f (ζ r) ≠ 0 := by
    filter_upwards [hrpos,hrot] with r hr hζ
    exact norm_pos_iff.mp ((half_pos (WimanValiron.circleMaximum_pos hf hfne hr)).trans_le hζ.2.1)
  have hpower : ∀ᶠ r in l, (N r : ℝ)^(-(1 : ℝ)/8+1/16) ≤ 1/2 :=
    (WimanValiron.centralIndex_error_power_tendsto_zero hf hnp
      (δ := (1 : ℝ)/16) (by norm_num) hl).eventually_le_const (by norm_num)
  have hWV (j : Fin (n+1)) : Tendsto
      (fun r => WimanValiron.derivativeRatio f (N r) j.val (ζ r)) l (𝓝 1) := by
    obtain ⟨C,hC,R,hR,htail⟩ := hquant j.val
    apply WimanValiron.derivativeRatio_tendsto_one_of_power_error hf hnp
      (δ := (1 : ℝ)/16) (C := C) (by norm_num) hl
    filter_upwards [hr.eventually (eventually_ge_atTop R),hgood₂,hrot,hpower,hrpos]
      with r hrR hg hζ hp hrp
    apply (htail r hrR hg).2 (ζ r) hζ.1
    calc
      _ ≤ WimanValiron.circleMaximum f r/2 := by
        have hm := mul_le_mul_of_nonneg_left hp
          (WimanValiron.circleMaximum_pos hf hfne hrp).le
        simpa only [mul_one_div] using hm
      _ ≤ ‖f (ζ r)‖ := hζ.2.1
  exact no_small_logDerivative_at_left_WV_points hne hsol hr
    (hrot.mono (fun _ h => h.1)) hN hfζ
    (hrot.mono (fun _ h => h.2.2)) hsmall hWV

end LiWangWen

#print axioms LiWangWen.angular_decay_mul_pow_tendsto_zero
#print axioms LiWangWen.exp_div_pow_tendsto_zero_of_left_displacement
#print axioms LiWangWen.polynomial_exp_perturbation_normalized_tendsto_zero
#print axioms LiWangWen.small_logDerivative_balance_impossible
#print axioms LiWangWen.small_logDerivative_ode_balance_impossible
#print axioms LiWangWen.ode_balance_of_derivativeRatio
#print axioms LiWangWen.no_small_logDerivative_at_left_WV_points
#print axioms LiWangWen.monic_no_small_logDerivative_at_left_WV_points
#print axioms LiWangWen.direct_small_logDerivative_impossible_of_strip

#print axioms LiWangWen.exists_eventually_pos_le_of_no_zero_subfilter
