import LiWangWenWimanValironGroups
import LiWangWenWimanValironLower
import WimanValironLinearType

/-!
# The unconditional direct lower bound for the central index

The actual grouped differential equation supplies the strip needed by the
same-circle Wiman--Valiron displacement. Excluding zero as a limit on every
nontrivial subfilter gives a uniform positive lower bound on good radii.
Monotonicity then removes the finite-logarithmic-measure exceptional set.
The proof uses no exponential-sum representation and no growth assumption.
-/

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Topology

namespace LiWangWen

/-- On the small-ratio regime, the logarithm of the logarithmic derivative
is bounded by the logarithm of the radius. -/
theorem abs_log_le_log_of_inv_radius_le {r t : ℝ}
    (hr : 0 < r) (htlo : 1/r ≤ t) (hthi : t ≤ 1) :
    |Real.log t| ≤ Real.log r := by
  have ht : 0 < t := lt_of_lt_of_le (one_div_pos.mpr hr) htlo
  have hlo := Real.log_le_log (one_div_pos.mpr hr) htlo
  have hhi : Real.log t ≤ 0 := Real.log_nonpos ht.le hthi
  rw [Real.log_div (by norm_num) hr.ne',Real.log_one,zero_sub] at hlo
  rw [abs_of_nonpos hhi]
  linarith

/-- Every transcendental entire solution whose constant-frequency group
is nonzero has a central index bounded below by a positive linear function.
This is the lower half of the direct repair of Lemma 5.1. -/
theorem direct_centralIndex_eventually_linear_lower {n : ℕ}
    {P : Fin (n+1) → Polynomial ℂ} {f : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (hnp : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z)
    (hne : ∃ j, (P j).eval 0 ≠ 0) (hsol : Solves P f) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ r : ℝ in atTop,
      c*r ≤ (WimanValiron.centralIndex (WimanValiron.taylorCoeff f) r : ℝ) := by
  classical
  obtain ⟨E₁,hE₁m,hE₁,hno⟩ := direct_small_logDerivative_impossible_of_strip hf hnp hne hsol
  obtain ⟨E₂,hE₂m,hE₂,_hE₂bot,z,hmax,hWV⟩ :=
    WimanValiron.wimanValiron_at_maximum_points hf hnp
      (δ := (1 : ℝ)/16) (by norm_num) (by norm_num)
  let E := E₁ ∪ E₂
  have hEm : MeasurableSet E := hE₁m.union hE₂m
  have hE : HelmrathExceptionalSet.FiniteLogarithmicMeasure E := by
    unfold E HelmrathExceptionalSet.FiniteLogarithmicMeasure at *
    rw [Set.union_inter_distrib_right]
    exact lt_of_le_of_lt (MeasureTheory.lintegral_union_le _ _ _)
      (ENNReal.add_lt_top.mpr ⟨hE₁,hE₂⟩)
  let g : Filter ℝ := atTop ⊓ 𝓟 Eᶜ
  let N : ℝ → ℕ := WimanValiron.centralIndex (WimanValiron.taylorCoeff f)
  have hqpos : ∀ᶠ r in g, 0 ≤ (N r : ℝ)/r := by
    filter_upwards [(eventually_gt_atTop (0 : ℝ)).filter_mono
      (show g ≤ atTop from inf_le_left)] with r hr
    exact div_nonneg (Nat.cast_nonneg _) hr.le
  have hnotzero (l : Filter ℝ) [NeBot l] (hl : l ≤ g) :
      ¬ Tendsto (fun r => (N r : ℝ)/r) l (𝓝 0) := by
    intro hsmall
    have hltop : l ≤ atTop := hl.trans inf_le_left
    have hgood : ∀ᶠ r in l, r ∉ E :=
      (show ∀ᶠ r in 𝓟 Eᶜ, r ∉ E from by simp).filter_mono (hl.trans inf_le_right)
    have hgood₁ : ∀ᶠ r in l, r ∉ E₁ := hgood.mono (fun _ h => fun hx => h (Or.inl hx))
    have hgood₂ : ∀ᶠ r in l, r ∉ E₂ := hgood.mono (fun _ h => fun hx => h (Or.inr hx))
    have hl₂ : l ≤ atTop ⊓ 𝓟 E₂ᶜ :=
      le_inf hltop (Filter.le_principal_iff.mpr hgood₂)
    have hrpos : ∀ᶠ r in l, 0 < r := (eventually_gt_atTop (0 : ℝ)).filter_mono hltop
    have hN : ∀ᶠ r in l, 1 ≤ N r :=
      ((WimanValiron.taylor_centralIndex_tendsto_atTop hf hnp).eventually
        (eventually_ge_atTop 1)).filter_mono hltop
    let w : ℝ → ℂ := fun r => (N r : ℂ)/z r
    have hnorm : ∀ᶠ r in l, ‖w r‖ = (N r : ℝ)/r := by
      filter_upwards [hrpos] with r hr
      simp only [w,norm_div,Complex.norm_natCast,(hmax r hr).1]
    have hw : Tendsto w l (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      exact hsmall.congr' (hnorm.mono (fun _ h => h.symm))
    have hwlo : ∀ᶠ r in l, 1/r ≤ ‖w r‖ := by
      filter_upwards [hrpos,hN,hnorm] with r hr hNr hn
      rw [hn]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hNr) hr.le
    have hwne : ∀ᶠ r in l, w r ≠ 0 := by
      filter_upwards [hrpos,hwlo] with r hr hw
      exact norm_pos_iff.mp ((one_div_pos.mpr hr).trans_le hw)
    have hratios (j : Fin (n+1)) : Tendsto
        (fun r => WimanValiron.derivativeRatio f (N r) j.val (z r)) l (𝓝 1) :=
      (hWV j.val).2.mono_left hl₂
    have hfne : f ≠ 0 := by intro h; exact hnp ⟨0,by simp [h]⟩
    have hbalance : ∀ᶠ r in l, ∑ j : Fin (n+1), (P j).eval (Complex.exp (z r))*
        WimanValiron.derivativeRatio f (N r) j.val (z r)*(w r)^j.val = 0 := by
      filter_upwards [hrpos,hN] with r hr hNr
      exact ode_balance_of_derivativeRatio hsol
        (norm_pos_iff.mp ((hmax r hr).1.symm ▸ hr)) (Nat.ne_zero_of_lt hNr)
        (norm_pos_iff.mp ((hmax r hr).2.symm ▸ WimanValiron.circleMaximum_pos hf hfne hr))
    have hP : ∃ j, P j ≠ 0 := by
      obtain ⟨j,hj⟩ := hne
      exact ⟨j,fun h => hj (by simp [h])⟩
    obtain ⟨C,hC,hstrip⟩ := exponential_ode_small_w_strip P hP Fin.val Fin.val_injective
      hratios hw hwne hbalance
    have hupper : ∀ᶠ r in l, ‖w r‖ ≤ 1 := by
      filter_upwards [hnorm,hsmall.eventually_lt_const zero_lt_one] with r hn hs
      exact hn ▸ hs.le
    apply hno l hltop z C C hgood₁ ?_ hsmall
    filter_upwards [hrpos,hstrip,hwlo,hupper] with r hr hs hwlo hwhi
    refine ⟨(hmax r hr).1,(hmax r hr).2,?_⟩
    have hlog := abs_log_le_log_of_inv_radius_le hr hwlo hwhi
    calc
      |(z r).re| ≤ C*(1+|Real.log ‖w r‖|) := hs
      _ ≤ C*(1+Real.log r) := mul_le_mul_of_nonneg_left (by linarith [hlog]) hC.le
      _ = C+C*Real.log r := by ring
  obtain ⟨c,hc,hbound⟩ := exists_eventually_pos_le_of_no_zero_subfilter hqpos hnotzero
  have hlin : ∀ᶠ r in g, c*r ≤ (N r : ℝ) := by
    filter_upwards [hbound,(eventually_gt_atTop (0 : ℝ)).filter_mono
      (show g ≤ atTop from inf_le_left)] with r hb hr
    exact (le_div_iff₀ hr).mp hb
  refine ⟨c/2,half_pos hc,?_⟩
  exact WimanValiron.centralIndex_eventually_ge_of_zero_density_exception hf
    (by intro h; exact hnp ⟨0,by simp [h]⟩)
    (HelmrathExceptionalSet.zero_density_of_finite_logarithmic_measure hEm hE) hc.le hlin

/-- The monic case used in Lemma 5.1. -/
theorem monic_direct_centralIndex_eventually_linear_lower {n : ℕ}
    {P : Fin (n+1) → Polynomial ℂ} {f : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (hnp : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z)
    (hlead : P (Fin.last n) = 1) (hsol : Solves P f) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ r : ℝ in atTop,
      c*r ≤ (WimanValiron.centralIndex (WimanValiron.taylorCoeff f) r : ℝ) :=
  direct_centralIndex_eventually_linear_lower hf hnp
    ⟨Fin.last n,by simp [hlead]⟩ hsol

end LiWangWen

#print axioms LiWangWen.abs_log_le_log_of_inv_radius_le
#print axioms LiWangWen.direct_centralIndex_eventually_linear_lower
#print axioms LiWangWen.monic_direct_centralIndex_eventually_linear_lower
