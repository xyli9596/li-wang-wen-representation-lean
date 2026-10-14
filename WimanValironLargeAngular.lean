import WimanValironLocalAngular
import LiWangWenWimanValironEndpoint

/-! Deep half-plane near-maximum points under a linear central-index upper
bound. The local angular estimate and all derivative ratios are proved from
actual Taylor coefficients and the quantitative Wiman--Valiron theorem. -/

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Topology
namespace WimanValiron

theorem wimanValiron_local_angular_linear {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnp : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z) {K : ℝ} (hK : 0 ≤ K) :
    ∃ E : Set ℝ, MeasurableSet E ∧ HelmrathExceptionalSet.FiniteLogarithmicMeasure E ∧
      ∃ C : ℝ, 0 < C ∧ ∃ R : ℝ, 0 < R ∧
        ∀ r : ℝ, R ≤ r → r ∉ E → (centralIndex (taylorCoeff f) r : ℝ) ≤ K*r →
          ∀ z : ℂ, ‖z‖ = r → ‖f z‖ = circleMaximum f r → ∀ θ : ℝ,
            |θ| ≤ r^(-7/8 : ℝ) →
            ‖angularRatio f (centralIndex (taylorCoeff f) r) z θ - 1‖ ≤
              (2*Real.sqrt C)*K^(13/16 : ℝ)*r^(-1/16 : ℝ) + (C/2)*K^(13/8 : ℝ)*r^(-1/8 : ℝ) := by
  have hne : f ≠ 0 := by intro h; exact hnp ⟨0, by simp [h]⟩
  obtain ⟨P,hP⟩ := comparisonSequence_bounded (show (1 : ℝ) < 33/32 by norm_num)
  obtain ⟨E,hEm,hE,hnormal⟩ := exists_exceptional_set_normal_radii
    (fun _ hr => taylor_admissible hf hne hr) (comparisonSequence_pos (33/32))
    (comparisonSequence_strictMono (33/32)).monotone hP
  obtain ⟨C,hC,hbound⟩ := normal_angularRatio_bound
  obtain ⟨R0,hR0⟩ := eventually_atTop.mp
    ((taylor_centralIndex_tendsto_atTop hf hnp).eventually (eventually_ge_atTop 1))
  refine ⟨E,hEm,hE,C,hC,max 1 R0,by positivity,?_⟩
  intro r hr hg hNr z hz hmax θ hθ
  have hrpos : 0 < r := zero_lt_one.trans_le ((le_max_left _ _).trans hr)
  have hN : 1 ≤ centralIndex (taylorCoeff f) r := hR0 r ((le_max_right _ _).trans hr)
  obtain ⟨N,hn⟩ := hnormal r hrpos hg
  have haN := normal_coefficient_ne_zero (comparisonSequence_pos (33/32)) hn
    (taylor_admissible hf hne hrpos).2.2
  have heq : N = centralIndex (taylorCoeff f) r := centralIndex_unique
    (normal_isCentralIndex (comparisonSequence_pos (33/32))
      (comparisonSequence_strictMono (33/32)) hn haN)
    (centralIndex_spec (taylor_admissible hf hne hrpos))
  subst N
  exact (hbound hf hne hN hn hz hmax θ).trans (LiWangWen.angular_error_linear_radial_bound hC.le hK hrpos hNr hθ)

theorem linear_local_angular_error_tendsto_zero (C K : ℝ) {l : Filter ℝ}
    (hl : l ≤ atTop) :
    Tendsto (fun r => (2*Real.sqrt C)*K^(13/16 : ℝ)*r^(-1/16 : ℝ) +
      (C/2)*K^(13/8 : ℝ)*r^(-1/8 : ℝ)) l (𝓝 0) := by
  have h1 := (tendsto_rpow_neg_atTop (show (0 : ℝ) < 1/16 by norm_num)).mono_left hl
  have h2 := (tendsto_rpow_neg_atTop (show (0 : ℝ) < 1/8 by norm_num)).mono_left hl
  simpa only [neg_div,mul_zero,add_zero] using
    (h1.const_mul ((2*Real.sqrt C)*K^(13/16 : ℝ))).add
      (h2.const_mul ((C/2)*K^(13/8 : ℝ)))

/-- At every sufficiently large good radius, an actual near-maximum point
can be chosen in a deep half-plane, with genuine WV limits of all fixed
orders. Only a linear upper bound on the central index is assumed. -/
theorem exists_deep_nearMaximum_WV_points {f : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (hnp : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z)
    {K : ℝ} (hK : 0 ≤ K)
    (hNu : ∀ᶠ r : ℝ in atTop, (centralIndex (taylorCoeff f) r : ℝ) ≤ K*r) :
    ∃ E : Set ℝ, MeasurableSet E ∧ HelmrathExceptionalSet.FiniteLogarithmicMeasure E ∧
      ∃ ζ : ℝ → ℂ,
        (∀ᶠ r : ℝ in atTop ⊓ 𝓟 Eᶜ,
          ‖ζ r‖ = r ∧ circleMaximum f r/2 ≤ ‖f (ζ r)‖ ∧
            r^(1/8 : ℝ)/8 ≤ |(ζ r).re|) ∧
        ∀ j : ℕ, Tendsto
          (fun r => derivativeRatio f (centralIndex (taylorCoeff f) r) j (ζ r))
          (atTop ⊓ 𝓟 Eᶜ) (𝓝 1) := by
  classical
  obtain ⟨E₁,hE₁m,hE₁,C,hC,R,hR,hlocal⟩ :=
    wimanValiron_local_angular_linear hf hnp hK
  obtain ⟨E₂,hE₂m,hE₂,hquant⟩ := wimanValiron_quantitative hf hnp
    (δ := (1 : ℝ)/16) (by norm_num) (by norm_num)
  have hEu : HelmrathExceptionalSet.FiniteLogarithmicMeasure (E₁ ∪ E₂) := by
    unfold HelmrathExceptionalSet.FiniteLogarithmicMeasure at *
    rw [Set.union_inter_distrib_right]
    exact lt_of_le_of_lt (MeasureTheory.lintegral_union_le _ _ _)
      (ENNReal.add_lt_top.mpr ⟨hE₁,hE₂⟩)
  have hchoices : ∀ r : ℝ, ∃ z : ℂ,
      0 < r → ‖z‖ = r ∧ ‖f z‖ = circleMaximum f r := by
    intro r
    by_cases hr : 0 < r
    · obtain ⟨z,hz,hmax⟩ := exists_norm_eq_circleMaximum hf.continuous hr.le
      refine ⟨z,fun _ => ⟨?_,hmax⟩⟩
      simpa only [Metric.mem_sphere,dist_zero_right] using hz
    · exact ⟨0,fun h => False.elim (hr h)⟩
  choose z hz using hchoices
  let l : Filter ℝ := atTop ⊓ 𝓟 (E₁ ∪ E₂)ᶜ
  let ζ : ℝ → ℂ := fun r => if r^(1/8 : ℝ)/8 ≤ |(z r).re| then z r else
    z r*Complex.exp (Complex.I*(leftAngularStep (z r) r : ℂ))
  have hl : l ≤ atTop := inf_le_left
  have hr : Tendsto (fun r : ℝ => r) l atTop := tendsto_id.mono_left hl
  have hpos := hr.eventually (eventually_gt_atTop (0 : ℝ))
  have hgood : ∀ᶠ r in l, r ∉ E₁ ∪ E₂ := by
    exact Filter.eventually_inf_principal.mpr (Filter.Eventually.of_forall (fun _ h => h))
  have hgood₁ : ∀ᶠ r in l, r ∉ E₁ := hgood.mono (fun _ h => fun hx => h (Or.inl hx))
  have hgood₂ : ∀ᶠ r in l, r ∉ E₂ := hgood.mono (fun _ h => fun hx => h (Or.inr hx))
  have hfne : f ≠ 0 := by intro h; exact hnp ⟨0,by simp [h]⟩
  have hsmall := (linear_local_angular_error_tendsto_zero C K hl).eventually_le_const
    (show (0 : ℝ) < 1/2 by norm_num)
  have hrot : ∀ᶠ r in l, ‖ζ r‖ = r ∧
      circleMaximum f r/2 ≤ ‖f (ζ r)‖ ∧ r^(1/8 : ℝ)/8 ≤ |(ζ r).re| := by
    filter_upwards [hr.eventually (eventually_ge_atTop (max R 1)),hsmall,hgood₁,
      hNu.filter_mono hl] with r hrR herr hg hN
    have hr1 : 1 ≤ r := (le_max_right _ _).trans hrR
    have hrp : 0 < r := zero_lt_one.trans_le hr1
    obtain ⟨hzn,hzM⟩ := hz r hrp
    by_cases hx : r^(1/8 : ℝ)/8 ≤ |(z r).re|
    · simp only [ζ,if_pos hx]
      exact ⟨hzn,by rw [hzM]; linarith [circleMaximum_pos hf hfne hrp],hx⟩
    · have hxsmall : |(z r).re| ≤ r^(1/8 : ℝ)/8 := (lt_of_not_ge hx).le
      have hleft := left_angular_rotation_re_le hr1 hzn hxsmall
      have hnear : circleMaximum f r/2 ≤
          ‖f (z r*Complex.exp (Complex.I*(leftAngularStep (z r) r : ℂ)))‖ := by
        apply angularRatio_nearMaximum (circleMaximum_pos hf hfne hrp) hzM
          (N := centralIndex (taylorCoeff f) r)
        exact (hlocal r ((le_max_left _ _).trans hrR) hg hN (z r) hzn hzM
          (leftAngularStep (z r) r) (abs_leftAngularStep _ hrp.le).le).trans herr
      simp only [ζ,if_neg hx]
      refine ⟨(norm_angular_rotation _ _).trans hzn,hnear,?_⟩
      exact (by linarith : r^(1/8 : ℝ)/8 ≤
        -(z r*Complex.exp (Complex.I*(leftAngularStep (z r) r : ℂ))).re).trans
          (neg_le_abs _)
  have hpower : ∀ᶠ r in l, (centralIndex (taylorCoeff f) r : ℝ)^(-(1 : ℝ)/8+1/16) ≤ 1/2 :=
    (centralIndex_error_power_tendsto_zero hf hnp
      (δ := (1 : ℝ)/16) (by norm_num) hl).eventually_le_const (by norm_num)
  refine ⟨E₁ ∪ E₂,hE₁m.union hE₂m,hEu,ζ,hrot,?_⟩
  intro j
  obtain ⟨Cj,hCj,Rj,hRj,htail⟩ := hquant j
  apply derivativeRatio_tendsto_one_of_power_error hf hnp
    (δ := (1 : ℝ)/16) (C := Cj) (by norm_num) hl
  filter_upwards [hr.eventually (eventually_ge_atTop Rj),hgood₂,hrot,hpower,hpos]
    with r hrR hg hζ hp hrp
  apply (htail r hrR hg).2 (ζ r) hζ.1
  calc
    _ ≤ circleMaximum f r/2 := by
      have hm := mul_le_mul_of_nonneg_left hp (circleMaximum_pos hf hfne hrp).le
      simpa only [mul_one_div] using hm
    _ ≤ ‖f (ζ r)‖ := hζ.2.1

#print axioms wimanValiron_local_angular_linear
#print axioms linear_local_angular_error_tendsto_zero
#print axioms exists_deep_nearMaximum_WV_points
end WimanValiron
