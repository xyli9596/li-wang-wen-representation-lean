import WimanValironTheorem
import WimanValironLimits

/-!
# A proved same-circle local Wiman--Valiron estimate

The actual angular Taylor series and the already proved second coefficient
moment bound imply a uniform local estimate near every maximum point.
No local monomial approximation is assumed as an additional hypothesis.
-/

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Topology

namespace WimanValiron

/-- The exact phase-normalized ratio at an angular displacement. -/
def angularRatio (f : ℂ → ℂ) (N : ℕ) (z : ℂ) (θ : ℝ) : ℂ :=
  Complex.exp (-Complex.I * ((θ*(N : ℝ) : ℝ) : ℂ)) *
    f (z*Complex.exp (Complex.I*(θ : ℂ))) / f z

/-- The actual angular deviation is controlled by the first signed and
second absolute Taylor moments. -/
theorem angular_deviation_le_moments {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hne : f ≠ 0) {r : ℝ} {z : ℂ} (hz : ‖z‖ = r)
    {N : ℕ} (hN : 0 < N) (t : ℝ) :
    ‖Complex.exp (-Complex.I*(t : ℂ))*
      f (z*Complex.exp (Complex.I*((t/(N : ℝ) : ℝ) : ℂ))) - f z‖ ≤
      |t| *‖rawTaylorMoment f z N 1‖ + t^2/2*absoluteTaylorMoment f r N 2 := by
  have hb : Summable (fun n => ‖taylorCoeff f n*z^n‖) :=
    (hasSum_taylorCoeff hf z).summable.norm
  have hsecond : Summable (fun n => ‖taylorCoeff f n*z^n‖*(realCenteredIndex N n)^2) := by
    have hs := summable_absoluteTaylorMoment hf hne (hz ▸ norm_nonneg z) N 2
    simpa only [norm_mul, norm_pow, hz, sq_abs, term, mul_comm, mul_left_comm, mul_assoc] using hs
  have h := angular_tsum_second_moment_bound (fun n => taylorCoeff f n*z^n)
    (realCenteredIndex N) hb hsecond t
  rw [angular_taylor_sum hf z (Nat.ne_zero_of_lt hN) t, (hasSum_taylorCoeff hf z).tsum_eq] at h
  have hfirst : (∑' n, (taylorCoeff f n*z^n)*(realCenteredIndex N n : ℂ)) =
      rawTaylorMoment f z N 1 := by
    simp only [rawTaylorMoment, pow_one, mul_comm, mul_left_comm]
  have habs : (∑' n, ‖taylorCoeff f n*z^n‖*(realCenteredIndex N n)^2) =
      absoluteTaylorMoment f r N 2 := by
    simp only [absoluteTaylorMoment, norm_mul, norm_pow, hz, sq_abs, term,
      mul_comm, mul_left_comm]
  rw [hfirst, habs] at h
  have ht : ‖Complex.I*(t : ℂ)*rawTaylorMoment f z N 1‖ =
      |t| *‖rawTaylorMoment f z N 1‖ := by simp
  have htri := norm_add_le
    (Complex.exp (-Complex.I*(t : ℂ))*
      f (z*Complex.exp (Complex.I*((t/(N : ℝ) : ℝ) : ℂ))) - f z -
        Complex.I*(t : ℂ)*rawTaylorMoment f z N 1)
    (Complex.I*(t : ℂ)*rawTaylorMoment f z N 1)
  rw [sub_add_cancel, ht] at htri
  exact htri.trans (by linarith)

/-- A genuine second-moment bound gives a relative local estimate at a
maximum point, with no restriction on the real angle. -/
theorem angularRatio_bound_of_second_moment {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hne : f ≠ 0) {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : ‖z‖ = r)
    (hmax : ‖f z‖ = circleMaximum f r) {N : ℕ} (hN : 0 < N)
    {C e : ℝ} (hC : 0 < C)
    (hsecond : absoluteTaylorMoment f r N 2 ≤ C*circleMaximum f r*(N : ℝ)^e)
    (θ : ℝ) :
    ‖angularRatio f N z θ - 1‖ ≤
      (2*Real.sqrt C)*|θ| *(N : ℝ)^(1+e/2) +
        (C/2)*θ^2*(N : ℝ)^(2+e) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hM := circleMaximum_pos hf hne hr
  have hfz : f z ≠ 0 := norm_pos_iff.mp (hmax ▸ hM)
  have hfirst := norm_rawTaylorMoment_one_of_power_second hf hne hz hN hC hsecond
  have h := angular_deviation_le_moments hf hne hz hN (θ*(N : ℝ))
  rw [mul_div_cancel_right₀ θ hNr.ne'] at h
  unfold angularRatio
  rw [div_sub_one hfz, norm_div, hmax]
  apply (div_le_iff₀ hM).mpr
  apply h.trans
  have hfirst' := mul_le_mul_of_nonneg_left hfirst (abs_nonneg (θ*(N : ℝ)))
  have hsecond' := mul_le_mul_of_nonneg_left hsecond
    (show 0 ≤ (θ*(N : ℝ))^2/2 by positivity)
  apply (add_le_add hfirst' hsecond').trans_eq
  rw [abs_mul, abs_of_pos hNr, mul_pow,
    Real.rpow_add hNr, Real.rpow_add hNr, Real.rpow_one,
    Real.rpow_ofNat]
  ring

/-- Uniform normal-radius constants for a convenient local angular error.
The exponents are chosen strictly below the displacement exponent `7/8`. -/
theorem normal_angularRatio_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {f : ℂ → ℂ}, Differentiable ℂ f → f ≠ 0 →
      ∀ {r : ℝ} {N : ℕ}, 1 ≤ N →
        NormalRadiusAt (taylorCoeff f) (comparisonSequence (33/32)) r N →
        ∀ {z : ℂ}, ‖z‖ = r → ‖f z‖ = circleMaximum f r → ∀ θ : ℝ,
          ‖angularRatio f N z θ - 1‖ ≤
            (2*Real.sqrt C)*|θ| *(N : ℝ)^(13/16 : ℝ) +
              (C/2)*θ^2*(N : ℝ)^(13/8 : ℝ) := by
  obtain ⟨C,hC,hbound⟩ := normal_absoluteTaylorMoment_bound 2
    (α := (33/32 : ℝ)) (β := (13/24 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨C,hC,?_⟩
  intro f hf hne r N hN hn z hz hmax θ
  have hsecond : absoluteTaylorMoment f r N 2 ≤
      C*circleMaximum f r*(N : ℝ)^(-3/8 : ℝ) := by
    simpa only [Nat.cast_ofNat, show (13/24 : ℝ)*(2+1)-2 = -3/8 by norm_num] using
      hbound hf hne hN hn
  convert angularRatio_bound_of_second_moment hf hne hn.1 hz hmax hN hC hsecond θ using 1
  norm_num

/-- At central index at most the radius, an angular displacement of size
`r^(-7/8)` has a quantitative error tending to zero. -/
theorem angular_error_radial_bound {C r θ : ℝ} {N : ℕ}
    (hC : 0 ≤ C) (hr : 0 < r) (hNr : (N : ℝ) ≤ r)
    (hθ : |θ| ≤ r^(-7/8 : ℝ)) :
    (2*Real.sqrt C)*|θ| *(N : ℝ)^(13/16 : ℝ) +
      (C/2)*θ^2*(N : ℝ)^(13/8 : ℝ) ≤
        (2*Real.sqrt C)*r^(-1/16 : ℝ) + (C/2)*r^(-1/8 : ℝ) := by
  have hθ2 : θ^2 ≤ (r^(-7/8 : ℝ))^2 := by
    have h := mul_self_le_mul_self (abs_nonneg θ) hθ
    simpa only [← pow_two, sq_abs] using h
  have h1 : (N : ℝ)^(13/16 : ℝ) ≤ r^(13/16 : ℝ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg N) hNr (by norm_num)
  have h2 : (N : ℝ)^(13/8 : ℝ) ≤ r^(13/8 : ℝ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg N) hNr (by norm_num)
  calc
    _ ≤ (2*Real.sqrt C)*r^(-7/8 : ℝ)*r^(13/16 : ℝ) +
        (C/2)*(r^(-7/8 : ℝ))^2*r^(13/8 : ℝ) := by gcongr
    _ = _ := by
      rw [mul_assoc (2*Real.sqrt C), ← Real.rpow_add hr,
        ← Real.rpow_mul_natCast hr.le, mul_assoc (C/2), ← Real.rpow_add hr]
      norm_num

/-- Outside a constructed finite-logarithmic-measure set, every maximum
point with `nu(r) <= r` admits the same uniform angular estimate. -/
theorem wimanValiron_local_angular {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnp : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z) :
    ∃ E : Set ℝ, MeasurableSet E ∧ HelmrathExceptionalSet.FiniteLogarithmicMeasure E ∧
      ∃ C : ℝ, 0 < C ∧ ∃ R : ℝ, 0 < R ∧
        ∀ r : ℝ, R ≤ r → r ∉ E → (centralIndex (taylorCoeff f) r : ℝ) ≤ r →
          ∀ z : ℂ, ‖z‖ = r → ‖f z‖ = circleMaximum f r → ∀ θ : ℝ,
            |θ| ≤ r^(-7/8 : ℝ) →
            ‖angularRatio f (centralIndex (taylorCoeff f) r) z θ - 1‖ ≤
              (2*Real.sqrt C)*r^(-1/16 : ℝ) + (C/2)*r^(-1/8 : ℝ) := by
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
  exact (hbound hf hne hN hn hz hmax θ).trans (angular_error_radial_bound hC.le hrpos hNr hθ)

/-- The uniform radial error in the local angular estimate tends to zero. -/
theorem local_angular_error_tendsto_zero (C : ℝ) {l : Filter ℝ} (hl : l ≤ atTop) :
    Tendsto (fun r => (2*Real.sqrt C)*r^(-1/16 : ℝ) + (C/2)*r^(-1/8 : ℝ))
      l (𝓝 0) := by
  have h1 := (tendsto_rpow_neg_atTop (show (0 : ℝ) < 1/16 by norm_num)).mono_left hl
  have h2 := (tendsto_rpow_neg_atTop (show (0 : ℝ) < 1/8 by norm_num)).mono_left hl
  simpa only [neg_div, mul_zero, add_zero] using (h1.const_mul (2*Real.sqrt C)).add (h2.const_mul (C/2))

/-- In particular, the actual phase-normalized values converge to one for
arbitrary admissible angular displacements along any good-radius subfilter. -/
theorem angularRatio_tendsto_one_of_local_bound {f : ℂ → ℂ} {l : Filter ℝ}
    (hl : l ≤ atTop) {z : ℝ → ℂ} {θ : ℝ → ℝ} {C : ℝ}
    (hbound : ∀ᶠ r in l,
      ‖angularRatio f (centralIndex (taylorCoeff f) r) (z r) (θ r)-1‖ ≤
        (2*Real.sqrt C)*r^(-1/16 : ℝ) + (C/2)*r^(-1/8 : ℝ)) :
    Tendsto (fun r => angularRatio f (centralIndex (taylorCoeff f) r) (z r) (θ r)) l (𝓝 1) := by
  have h := squeeze_zero_norm' hbound (local_angular_error_tendsto_zero C hl)
  simpa only [sub_add_cancel, zero_add] using h.add_const (1 : ℂ)

/-- An angular ratio within one half of one remains a genuine near-maximum
point on the same circle. -/
theorem angularRatio_nearMaximum {f : ℂ → ℂ} {r : ℝ} {z : ℂ} {N : ℕ} {θ : ℝ}
    (hM : 0 < circleMaximum f r) (hmax : ‖f z‖ = circleMaximum f r)
    (hsmall : ‖angularRatio f N z θ - 1‖ ≤ 1/2) :
    circleMaximum f r / 2 ≤ ‖f (z*Complex.exp (Complex.I*(θ : ℂ)))‖ := by
  have htri := norm_sub_le (angularRatio f N z θ) (angularRatio f N z θ-1)
  have hnormphase : ‖Complex.exp (-Complex.I*((θ*(N : ℝ) : ℝ) : ℂ))‖ = 1 := by
    simp [Complex.norm_exp, Complex.mul_re]
  have hlow : 1/2 ≤ ‖angularRatio f N z θ‖ := by
    simp only [sub_sub_cancel, norm_one] at htri
    linarith
  unfold angularRatio at hlow
  rw [norm_div, norm_mul, hnormphase, one_mul, hmax] at hlow
  have h := (le_div_iff₀ hM).mp hlow
  linarith

/-- A small angular step toward the left half-plane, from either semicircle. -/
def leftAngularStep (z : ℂ) (r : ℝ) : ℝ :=
  if 0 ≤ z.im then r^(-7/8 : ℝ) else -(r^(-7/8 : ℝ))

theorem abs_leftAngularStep (z : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    |leftAngularStep z r| = r^(-7/8 : ℝ) := by
  unfold leftAngularStep
  split_ifs <;> simp [abs_of_nonneg (Real.rpow_nonneg hr _)]

theorem norm_angular_rotation (z : ℂ) (θ : ℝ) :
    ‖z*Complex.exp (Complex.I*(θ : ℂ))‖ = ‖z‖ := by
  simp [Complex.norm_exp, Complex.mul_re]

theorem re_left_angular_rotation (z : ℂ) (r : ℝ) :
    (z*Complex.exp (Complex.I*(leftAngularStep z r : ℂ))).re =
      z.re*Real.cos (r^(-7/8 : ℝ)) - |z.im| *Real.sin (r^(-7/8 : ℝ)) := by
  unfold leftAngularStep
  split_ifs with h
  · simp [Complex.mul_re, Complex.exp_re, Complex.exp_im, abs_of_nonneg h]
  · simp [Complex.mul_re, Complex.exp_re, Complex.exp_im, abs_of_neg (lt_of_not_ge h)]

/-- A point in a thin vertical strip can be rotated far into the left
half-plane while remaining on exactly the same circle. -/
theorem left_angular_rotation_re_le {r : ℝ} (hr : 1 ≤ r) {z : ℂ} (hz : ‖z‖ = r)
    (hx : |z.re| ≤ r^(1/8 : ℝ)/8) :
    (z*Complex.exp (Complex.I*(leftAngularStep z r : ℂ))).re ≤ -r^(1/8 : ℝ)/8 := by
  have hrpos : 0 < r := zero_lt_one.trans_le hr
  let t : ℝ := r^(-7/8 : ℝ)
  have htpos : 0 < t := Real.rpow_pos_of_pos hrpos _
  have ht1 : t ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hr (by norm_num)
  have hp : r^(1/8 : ℝ) ≤ r := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hr
      (show (1/8 : ℝ) ≤ 1 by norm_num)
  have hxhalf : |z.re| ≤ r/2 := by linarith
  have hy : r/2 ≤ |z.im| := by
    have h := Complex.norm_le_abs_re_add_abs_im z
    rw [hz] at h
    linarith
  have ht2 : t^2 ≤ 1 := pow_le_one₀ htpos.le ht1
  have ht3 : t^3 ≤ t := by nlinarith
  have hsin : t/2 ≤ Real.sin t := by
    have h := Real.sin_ge_sub_cube htpos.le
    nlinarith
  have hcos : z.re*Real.cos t ≤ |z.re| := by
    calc
      _ ≤ |z.re*Real.cos t| := le_abs_self _
      _ = |z.re| *|Real.cos t| := abs_mul _ _
      _ ≤ |z.re| *1 := mul_le_mul_of_nonneg_left (Real.abs_cos_le_one t) (abs_nonneg _)
      _ = _ := mul_one _
  have hprod : r*t/4 ≤ |z.im| *Real.sin t := by
    have h := mul_le_mul hy hsin (half_pos htpos).le (abs_nonneg _)
    nlinarith
  have hrt : r*t = r^(1/8 : ℝ) := by
    dsimp [t]
    calc
      r*r^(-7/8 : ℝ) = r^(1 : ℝ)*r^(-7/8 : ℝ) := by rw [Real.rpow_one]
      _ = r^(1/8 : ℝ) := by rw [← Real.rpow_add hrpos]; norm_num
  rw [re_left_angular_rotation]
  change z.re*Real.cos t - |z.im| *Real.sin t ≤ _
  rw [hrt] at hprod
  linarith

/-- Every fixed logarithmic strip is eventually thin enough for the
concrete leftward angular displacement. -/
theorem eventually_logarithmic_strip_small (A B : ℝ) :
    ∀ᶠ r : ℝ in atTop, A+B*Real.log r ≤ r^(1/8 : ℝ)/8 := by
  have hc : (fun _ : ℝ => A) =o[atTop] (fun r : ℝ => r^(1/8 : ℝ)) := by
    apply Asymptotics.isLittleO_const_left.mpr
    right
    have h := tendsto_rpow_atTop (show (0 : ℝ) < 1/8 by norm_num)
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    simp only [Function.comp_def, Real.norm_of_nonneg (Real.rpow_nonneg hr.le _)]
  have hl := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1/8 by norm_num)).const_mul_left B
  have hbound := (hc.add hl).bound (show (0 : ℝ) < 1/8 by norm_num)
  filter_upwards [hbound, eventually_gt_atTop (0 : ℝ)] with r hr hrpos
  simp only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hrpos _)] at hr
  exact (le_abs_self _).trans (by linarith)

/-- For maximum points in any fixed logarithmic strip with `nu <= r`,
the explicit leftward rotations stay near maximum and enter a deep left
half-plane. All local analytic and geometric claims have been proved above. -/
theorem exists_eventually_left_nearMaximum {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hnp : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z) :
    ∃ E : Set ℝ, MeasurableSet E ∧ HelmrathExceptionalSet.FiniteLogarithmicMeasure E ∧
      ∀ (l : Filter ℝ), l ≤ atTop → ∀ (z : ℝ → ℂ) (A B : ℝ),
        (∀ᶠ r in l, r ∉ E) →
        (∀ᶠ r in l, ‖z r‖ = r ∧ ‖f (z r)‖ = circleMaximum f r ∧
          (centralIndex (taylorCoeff f) r : ℝ) ≤ r ∧ |(z r).re| ≤ A+B*Real.log r) →
        ∀ᶠ r in l,
          ‖z r*Complex.exp (Complex.I*(leftAngularStep (z r) r : ℂ))‖ = r ∧
          circleMaximum f r/2 ≤
            ‖f (z r*Complex.exp (Complex.I*(leftAngularStep (z r) r : ℂ)))‖ ∧
          (z r*Complex.exp (Complex.I*(leftAngularStep (z r) r : ℂ))).re ≤
            -r^(1/8 : ℝ)/8 := by
  obtain ⟨E,hEm,hE,C,hC,R,hR,hlocal⟩ := wimanValiron_local_angular hf hnp
  refine ⟨E,hEm,hE,?_⟩
  intro l hl z A B hgood hpoint
  have hrad := (eventually_ge_atTop (max R 1)).filter_mono hl
  have hsmall := (local_angular_error_tendsto_zero C hl).eventually_lt_const
    (show (0 : ℝ) < 1/2 by norm_num)
  have hstrip := (eventually_logarithmic_strip_small A B).filter_mono hl
  have hne : f ≠ 0 := by intro h; exact hnp ⟨0, by simp [h]⟩
  filter_upwards [hrad,hsmall,hstrip,hgood,hpoint] with r hr herr hstrip hg hz
  have hr1 : 1 ≤ r := (le_max_right _ _).trans hr
  have hrpos : 0 < r := zero_lt_one.trans_le hr1
  refine ⟨(norm_angular_rotation _ _).trans hz.1, ?_,
    left_angular_rotation_re_le hr1 hz.1 (hz.2.2.2.trans hstrip)⟩
  apply angularRatio_nearMaximum (circleMaximum_pos hf hne hrpos) hz.2.1
    (N := centralIndex (taylorCoeff f) r)
  exact (hlocal r ((le_max_left _ _).trans hr) hg hz.2.2.1 (z r) hz.1 hz.2.1
    (leftAngularStep (z r) r) (abs_leftAngularStep _ hrpos.le).le).trans herr.le

end WimanValiron

#print axioms WimanValiron.angular_deviation_le_moments
#print axioms WimanValiron.angularRatio_bound_of_second_moment
#print axioms WimanValiron.normal_angularRatio_bound
#print axioms WimanValiron.angular_error_radial_bound
#print axioms WimanValiron.wimanValiron_local_angular
#print axioms WimanValiron.local_angular_error_tendsto_zero
#print axioms WimanValiron.angularRatio_tendsto_one_of_local_bound
#print axioms WimanValiron.angularRatio_nearMaximum
#print axioms WimanValiron.abs_leftAngularStep
#print axioms WimanValiron.norm_angular_rotation
#print axioms WimanValiron.re_left_angular_rotation
#print axioms WimanValiron.left_angular_rotation_re_le
#print axioms WimanValiron.eventually_logarithmic_strip_small
#print axioms WimanValiron.exists_eventually_left_nearMaximum
