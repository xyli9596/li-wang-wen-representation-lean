import LiWangWenGrowth
import HelmrathODECoefficients
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Positive exponential type of a nonpolynomial exponential sum

Equal frequencies are combined before choosing a dominant direction, so
cancellation cannot create an unsupported positive-type conclusion.
-/

noncomputable section
open Filter Finset Polynomial
open scoped Topology

namespace LiWangWen

theorem IsExponentialSum.exponentialBound {f : ℂ → ℂ} (h : IsExponentialSum f) :
    ExponentialBound f := by
  obtain ⟨N, p, a, hf⟩ := h
  have he : f = (fun z => ∑ j, (p j).eval z * Complex.exp (a j*z)) := funext hf
  rw [he]
  exact bound_sum Finset.univ _ (fun j _ =>
    (bound_poly_comp (p j) bound_id).mul (bound_exp (a j)))

theorem IsExponentialSum.grouped {f : ℂ → ℂ} (h : IsExponentialSum f) :
    ∃ S : Finset ℂ, ∃ p : ℂ → Polynomial ℂ,
      (∀ a ∈ S, p a ≠ 0) ∧ ∀ z, f z = ∑ a ∈ S, (p a).eval z * Complex.exp (a*z) := by
  classical
  obtain ⟨N, p, a, hf⟩ := h
  let S := Finset.univ.image a
  let q : ℂ → Polynomial ℂ := fun b => ∑ j : Fin N with a j = b, p j
  refine ⟨S.filter (fun b => q b ≠ 0), q, ?_, ?_⟩
  · intro b hb
    exact (Finset.mem_filter.mp hb).2
  · intro z
    rw [hf z]
    have hsum : ∑ b ∈ S, (q b).eval z * Complex.exp (b*z) =
        ∑ j : Fin N, (p j).eval z * Complex.exp (a j*z) := by
      calc
        _ = ∑ b ∈ S, ∑ j : Fin N with a j = b,
            (p j).eval z * Complex.exp (a j*z) := by
          apply Finset.sum_congr rfl
          intro b hb
          simp only [q, Polynomial.eval_finsetSum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j hj
          rw [(Finset.mem_filter.mp hj).2]
        _ = _ := Finset.sum_fiberwise_of_maps_to
          (fun j _ => Finset.mem_image_of_mem a (Finset.mem_univ j)) _
    rw [← hsum]
    symm
    apply Finset.sum_filter_of_ne
    intro b hb hne
    contrapose! hne
    simp [hne]

theorem strict_real_projection {a b : ℂ} (hba : b ≠ a) (h : ‖b‖ ≤ ‖a‖) :
    (b*starRingEnd ℂ a).re < ‖a‖^2 := by
  have hpos : 0 < ‖b-a‖^2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hba))
  have he := Complex.normSq_sub b a
  simp only [Complex.normSq_eq_norm_sq] at he
  have hb := sq_le_sq₀ (norm_nonneg b) (norm_nonneg a) |>.mpr h
  nlinarith

/-- Exponential suppression beats every polynomial on a fixed unit ray. -/
theorem polynomial_ray_exp_decay (p : Polynomial ℂ) {ζ c : ℂ}
    (hζ : ‖ζ‖ = 1) (hc : (c*ζ).re < 0) (d : ℕ) :
    Tendsto (fun r : ℝ => p.eval ((r : ℂ)*ζ) / ((r : ℂ)*ζ)^d *
      Complex.exp (c*((r : ℂ)*ζ))) atTop (𝓝 0) := by
  by_cases hp : p = 0
  · simp [hp]
  have hray : Tendsto (fun r : ℝ => ‖(r : ℂ)*ζ‖) atTop atTop := by
    apply tendsto_id.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
    simp [hζ, abs_of_nonneg hr]
  have hnorm := (HelmrathODE.polynomial_normalized_tendsto p hp hray).norm
  have hb := hnorm.eventually_lt_const (show ‖p.leadingCoeff‖ < ‖p.leadingCoeff‖+1 by linarith)
  let C : ℝ := ‖p.leadingCoeff‖+1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbound : ∀ᶠ r : ℝ in atTop,
      ‖p.eval ((r : ℂ)*ζ) / ((r : ℂ)*ζ)^d * Complex.exp (c*((r : ℂ)*ζ))‖ ≤
        C*(r^(p.natDegree)*Real.exp (-(-(c*ζ).re)*r)) := by
    filter_upwards [hb, eventually_ge_atTop (1 : ℝ)] with r hb hr
    have hrp : 0 < r := by linarith
    have hn : ‖(r : ℂ)*ζ‖ = r := by simp [hζ, abs_of_pos hrp]
    rw [norm_div, norm_pow, hn] at hb
    have hpbound : ‖p.eval ((r : ℂ)*ζ)‖ ≤ C*r^p.natDegree := by
      exact le_of_lt ((div_lt_iff₀ (pow_pos hrp _)).mp hb)
    have hd : 1 ≤ r^d := one_le_pow₀ hr
    have he : (c*((r : ℂ)*ζ)).re = (c*ζ).re*r := by
      rw [show c*((r : ℂ)*ζ) = (c*ζ)*(r : ℂ) by ring]
      simp
    rw [norm_mul, norm_div, norm_pow, hn, Complex.norm_exp, he]
    have hdiv : ‖p.eval ((r : ℂ)*ζ)‖ / r^d ≤ C*r^p.natDegree := by
      apply (div_le_self (norm_nonneg _) hd).trans hpbound
    simpa only [neg_neg, mul_assoc] using
      mul_le_mul_of_nonneg_right hdiv (Real.exp_pos ((c*ζ).re*r)).le
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) hbound
  simpa only [Real.rpow_natCast, mul_zero] using
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (p.natDegree : ℝ) (-(c*ζ).re)
      (neg_pos.mpr hc)).const_mul C

/-- Along a strictly dominant ray, the normalized sum tends to the actual
leading coefficient of its dominant polynomial multiplier. -/
theorem exponential_sum_dominant_ray_limit (S : Finset ℂ) (p : ℂ → Polynomial ℂ)
    {a ζ : ℂ} (ha : a ∈ S) (hpa : p a ≠ 0) (hζ : ‖ζ‖ = 1)
    (hstrict : ∀ b ∈ S, b ≠ a → ((b-a)*ζ).re < 0) :
    Tendsto (fun r : ℝ =>
      (∑ b ∈ S, (p b).eval ((r : ℂ)*ζ) * Complex.exp (b*((r : ℂ)*ζ))) /
        (((r : ℂ)*ζ)^(p a).natDegree * Complex.exp (a*((r : ℂ)*ζ))))
      atTop (𝓝 (p a).leadingCoeff) := by
  classical
  have hray : Tendsto (fun r : ℝ => ‖(r : ℂ)*ζ‖) atTop atTop := by
    apply tendsto_id.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
    simp [hζ, abs_of_nonneg hr]
  have hlim (b : ℂ) (hb : b ∈ S) :
      Tendsto (fun r : ℝ => (p b).eval ((r : ℂ)*ζ) / ((r : ℂ)*ζ)^(p a).natDegree *
        Complex.exp ((b-a)*((r : ℂ)*ζ))) atTop
        (𝓝 (if b = a then (p a).leadingCoeff else 0)) := by
    by_cases hba : b = a
    · subst b
      simpa only [sub_self, zero_mul, Complex.exp_zero, mul_one, if_true] using
        HelmrathODE.polynomial_normalized_tendsto (p a) hpa hray
    · simpa only [if_neg hba] using polynomial_ray_exp_decay (p b) hζ
        (hstrict b hb hba) (p a).natDegree
  have hsum := tendsto_finsetSum S hlim
  simp only [Finset.sum_ite_eq', ha, if_true] at hsum
  apply hsum.congr'
  apply Eventually.of_forall
  intro r
  dsimp only
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro b _
  rw [sub_mul, Complex.exp_sub]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem ExponentialBound.finiteType_one {f : ℂ → ℂ} (h : ExponentialBound f) :
    ∃ C : ℝ, 0 < C ∧ ∃ R : ℝ, 0 < R ∧
      ∀ z : ℂ, R ≤ ‖z‖ → ‖f z‖ ≤ Real.exp (C * ‖z‖^(1 : ℝ)) := by
  obtain ⟨A,B,hA,hB,hbound⟩ := h
  refine ⟨A+B+1,by positivity,1,zero_lt_one,?_⟩
  intro z hz
  rw [Real.rpow_one]
  calc
    ‖f z‖ ≤ A*Real.exp (B*‖z‖) := hbound z
    _ ≤ Real.exp A * Real.exp (B*‖z‖) :=
      mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp A]) (Real.exp_pos _).le
    _ = Real.exp (A+B*‖z‖) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((A+B+1)*‖z‖) := Real.exp_le_exp.mpr (by nlinarith)

/-- A nonzero normalized limit on one exponentially growing ray supplies
the positive half of finite positive type. -/
theorem positiveType_of_dominant_ray {f : ℂ → ℂ} {ζ a L : ℂ} {d : ℕ}
    (hζ : ‖ζ‖ = 1) (hα : 0 < (a*ζ).re) (hL : L ≠ 0)
    (hlim : Tendsto (fun r : ℝ => f ((r : ℂ)*ζ) /
      (((r : ℂ)*ζ)^d * Complex.exp (a*((r : ℂ)*ζ)))) atTop (𝓝 L)) :
    ∃ c : ℝ, 0 < c ∧ ∀ R : ℝ, ∃ z : ℂ, max R 1 ≤ ‖z‖ ∧
      Real.exp (c * ‖z‖^(1 : ℝ)) ≤ ‖f z‖ := by
  let α : ℝ := (a*ζ).re
  let k : ℝ := ‖L‖/2
  have hk : 0 < k := by dsimp [k]; exact half_pos (norm_pos_iff.mpr hL)
  have hkL : k < ‖L‖ := by dsimp [k]; linarith [norm_pos_iff.mpr hL]
  have hlow := hlim.norm.eventually_const_lt hkL
  have hexp : Tendsto (fun r : ℝ => Real.exp (-(α/2)*r)) atTop (𝓝 0) := by
    have hα' : 0 < α/2 := by dsimp [α]; positivity
    simpa only [Real.rpow_zero, one_mul] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (α/2) hα'
  have hsmall := hexp.eventually_lt_const hk
  have hevent : ∀ᶠ r : ℝ in atTop,
      Real.exp ((α/2)*r) ≤ ‖f ((r : ℂ)*ζ)‖ := by
    filter_upwards [hlow,hsmall,eventually_ge_atTop (1 : ℝ)] with r hrlo hrsmall hr
    have hrp : 0 < r := zero_lt_one.trans_le hr
    have hn : ‖(r : ℂ)*ζ‖ = r := by simp [hζ, abs_of_pos hrp]
    have he : (a*((r : ℂ)*ζ)).re = α*r := by
      rw [show a*((r : ℂ)*ζ) = (a*ζ)*(r : ℂ) by ring]
      simp [α]
    rw [norm_div, norm_mul, norm_pow, hn, Complex.norm_exp, he] at hrlo
    have hprod : k*(r^d*Real.exp (α*r)) ≤ ‖f ((r : ℂ)*ζ)‖ :=
      ((lt_div_iff₀ (mul_pos (pow_pos hrp _) (Real.exp_pos _))).mp hrlo).le
    calc
      Real.exp ((α/2)*r) = Real.exp (-(α/2)*r)*Real.exp (α*r) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ k*Real.exp (α*r) :=
        mul_le_mul_of_nonneg_right hrsmall.le (Real.exp_pos _).le
      _ ≤ k*(r^d*Real.exp (α*r)) := by
        have hpow := one_le_pow₀ hr (n := d)
        apply mul_le_mul_of_nonneg_left _ hk.le
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hpow (Real.exp_pos (α*r)).le
      _ ≤ _ := hprod
  obtain ⟨T,hT⟩ := eventually_atTop.mp hevent
  refine ⟨α/2, by dsimp [α]; positivity, ?_⟩
  intro R
  let r : ℝ := max T (max R 1)
  have hr : 0 < r := zero_lt_one.trans_le ((le_max_right R 1).trans (le_max_right T _))
  have hn : ‖(r : ℂ)*ζ‖ = r := by simp [hζ,abs_of_pos hr]
  refine ⟨(r : ℂ)*ζ, ?_, ?_⟩
  · rw [hn]
    exact le_max_right _ _
  · simpa only [hn,Real.rpow_one] using hT r (le_max_left _ _)

/-- Nonpolynomial exponential sums have finite positive exponential type.
Repeated frequencies and cancellation were removed by `grouped` above. -/
theorem IsExponentialSum.finitePositiveType_one {f : ℂ → ℂ}
    (h : IsExponentialSum f)
    (hnp : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z) :
    LevinGrowth.FinitePositiveType f 1 := by
  classical
  refine ⟨h.exponentialBound.finiteType_one, ?_⟩
  obtain ⟨S,p,hp,hf⟩ := h.grouped
  have hnz : ∃ b ∈ S, b ≠ 0 := by
    by_contra hno
    push Not at hno
    apply hnp
    refine ⟨∑ b ∈ S, p b, ?_⟩
    intro z
    rw [hf, Polynomial.eval_finsetSum]
    apply Finset.sum_congr rfl
    intro b hb
    rw [hno b hb, zero_mul, Complex.exp_zero, mul_one]
  obtain ⟨b,hb,hbne⟩ := hnz
  obtain ⟨a,ha,hmax⟩ := Finset.exists_max_image S (fun b => ‖b‖) ⟨b,hb⟩
  have hap : 0 < ‖a‖ := (norm_pos_iff.mpr hbne).trans_le (hmax b hb)
  let ζ : ℂ := starRingEnd ℂ a / (‖a‖ : ℂ)
  have hζ : ‖ζ‖ = 1 := by
    simp only [ζ, norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hap, div_self hap.ne']
  have haz : (a*ζ).re = ‖a‖ := by
    dsimp [ζ]
    rw [← mul_div_assoc, Complex.div_ofReal_re, Complex.mul_conj]
    simp only [Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    field_simp
  have hstrict : ∀ c ∈ S, c ≠ a → ((c-a)*ζ).re < 0 := by
    intro c hc hca
    have hh := strict_real_projection hca (hmax c hc)
    have he : ((c-a)*ζ).re = ((c*starRingEnd ℂ a).re - ‖a‖^2) / ‖a‖ := by
      dsimp [ζ]
      rw [← mul_div_assoc, Complex.div_ofReal_re, sub_mul, Complex.sub_re, Complex.mul_conj]
      simp only [Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    rw [he]
    exact div_neg_of_neg_of_pos (sub_neg.mpr hh) hap
  have hlim := exponential_sum_dominant_ray_limit S p ha (hp a ha) hζ hstrict
  have hlimf : Tendsto (fun r : ℝ => f ((r : ℂ)*ζ) /
      (((r : ℂ)*ζ)^(p a).natDegree * Complex.exp (a*((r : ℂ)*ζ))))
      atTop (𝓝 (p a).leadingCoeff) := by
    simpa only [hf] using hlim
  exact positiveType_of_dominant_ray hζ (by rw [haz]; exact hap)
    (Polynomial.leadingCoeff_ne_zero.mpr (hp a ha)) hlimf

theorem IsExponentialSum.isOrder_one {f : ℂ → ℂ} (h : IsExponentialSum f)
    (hnp : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z) : CRGOrder.IsOrder f 1 :=
  CRGOrder.finitePositiveType_isOrder zero_le_one (h.finitePositiveType_one hnp)

#print axioms IsExponentialSum.exponentialBound
#print axioms IsExponentialSum.grouped
#print axioms strict_real_projection
#print axioms polynomial_ray_exp_decay
#print axioms exponential_sum_dominant_ray_limit
#print axioms ExponentialBound.finiteType_one
#print axioms positiveType_of_dominant_ray
#print axioms IsExponentialSum.finitePositiveType_one
#print axioms IsExponentialSum.isOrder_one
end LiWangWen
