import HelmrathRootClustering

/-!
# The corrected noncancellation step in the direct Wiman--Valiron proof

Terms are first grouped by their exponential frequency. At a large
logarithmic derivative, each group is normalized by its largest derivative
power; at a small logarithmic derivative, by its smallest derivative power.
The resulting nonzero limits prevent cancellation within a group. A finite
balance then places the maximum point in a logarithmic vertical strip.
-/

set_option autoImplicit false
noncomputable section
open Filter Finset Polynomial
open scoped Topology

namespace LiWangWen
open HelmrathNewtonBranches HelmrathRootClustering

/-- Perturbations of the derivative ratios do not change the dominant
coefficient when the logarithmic derivative tends to infinity. -/
theorem perturbed_polynomial_max_normalized {α ι : Type*} [Fintype ι] [DecidableEq ι]
    {l : Filter α} (index : ι → ℕ) (hinj : Function.Injective index)
    (c : ι → ℂ) (i₀ : ι) (hmax : ∀ j, c j ≠ 0 → index j ≤ index i₀)
    {b : α → ι → ℂ} {w : α → ℂ}
    (hb : ∀ j, Tendsto (fun x => b x j) l (𝓝 1))
    (hw : Tendsto (fun x => ‖w x‖) l atTop) :
    Tendsto (fun x => (∑ j, c j*b x j*(w x)^(index j)) / (w x)^(index i₀))
      l (𝓝 (c i₀)) := by
  have hwne : ∀ᶠ x in l, w x ≠ 0 := by
    filter_upwards [hw.eventually (eventually_gt_atTop (0 : ℝ))] with x hx
    exact norm_pos_iff.mp hx
  have hlim (j : ι) :
      Tendsto (fun x => c j*b x j*((w x)^(index j)/(w x)^(index i₀)))
        l (𝓝 (if j=i₀ then c i₀ else 0)) := by
    by_cases hji : j = i₀
    · subst j
      simp only [ite_true]
      apply (show Tendsto (fun x => c i₀*b x i₀) l (𝓝 (c i₀)) by
        simpa only [mul_one] using (hb i₀).const_mul (c i₀)).congr'
      filter_upwards [hwne] with x hx
      simp [div_self (pow_ne_zero _ hx)]
    · by_cases hc : c j = 0
      · simpa only [hc, zero_mul, if_neg hji] using
          (tendsto_const_nhds (x := (0 : ℂ)) (f := l))
      · have hjlt : index j < index i₀ := lt_of_le_of_ne (hmax j hc)
          (fun h => hji (hinj h))
        have he : (index j : ℝ) - index i₀ < 0 := sub_neg.mpr (by exact_mod_cast hjlt)
        have hp := cpow_negative_tendsto_zero hw he
        have hratio : Tendsto (fun x => (w x)^(index j)/(w x)^(index i₀)) l (𝓝 0) := by
          apply hp.congr'
          filter_upwards [hwne] with x hx
          rw [Complex.ofReal_sub, Complex.ofReal_natCast, Complex.ofReal_natCast,
            Complex.cpow_sub _ _ hx, Complex.cpow_natCast, Complex.cpow_natCast]
        simpa only [if_neg hji, mul_one, mul_zero] using
          ((hb j).const_mul (c j)).mul hratio
  have hsum := tendsto_finsetSum Finset.univ (fun j _ => hlim j)
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at hsum
  convert hsum using 1
  funext x
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The corresponding lower-degree normalization when the logarithmic
derivative tends to zero. Nonzero values are needed for the normalization. -/
theorem perturbed_polynomial_min_normalized {α ι : Type*} [Fintype ι] [DecidableEq ι]
    {l : Filter α} (index : ι → ℕ) (hinj : Function.Injective index)
    (c : ι → ℂ) (i₀ : ι) (hmin : ∀ j, c j ≠ 0 → index i₀ ≤ index j)
    {b : α → ι → ℂ} {w : α → ℂ}
    (hb : ∀ j, Tendsto (fun x => b x j) l (𝓝 1))
    (hw : Tendsto w l (𝓝 0)) (hwne : ∀ᶠ x in l, w x ≠ 0) :
    Tendsto (fun x => (∑ j, c j*b x j*(w x)^(index j)) / (w x)^(index i₀))
      l (𝓝 (c i₀)) := by
  have hlim (j : ι) :
      Tendsto (fun x => c j*b x j*((w x)^(index j)/(w x)^(index i₀)))
        l (𝓝 (if j=i₀ then c i₀ else 0)) := by
    by_cases hji : j = i₀
    · subst j
      simp only [ite_true]
      apply (show Tendsto (fun x => c i₀*b x i₀) l (𝓝 (c i₀)) by
        simpa only [mul_one] using (hb i₀).const_mul (c i₀)).congr'
      filter_upwards [hwne] with x hx
      simp [div_self (pow_ne_zero _ hx)]
    · by_cases hc : c j = 0
      · simpa only [hc, zero_mul, if_neg hji] using
          (tendsto_const_nhds (x := (0 : ℂ)) (f := l))
      · have hjlt : index i₀ < index j := lt_of_le_of_ne (hmin j hc)
          (fun h => hji (hinj h.symm))
        have hpow : Tendsto (fun x => (w x)^(index j-index i₀)) l (𝓝 0) := by
          simpa only [zero_pow (Nat.sub_pos_of_lt hjlt).ne'] using hw.pow (index j-index i₀)
        have hratio : Tendsto (fun x => (w x)^(index j)/(w x)^(index i₀)) l (𝓝 0) := by
          apply hpow.congr'
          filter_upwards [hwne] with x hx
          have he : (w x)^(index j) = (w x)^(index j-index i₀)*(w x)^(index i₀) := by
            rw [← pow_add, Nat.sub_add_cancel (hmin j hc)]
          rw [he, mul_div_cancel_right₀ _ (pow_ne_zero _ hx)]
        simpa only [if_neg hji, mul_one, mul_zero] using
          ((hb j).const_mul (c j)).mul hratio
  have hsum := tendsto_finsetSum Finset.univ (fun j _ => hlim j)
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at hsum
  convert hsum using 1
  funext x
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Comparable grouped exponential terms constrain the real part of the
maximum point. The derivative orders of different groups may coincide. -/
theorem logarithmic_strip_of_comparable_groups
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (frequency degree : ι → ℕ) (hinj : Function.Injective frequency)
    {Q : ℝ} (hQ : 1 ≤ Q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : ι → ℂ) (x t : ℝ), 0 < t →
      (∀ i, radialMonomial (degree i : ℤ) (frequency i) t (Real.exp x) ≤ Q*‖u i‖) →
      (∀ i, ‖u i‖ ≤ Q*radialMonomial (degree i : ℤ) (frequency i) t (Real.exp x)) →
      (∑ i, u i = 0) → |x| ≤ C*(1+|Real.log t|) := by
  classical
  let slopes := candidateSlopes frequency (fun i => (degree i : ℤ))
  let K : ℝ := bandConstant (Fintype.card ι) Q
  let A : ℝ := ∑ q ∈ slopes, |(q : ℝ)|
  have hA : 0 ≤ A := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  let C : ℝ := 1 + |Real.log K| + A
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro u x t ht hlo hhi hsum
  obtain ⟨i,j,hij,hijm,hjim⟩ := exists_comparable_monomials u
    (fun i => radialMonomial (degree i : ℤ) (frequency i) t (Real.exp x)) hQ
    (fun i => radialMonomial_pos _ _ ht (Real.exp_pos x)) hlo hhi hsum
  have hK : 0 < K := bandConstant_pos Fintype.card_pos hQ
  have hlog := log_band_of_comparable frequency (fun i => (degree i : ℤ))
    hinj hij ht (Real.exp_pos x) hK hijm hjim
  rw [Real.log_exp] at hlog
  let q : ℚ := candidateSlope frequency (fun i => (degree i : ℤ)) i j
  have hq : q ∈ slopes := candidateSlope_mem _ _ hij
  have hqA : |(q : ℝ)| ≤ A :=
    Finset.single_le_sum (f := fun q : ℚ => |(q : ℝ)|) (fun _ _ => abs_nonneg _) hq
  calc
    |x| ≤ |x-(q : ℝ)*Real.log t| + |(q : ℝ)*Real.log t| := by
      simpa only [sub_add_cancel] using abs_add_le (x-(q : ℝ)*Real.log t) ((q : ℝ)*Real.log t)
    _ ≤ Real.log K + |(q : ℝ)| * |Real.log t| := by rw [abs_mul]; exact add_le_add hlog le_rfl
    _ ≤ |Real.log K| + A * |Real.log t| :=
      add_le_add (le_abs_self _) (mul_le_mul_of_nonneg_right hqA (abs_nonneg _))
    _ ≤ C*(1+|Real.log t|) := by dsimp [C]; nlinarith [abs_nonneg (Real.log K), abs_nonneg (Real.log t)]

/-- The direct Wiman--Valiron balance yields a logarithmic strip once each
group has its proved nonzero normalized limit. This conclusion works for
both the large- and small-logarithmic-derivative normalizations above. -/
theorem eventually_logarithmic_strip_of_normalized_groups
    {α ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {l : Filter α} (frequency degree : ι → ℕ) (hinj : Function.Injective frequency)
    {A : α → ι → ℂ} {z w : α → ℂ} {c : ι → ℂ}
    (hc : ∀ i, c i ≠ 0)
    (hA : ∀ i, Tendsto (fun x => A x i / (w x)^(degree i)) l (𝓝 (c i)))
    (hwne : ∀ᶠ x in l, w x ≠ 0)
    (hbalance : ∀ᶠ x in l, ∑ i, A x i * Complex.exp ((frequency i : ℂ)*z x) = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x in l, |(z x).re| ≤ C*(1+|Real.log ‖w x‖|) := by
  obtain ⟨Q,hQ,hbound⟩ := HelmrathODE.eventually_uniform_multiplier_bounds hc hA
  obtain ⟨C,hC,hstrip⟩ := logarithmic_strip_of_comparable_groups frequency degree hinj hQ
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound,hwne,hbalance] with x hx hxw hxbal
  let u : ι → ℂ := fun i => A x i * Complex.exp ((frequency i : ℂ)*z x)
  have hnorm (i : ι) : ‖u i‖ = ‖A x i/(w x)^(degree i)‖ *
      radialMonomial (degree i : ℤ) (frequency i) ‖w x‖ (Real.exp (z x).re) := by
    simp only [u, norm_mul, Complex.norm_exp, radialMonomial, Int.cast_natCast,
      Real.rpow_natCast, norm_div, norm_pow, ← Real.exp_nat_mul]
    have hwpos : 0 < ‖w x‖ := norm_pos_iff.mpr hxw
    simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
    field_simp
  apply hstrip u (z x).re ‖w x‖ (norm_pos_iff.mpr hxw) ?_ ?_ hxbal
  · intro i
    rw [hnorm]
    have hm := (radialMonomial_pos (degree i : ℤ) (frequency i)
      (norm_pos_iff.mpr hxw) (Real.exp_pos (z x).re)).le
    have hh := mul_le_mul_of_nonneg_right (hx i).1 hm
    simpa only [one_mul,mul_assoc] using hh
  · intro i
    rw [hnorm]
    exact mul_le_mul_of_nonneg_right (hx i).2
      (radialMonomial_pos (degree i : ℤ) (frequency i)
        (norm_pos_iff.mpr hxw) (Real.exp_pos _)).le

end LiWangWen

#print axioms LiWangWen.perturbed_polynomial_max_normalized
#print axioms LiWangWen.perturbed_polynomial_min_normalized
#print axioms LiWangWen.logarithmic_strip_of_comparable_groups
#print axioms LiWangWen.eventually_logarithmic_strip_of_normalized_groups
