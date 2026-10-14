import LiWangWenVerticalGrowth
import WimanValironFiniteOrder
import LiWangWenWimanValironGroups
import LiWangWenWimanValironLower

/-!
# The upper-bound part of a direct Wiman--Valiron repair

A logarithmic strip for maximum points only when `nu(r)/r` is large is
sufficient. Choose a good outer radius in `[2*r,3*r]` and compare genuine
maximum terms there. This proves a global linear central-index bound without
assuming a selected Newton branch or an exponential-sum representation.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace LiWangWen

/-- A conditional maximum-modulus bound at large central-index ratios already
forces an unconditional linear central-index bound. -/
theorem centralIndex_linear_of_large_ratio_circle_bound {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hne : f ≠ 0) {E : Set ℝ}
    (hE : LevinDensity.ZeroRadialDensity E) {Q D : ℝ} (hQ : 0 ≤ Q) (hD : 0 ≤ D)
    (hM : ∀ᶠ s : ℝ in atTop, s ∉ E →
      Q*s < (WimanValiron.centralIndex (WimanValiron.taylorCoeff f) s : ℝ) →
      WimanValiron.circleMaximum f s ≤ Real.exp (D*s)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ r : ℝ in atTop,
      (WimanValiron.centralIndex (WimanValiron.taylorCoeff f) r : ℝ) ≤ B*r := by
  let μ := WimanValiron.maximumTerm (WimanValiron.taylorCoeff f) 1
  have hμ : 0 < μ := WimanValiron.maximumTerm_pos
    (WimanValiron.taylor_admissible hf hne zero_lt_one)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let L := (3*D+|Real.log μ|)/Real.log 2
  have hL : 0 ≤ L := div_nonneg (by positivity) hlog.le
  obtain ⟨R,hR⟩ := eventually_atTop.mp hM
  refine ⟨max (3*Q) L, le_max_of_le_left (by positivity), ?_⟩
  filter_upwards [HelmrathExceptionalSet.exists_good_radius hE
    (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (2 : ℝ) < 3),
    eventually_ge_atTop (max 1 R)] with r hs hr
  have hr1 : 1 ≤ r := (le_max_left _ _).trans hr
  have hrpos : 0 < r := zero_lt_one.trans_le hr1
  by_cases hsmall : (WimanValiron.centralIndex (WimanValiron.taylorCoeff f) r : ℝ) ≤ (3*Q)*r
  · exact hsmall.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hrpos.le)
  obtain ⟨s,hs,hsE⟩ := hs
  have hrs : r ≤ s := by linarith [hs.1]
  have hspos : 0 < s := hrpos.trans_le hrs
  have ha := WimanValiron.taylor_admissible hf hne hrpos
  have has := WimanValiron.taylor_admissible hf hne hspos
  have hmono : (WimanValiron.centralIndex (WimanValiron.taylorCoeff f) r : ℝ) ≤
      WimanValiron.centralIndex (WimanValiron.taylorCoeff f) s := by
    exact_mod_cast WimanValiron.centralIndex_le ha has hrs
  have hlarge : Q*s < (WimanValiron.centralIndex (WimanValiron.taylorCoeff f) s : ℝ) := by
    have hq := mul_le_mul_of_nonneg_left hs.2 hQ
    have hstrict := lt_of_not_ge hsmall
    nlinarith
  have hMs := hR s (((le_max_right _ _).trans hr).trans hrs) hsE hlarge
  have hμr : μ ≤ WimanValiron.maximumTerm (WimanValiron.taylorCoeff f) r :=
    WimanValiron.maximumTerm_le
      (WimanValiron.taylor_admissible hf hne zero_lt_one) ha hr1
  have hratio : (2 : ℝ) ≤ s/r := (le_div_iff₀ hrpos).mpr hs.1
  have hmax : μ*(2 : ℝ)^WimanValiron.centralIndex (WimanValiron.taylorCoeff f) r ≤
      Real.exp (3*D*r) := by
    calc
      _ ≤ WimanValiron.maximumTerm (WimanValiron.taylorCoeff f) r *
          (s/r)^WimanValiron.centralIndex (WimanValiron.taylorCoeff f) r :=
        mul_le_mul hμr (pow_le_pow_left₀ (by norm_num) hratio _)
          (by positivity) (WimanValiron.maximumTerm_pos ha).le
      _ ≤ WimanValiron.maximumTerm (WimanValiron.taylorCoeff f) s :=
        WimanValiron.maximumTerm_ge_radius_ratio ha has
      _ ≤ WimanValiron.circleMaximum f s :=
        WimanValiron.maximumTerm_le_circleMaximum hf hspos
      _ ≤ Real.exp (D*s) := hMs
      _ ≤ Real.exp (3*D*r) := by apply Real.exp_le_exp.mpr; nlinarith [hs.2]
  have hleftpos : 0 < μ*(2 : ℝ)^WimanValiron.centralIndex (WimanValiron.taylorCoeff f) r := by positivity
  have hlogs := Real.log_le_log hleftpos hmax
  rw [Real.log_mul hμ.ne' (by positivity), Real.log_pow, Real.log_exp] at hlogs
  have hLin : (WimanValiron.centralIndex (WimanValiron.taylorCoeff f) r : ℝ) ≤ L*r := by
    apply le_of_mul_le_mul_right (a := Real.log 2) _ hlog
    calc
      _ ≤ 3*D*r-Real.log μ := by linarith
      _ ≤ (3*D+|Real.log μ|)*r := by
        nlinarith [neg_le_abs (Real.log μ), abs_nonneg (Real.log μ)]
      _ = (L*r)*Real.log 2 := by dsimp [L]; field_simp
  exact hLin.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hrpos.le)

/-- The direct WV logarithmic-strip conclusion combines with vertical Floquet
growth to bound the central index linearly, with no branch-limit hypothesis. -/
theorem centralIndex_linear_of_large_ratio_maximum_strip {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hne : f ≠ 0) {E : Set ℝ}
    (hE : LevinDensity.ZeroRadialDensity E) (hv : VerticalPowerBound f)
    {Q C : ℝ} (hQ : 0 ≤ Q) (hC : 0 ≤ C)
    (hstrip : ∀ᶠ r : ℝ in atTop, r ∉ E →
      Q*r < (WimanValiron.centralIndex (WimanValiron.taylorCoeff f) r : ℝ) →
      ∃ z : ℂ, ‖z‖ = r ∧ ‖f z‖ = WimanValiron.circleMaximum f r ∧
        |z.re| ≤ C*(1+Real.log r)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ r : ℝ in atTop,
      (WimanValiron.centralIndex (WimanValiron.taylorCoeff f) r : ℝ) ≤ B*r := by
  obtain ⟨D,hD,hbound⟩ := hv.logarithmic_strip hC
  apply centralIndex_linear_of_large_ratio_circle_bound hf hne hE hQ hD
  filter_upwards [hstrip,hbound] with r hr hb hrE hrQ
  obtain ⟨z,hzr,hzM,hx⟩ := hr hrE hrQ
  rw [← hzM]
  exact hb z hzr.le hx

/-- The upper growth conclusion of the direct WV repair. -/
theorem exponentialBound_of_large_ratio_maximum_strip {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hne : f ≠ 0) {E : Set ℝ}
    (hE : LevinDensity.ZeroRadialDensity E) (hv : VerticalPowerBound f)
    {Q C : ℝ} (hQ : 0 ≤ Q) (hC : 0 ≤ C)
    (hstrip : ∀ᶠ r : ℝ in atTop, r ∉ E →
      Q*r < (WimanValiron.centralIndex (WimanValiron.taylorCoeff f) r : ℝ) →
      ∃ z : ℂ, ‖z‖ = r ∧ ‖f z‖ = WimanValiron.circleMaximum f r ∧
        |z.re| ≤ C*(1+Real.log r)) : ExponentialBound f := by
  obtain ⟨B,hB,hν⟩ := centralIndex_linear_of_large_ratio_maximum_strip hf hne hE hv hQ hC hstrip
  exact WimanValiron.exponentialBound_of_centralIndex_eventually_le hf hB hν

/-- A polynomial bound on the central index converts a logarithmic-ratio
strip to a logarithmic-radius strip on the large-ratio range. -/
theorem centralIndex_linear_of_large_ratio_log_strip {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hne : f ≠ 0) {E : Set ℝ}
    (hE : LevinDensity.ZeroRadialDensity E) (hv : VerticalPowerBound f)
    {Q C A : ℝ} {k : ℕ} (hQ : 1 ≤ Q) (hC : 0 ≤ C) (_hA : 0 ≤ A)
    (hpoly : ∀ᶠ r : ℝ in atTop,
      (WimanValiron.centralIndex (WimanValiron.taylorCoeff f) r : ℝ) ≤ A*r^k)
    (hstrip : ∀ᶠ r : ℝ in atTop, r ∉ E →
      Q*r < (WimanValiron.centralIndex (WimanValiron.taylorCoeff f) r : ℝ) →
      ∃ z : ℂ, ‖z‖ = r ∧ ‖f z‖ = WimanValiron.circleMaximum f r ∧
        |z.re| ≤ C*(1+|Real.log
          ((WimanValiron.centralIndex (WimanValiron.taylorCoeff f) r : ℝ)/r)|)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ r : ℝ in atTop,
      (WimanValiron.centralIndex (WimanValiron.taylorCoeff f) r : ℝ) ≤ B*r := by
  let A' := max 1 A
  have hA' : 0 < A' := zero_lt_one.trans_le (le_max_left _ _)
  have hlogA : 0 ≤ Real.log A' := Real.log_nonneg (le_max_left _ _)
  let L := 1+Real.log A'+(k : ℝ)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  apply centralIndex_linear_of_large_ratio_maximum_strip hf hne hE hv
    (zero_le_one.trans hQ) (C := C*(1+L)) (by positivity)
  filter_upwards [hstrip,hpoly,eventually_ge_atTop (1 : ℝ)] with r hs hp hr hrE hrQ
  have hrpos : 0 < r := zero_lt_one.trans_le hr
  let q := (WimanValiron.centralIndex (WimanValiron.taylorCoeff f) r : ℝ)/r
  have hq1 : 1 ≤ q := by
    have hh := (lt_div_iff₀ hrpos).mpr hrQ
    exact hQ.trans hh.le
  have hqpos : 0 < q := zero_lt_one.trans_le hq1
  have hqpoly : q ≤ A'*r^k := by
    have hn : 0 ≤ (WimanValiron.centralIndex (WimanValiron.taylorCoeff f) r : ℝ) := by positivity
    have hh : q ≤ (WimanValiron.centralIndex (WimanValiron.taylorCoeff f) r : ℝ) :=
      div_le_self hn hr
    exact hh.trans (hp.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)))
  have hlogr : 0 ≤ Real.log r := Real.log_nonneg hr
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hlogbound : Real.log q ≤ L*(1+Real.log r) := by
    have hh := Real.log_le_log hqpos hqpoly
    rw [Real.log_mul hA'.ne' (pow_pos hrpos k).ne', Real.log_pow] at hh
    dsimp only [L]
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  obtain ⟨z,hzr,hzM,hx⟩ := hs hrE hrQ
  refine ⟨z,hzr,hzM,?_⟩
  have hx' : |z.re| ≤ C*(1+Real.log q) := by
    simpa only [← show q = (WimanValiron.centralIndex (WimanValiron.taylorCoeff f) r : ℝ)/r from rfl,
      abs_of_nonneg hlogq] using hx
  apply hx'.trans
  have hh := mul_le_mul_of_nonneg_left hlogbound hC
  nlinarith

/-- The actual ODE at actual maximum points gives a uniform logarithmic strip
whenever the central-index ratio exceeds one fixed threshold. -/
theorem solution_large_ratio_maximum_log_strip {n : ℕ}
    {P : Fin (n+1) → Polynomial ℂ} {f : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (hnp : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z)
    (hP : ∃ j, P j ≠ 0) (hsol : Solves P f) :
    ∃ E : Set ℝ, MeasurableSet E ∧ HelmrathExceptionalSet.FiniteLogarithmicMeasure E ∧
      ∃ Q : ℝ, 1 ≤ Q ∧ ∃ C : ℝ, 0 < C ∧
      ∀ᶠ r : ℝ in atTop, r ∉ E →
        Q*r < (WimanValiron.centralIndex (WimanValiron.taylorCoeff f) r : ℝ) →
        ∃ z : ℂ, ‖z‖ = r ∧ ‖f z‖ = WimanValiron.circleMaximum f r ∧
          |z.re| ≤ C*(1+|Real.log
            ((WimanValiron.centralIndex (WimanValiron.taylorCoeff f) r : ℝ)/r)|) := by
  classical
  obtain ⟨E,hEm,hE,_hbot,z,hmax,hWV⟩ :=
    WimanValiron.wimanValiron_at_maximum_points hf hnp
      (δ := (1 : ℝ)/16) (by norm_num) (by norm_num)
  let g : Filter ℝ := atTop ⊓ 𝓟 Eᶜ
  let N := WimanValiron.centralIndex (WimanValiron.taylorCoeff f)
  let w : ℝ → ℂ := fun r => (N r : ℂ)/z r
  have hpos : ∀ᶠ r in g, 0 < r :=
    (eventually_gt_atTop (0 : ℝ)).filter_mono inf_le_left
  have hN : ∀ᶠ r in g, 1 ≤ N r :=
    ((WimanValiron.taylor_centralIndex_tendsto_atTop hf hnp).eventually
      (eventually_ge_atTop 1)).filter_mono inf_le_left
  have hfne : f ≠ 0 := by intro h; exact hnp ⟨0,by simp [h]⟩
  have hbalance : ∀ᶠ r in g, ∑ j : Fin (n+1), (P j).eval (Complex.exp (z r))*
      WimanValiron.derivativeRatio f (N r) j.val (z r)*(w r)^j.val = 0 := by
    filter_upwards [hpos,hN] with r hr hNr
    exact ode_balance_of_derivativeRatio hsol
      (norm_pos_iff.mp ((hmax r hr).1.symm ▸ hr)) (Nat.ne_zero_of_lt hNr)
      (norm_pos_iff.mp ((hmax r hr).2.symm ▸ WimanValiron.circleMaximum_pos hf hfne hr))
  obtain ⟨Q,hQ,C,hC,hstrip⟩ := exponential_ode_large_w_strip_threshold P hP
    Fin.val Fin.val_injective (fun j => (hWV j.val).2) hbalance
  refine ⟨E,hEm,hE,Q,hQ,C,hC,?_⟩
  apply Filter.eventually_inf_principal.mp
  filter_upwards [hstrip,hpos] with r hs hr hlarge
  have hnorm : ‖w r‖ = (N r : ℝ)/r := by
    simp only [w,norm_div,Complex.norm_natCast,(hmax r hr).1]
  have hq : Q ≤ ‖w r‖ := by
    rw [hnorm]
    exact ((lt_div_iff₀ hr).mpr hlarge).le
  refine ⟨z r,(hmax r hr).1,(hmax r hr).2,?_⟩
  have hh := hs hq
  rw [hnorm] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left
    (by linarith [le_abs_self (Real.log ((N r : ℝ)/r))]) hC.le)

/-- The direct WV upper bound for a finite-order entire ODE solution. The
proof uses the coefficient-group strip and periodic Floquet growth, without
classifying the periodic coefficients or assuming any Newton branch limit. -/
theorem finiteOrder_solution_direct_centralIndex_linear_upper {n : ℕ}
    {P : Fin (n+1) → Polynomial ℂ} {f : ℂ → ℂ}
    (hlead : (P (Fin.last n)).eval 1 ≠ 0)
    (hf : Differentiable ℂ f)
    (hnp : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z)
    (hfo : CRGOrder.FiniteOrder f) (hsol : Solves P f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ r : ℝ in atTop,
      (WimanValiron.centralIndex (WimanValiron.taylorCoeff f) r : ℝ) ≤ B*r := by
  have hP : ∃ j, P j ≠ 0 :=
    ⟨Fin.last n, fun h => hlead (by simp [h])⟩
  have hfne : f ≠ 0 := by intro h; exact hnp ⟨0,by simp [h]⟩
  obtain ⟨E,hEm,hE,Q,hQ,C,hC,hstrip⟩ :=
    solution_large_ratio_maximum_log_strip hf hnp hP hsol
  obtain ⟨k,A,hA,hpoly⟩ := WimanValiron.centralIndex_polynomial_bound hf hfne hfo
  exact centralIndex_linear_of_large_ratio_log_strip hf hfne
    (HelmrathExceptionalSet.zero_density_of_finite_logarithmic_measure hEm hE)
    (finiteOrder_solution_verticalPowerBound hlead hf hfo hsol) hQ hC.le hA
    ((eventually_ge_atTop (1 : ℝ)).mono (fun r hr => hpoly r hr)) hstrip

/-- Finite order improves to finite exponential type by the direct WV route. -/
theorem finiteOrder_solution_direct_exponentialBound {n : ℕ}
    {P : Fin (n+1) → Polynomial ℂ} {f : ℂ → ℂ}
    (hlead : (P (Fin.last n)).eval 1 ≠ 0)
    (hf : Differentiable ℂ f)
    (hnp : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z)
    (hfo : CRGOrder.FiniteOrder f) (hsol : Solves P f) : ExponentialBound f := by
  obtain ⟨B,hB,hν⟩ :=
    finiteOrder_solution_direct_centralIndex_linear_upper hlead hf hnp hfo hsol
  exact WimanValiron.exponentialBound_of_centralIndex_eventually_le hf hB hν

#print axioms solution_large_ratio_maximum_log_strip
#print axioms finiteOrder_solution_direct_centralIndex_linear_upper
#print axioms finiteOrder_solution_direct_exponentialBound

#print axioms centralIndex_linear_of_large_ratio_circle_bound
#print axioms centralIndex_linear_of_large_ratio_maximum_strip
#print axioms exponentialBound_of_large_ratio_maximum_strip
#print axioms centralIndex_linear_of_large_ratio_log_strip

end LiWangWen
