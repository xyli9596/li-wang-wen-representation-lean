import LiWangWenWimanValironUpper
import HelmrathRootClustering
import HelmrathBranchSelection
import WimanValironLargeAngular

/-!
# Finite endpoint-root candidates select one linear central-index branch

A bounded logarithmic derivative whose fixed endpoint polynomial tends to
zero approaches the finite moduli of the nonzero roots. Monotonicity then
selects one of these linear branches and removes the finite-logarithmic
exceptional set. No exponential-sum representation is used.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Finset
open scoped Topology

namespace LiWangWen

/-- A nonzero constant term removes the zero root without requiring an
independent lower bound on the variable. -/
theorem eventually_near_positive_rootModuli {α : Type*} {l : Filter α}
    (p : Polynomial ℂ) (hp0 : p.eval 0 ≠ 0) {w : α → ℂ} {K : ℝ}
    (hw : ∀ᶠ x in l, ‖w x‖ ≤ K)
    (hpw : Tendsto (fun x => p.eval (w x)) l (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in l, ∃ c ∈ HelmrathRootClustering.rootModuli p,
      |‖w x‖ - c| < ε := by
  filter_upwards [HelmrathRootClustering.eventually_near_roots p hw hpw hε]
    with x hx
  obtain ⟨ζ, hζ, hclose⟩ := hx
  have hζne : ζ ≠ 0 := by
    intro hzero
    apply hp0
    simpa only [Polynomial.IsRoot, hzero] using hζ
  refine ⟨‖ζ‖, ⟨ζ, ⟨hζ, hζne⟩, rfl⟩, ?_⟩
  exact (abs_norm_sub_norm_le (w x) ζ).trans_lt
    (by simpa only [dist_eq_norm] using hclose)

/-- Finite positive root moduli suffice to prove a genuine linear asymptotic
for a monotone central-index function. -/
theorem linear_asymptotic_of_endpoint_polynomial
    {E : Set ℝ} (hEm : MeasurableSet E)
    (hE : HelmrathExceptionalSet.FiniteLogarithmicMeasure E)
    {ν : ℝ → ℝ} (hν : MonotoneOn ν (Ioi 0))
    (p : Polynomial ℂ) (hp0 : p.eval 0 ≠ 0) {w : ℝ → ℂ} {K : ℝ}
    (hw : ∀ᶠ r : ℝ in atTop ⊓ 𝓟 Eᶜ, ‖w r‖ ≤ K)
    (hnorm : ∀ᶠ r : ℝ in atTop ⊓ 𝓟 Eᶜ, ‖w r‖ = ν r / r)
    (hpw : Tendsto (fun r => p.eval (w r)) (atTop ⊓ 𝓟 Eᶜ) (𝓝 0)) :
    ∃ C : ℝ, 0 < C ∧ Tendsto (fun r : ℝ => ν r / r) atTop (𝓝 C) := by
  classical
  have hp : p ≠ 0 := by
    intro hzero
    exact hp0 (by simp [hzero])
  let S := (HelmrathRootClustering.rootModuli_finite hp).toFinset
  let C : Finset (ℚ × ℝ) := S.image (fun c => ((1 : ℚ), c))
  have hC : ∀ q ∈ C, 0 < q.1 ∧ 0 < q.2 := by
    intro q hq
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hq
    refine ⟨by norm_num, ?_⟩
    exact HelmrathRootClustering.rootModuli_pos
      ((Set.Finite.mem_toFinset _).mp hc)
  have happ : ∀ ε > 0, ∀ᶠ r : ℝ in atTop ⊓ 𝓟 Eᶜ,
      ∃ q ∈ C, |ν r / r^(q.1 : ℝ) - q.2| < ε := by
    intro ε hε
    filter_upwards [hnorm, eventually_near_positive_rootModuli p hp0 hw hpw hε]
      with r hr hn
    obtain ⟨c, hc, hclose⟩ := hn
    refine ⟨((1 : ℚ), c), Finset.mem_image.mpr ⟨c, ?_, rfl⟩, ?_⟩
    · exact (Set.Finite.mem_toFinset _).mpr hc
    · simpa only [Rat.cast_one, Real.rpow_one, ← hr] using hclose
  obtain ⟨q, hq, hlim⟩ := HelmrathBranchSelection.exists_single_power_branch_finset
    C hEm hE hν hC happ
  obtain ⟨c, hc, hqc⟩ := Finset.mem_image.mp hq
  subst q
  refine ⟨c, (hC ((1 : ℚ), c) (Finset.mem_image.mpr ⟨c, hc, rfl⟩)).2, ?_⟩
  simpa only [Rat.cast_one, Real.rpow_one] using hlim

/-- The same conclusion for the genuine central index, with its monotonicity
derived from the entire function rather than imposed as a hypothesis. -/
theorem centralIndex_asymptotic_of_endpoint_polynomial {f : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (hnp : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z)
    {E : Set ℝ} (hEm : MeasurableSet E)
    (hE : HelmrathExceptionalSet.FiniteLogarithmicMeasure E)
    (p : Polynomial ℂ) (hp0 : p.eval 0 ≠ 0) {w : ℝ → ℂ} {K : ℝ}
    (hw : ∀ᶠ r : ℝ in atTop ⊓ 𝓟 Eᶜ, ‖w r‖ ≤ K)
    (hnorm : ∀ᶠ r : ℝ in atTop ⊓ 𝓟 Eᶜ,
      ‖w r‖ = (WimanValiron.centralIndex (WimanValiron.taylorCoeff f) r : ℝ) / r)
    (hpw : Tendsto (fun r => p.eval (w r)) (atTop ⊓ 𝓟 Eᶜ) (𝓝 0)) :
    ∃ C : ℝ, 0 < C ∧ Tendsto (fun r : ℝ =>
      (WimanValiron.centralIndex (WimanValiron.taylorCoeff f) r : ℝ) / r)
      atTop (𝓝 C) := by
  have hfne : f ≠ 0 := by
    intro hzero
    exact hnp ⟨0, by simp [hzero]⟩
  apply linear_asymptotic_of_endpoint_polynomial hEm hE ?_ p hp0 hw hnorm hpw
  intro r hr s hs hrs
  change (WimanValiron.centralIndex (WimanValiron.taylorCoeff f) r : ℝ) ≤
    (WimanValiron.centralIndex (WimanValiron.taylorCoeff f) s : ℝ)
  exact_mod_cast WimanValiron.taylor_centralIndex_monotone hf hfne hr hs hrs

/-- The actual ODE provides bounded logarithmic derivatives and exact WV
balances at near-maximum points deep in one of the two half planes. -/
theorem finiteOrder_solution_deep_WV_data {n : ℕ}
    {P : Fin (n+1) → Polynomial ℂ} {f : ℂ → ℂ}
    (hlead : (P (Fin.last n)).eval 1 ≠ 0)
    (hf : Differentiable ℂ f) (hfo : CRGOrder.FiniteOrder f)
    (hnp : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z)
    (hsol : Solves P f) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ E : Set ℝ, MeasurableSet E ∧
      HelmrathExceptionalSet.FiniteLogarithmicMeasure E ∧ ∃ ζ : ℝ → ℂ,
      (∀ᶠ r : ℝ in atTop ⊓ 𝓟 Eᶜ,
        ‖ζ r‖ = r ∧ r^(1/8 : ℝ)/8 ≤ |(ζ r).re| ∧
        1/r ≤ ‖(WimanValiron.centralIndex (WimanValiron.taylorCoeff f) r : ℂ)/ζ r‖ ∧
        ‖(WimanValiron.centralIndex (WimanValiron.taylorCoeff f) r : ℂ)/ζ r‖ ≤ K) ∧
      (∀ j : Fin (n+1), Tendsto (fun r => WimanValiron.derivativeRatio f
        (WimanValiron.centralIndex (WimanValiron.taylorCoeff f) r) j.val (ζ r))
        (atTop ⊓ 𝓟 Eᶜ) (𝓝 1)) ∧
      ∀ᶠ r : ℝ in atTop ⊓ 𝓟 Eᶜ, ∑ j : Fin (n+1),
        (P j).eval (Complex.exp (ζ r)) * WimanValiron.derivativeRatio f
          (WimanValiron.centralIndex (WimanValiron.taylorCoeff f) r) j.val (ζ r) *
          ((WimanValiron.centralIndex (WimanValiron.taylorCoeff f) r : ℂ)/ζ r)^j.val = 0 := by
  obtain ⟨K,hK,hNu⟩ := finiteOrder_solution_direct_centralIndex_linear_upper
    hlead hf hnp hfo hsol
  obtain ⟨E,hEm,hE,ζ,hζ,hWV⟩ :=
    WimanValiron.exists_deep_nearMaximum_WV_points hf hnp hK hNu
  let g : Filter ℝ := atTop ⊓ 𝓟 Eᶜ
  let N := WimanValiron.centralIndex (WimanValiron.taylorCoeff f)
  have hpos : ∀ᶠ r in g, 0 < r :=
    (eventually_gt_atTop (0 : ℝ)).filter_mono inf_le_left
  have hN : ∀ᶠ r in g, 1 ≤ N r :=
    ((WimanValiron.taylor_centralIndex_tendsto_atTop hf hnp).eventually
      (eventually_ge_atTop 1)).filter_mono inf_le_left
  have hNub : ∀ᶠ r in g, (N r : ℝ) ≤ K*r := hNu.filter_mono inf_le_left
  have hfne : f ≠ 0 := by intro h; exact hnp ⟨0,by simp [h]⟩
  refine ⟨K,hK,E,hEm,hE,ζ,?_,fun j => hWV j.val,?_⟩
  · filter_upwards [hζ,hpos,hN,hNub] with r hz hr hNr hNur
    have hnorm : ‖(N r : ℂ)/ζ r‖ = (N r : ℝ)/r := by
      simp only [norm_div,Complex.norm_natCast,hz.1]
    refine ⟨hz.1,hz.2.2,?_,?_⟩
    · rw [hnorm]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hNr) hr.le
    · rw [hnorm]
      exact (div_le_iff₀ hr).mpr hNur
  · filter_upwards [hζ,hpos,hN] with r hz hr hNr
    have hfζ : f (ζ r) ≠ 0 := norm_pos_iff.mp
      ((half_pos (WimanValiron.circleMaximum_pos hf hfne hr)).trans_le hz.2.1)
    exact ode_balance_of_derivativeRatio hsol
      (norm_pos_iff.mp (hz.1.symm ▸ hr)) (Nat.ne_zero_of_lt hNr) hfζ

/-- The fixed product of the normalized extreme coefficient groups is
extracted from the actual polynomial coefficients. -/
theorem polynomial_exponential_endpoint_product {α : Type*} {n : ℕ}
    {l : Filter α} (P : Fin (n+1) → Polynomial ℂ)
    (hP0 : ∃ j, (P j).coeff 0 ≠ 0)
    {r : α → ℝ} {z w : α → ℂ} {a : α → Fin (n+1) → ℂ}
    {K : ℝ} (hK : 0 ≤ K) (hr : Tendsto r l atTop)
    (hwlo : ∀ᶠ x in l, 1/r x ≤ ‖w x‖)
    (hwup : ∀ᶠ x in l, ‖w x‖ ≤ K)
    (hz : ∀ᶠ x in l, (r x)^((1 : ℝ)/8)/8 ≤ |(z x).re|)
    (ha : ∀ j, Tendsto (fun x => a x j) l (𝓝 1))
    (hbalance : ∀ᶠ x in l, ∑ j,
      (P j).eval (Complex.exp (z x))*a x j*(w x)^j.val = 0) :
    ∃ p : Polynomial ℂ, p.eval 0 ≠ 0 ∧
      Tendsto (fun x => p.eval (w x)) l (𝓝 0) := by
  classical
  let s := exponentialDegreeSupport P
  have hzero : 0 ∈ s := (mem_exponentialDegreeSupport P 0).mpr hP0
  have hs : s.Nonempty := ⟨0,hzero⟩
  let D := s.max' hs
  have hDmem : D ∈ exponentialDegreeSupport P := Finset.max'_mem s hs
  have hdegrees : ∀ j, (P j).natDegree ≤ D := by
    intro j
    by_cases hj : P j = 0
    · simp [hj]
    · exact Finset.le_max' s _ ((mem_exponentialDegreeSupport P _).mpr
        ⟨j,Polynomial.mem_support_iff.mp (Polynomial.natDegree_mem_support_of_nonzero hj)⟩)
  obtain ⟨i₀,hi₀,hmin0⟩ := exists_group_min_index P Fin.val hzero
  obtain ⟨iD,hiD,hminD⟩ := exists_group_min_index P Fin.val hDmem
  let c : Fin (n+1) → Fin (D+1) → ℂ := fun j d => (P j).coeff d.val
  have hbalance' : ∀ᶠ x in l, ∑ d : Fin (D+1), ∑ j,
      c j d*a x j*(w x)^j.val*Complex.exp ((d.val : ℂ)*z x) = 0 := by
    filter_upwards [hbalance] with x hx
    have heval : ∀ j, (P j).eval (Complex.exp (z x)) =
        ∑ d : Fin (D+1), (P j).coeff d.val*(Complex.exp (z x))^d.val := by
      intro j
      exact (Polynomial.eval_eq_sum_range' (n := D+1)
        (by have := hdegrees j; omega) (Complex.exp (z x))).trans
        (Fin.sum_univ_eq_sum_range
          (fun d => (P j).coeff d*(Complex.exp (z x))^d) (D+1)).symm
    simp_rw [heval,Finset.sum_mul] at hx
    rw [Finset.sum_comm] at hx
    convert hx using 1
    apply Finset.sum_congr rfl
    intro d _
    apply Finset.sum_congr rfl
    intro j _
    rw [Complex.exp_nat_mul]
    dsimp only [c]
    ring
  let p := endpointPolynomial (fun j => c j 0) i₀.val *
    endpointPolynomial (fun j => c j (Fin.last D)) iD.val
  refine ⟨p,?_,?_⟩
  · exact endpoint_product_eval_zero_ne c i₀ iD hi₀ hiD hmin0 hminD
  · exact endpoint_product_tendsto_zero c i₀ iD hmin0 hminD
      hK hr hwlo hwup hz ha hbalance'

/-- The direct WV argument selects a positive constant, even after removing
the exceptional set. No separate linear lower-bound argument is used. -/
theorem lemma_5_1_centralIndex_asymptotic {n : ℕ}
    {P : Fin (n+1) → Polynomial ℂ} {f : ℂ → ℂ}
    (hlead : P (Fin.last n) = 1)
    (hf : Differentiable ℂ f) (hfo : CRGOrder.FiniteOrder f)
    (hnp : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z)
    (hsol : Solves P f) :
    ∃ C : ℝ, 0 < C ∧ Tendsto (fun r : ℝ =>
      (WimanValiron.centralIndex (WimanValiron.taylorCoeff f) r : ℝ)/r)
      atTop (𝓝 C) := by
  have hleval : (P (Fin.last n)).eval 1 ≠ 0 := by simp [hlead]
  obtain ⟨K,hK,E,hEm,hE,ζ,hζ,hWV,hbalance⟩ :=
    finiteOrder_solution_deep_WV_data hleval hf hfo hnp hsol
  let N := WimanValiron.centralIndex (WimanValiron.taylorCoeff f)
  let w : ℝ → ℂ := fun r => (N r : ℂ)/ζ r
  obtain ⟨p,hp0,hpw⟩ := polynomial_exponential_endpoint_product P
    ⟨Fin.last n,by simp [hlead]⟩ hK
    (show Tendsto (id : ℝ → ℝ) (atTop ⊓ 𝓟 Eᶜ) atTop from
      tendsto_id.mono_left inf_le_left)
    (hζ.mono (fun _ h => h.2.2.1)) (hζ.mono (fun _ h => h.2.2.2))
    (hζ.mono (fun _ h => h.2.1)) hWV hbalance
  apply centralIndex_asymptotic_of_endpoint_polynomial hf hnp hEm hE p hp0
    (hζ.mono (fun _ h => h.2.2.2)) ?_ hpw
  filter_upwards [hζ] with r hr
  simp only [norm_div,Complex.norm_natCast,hr.1]

/-- Lemma 5.1 follows from the single-branch asymptotic by the growth bridge. -/
theorem lemma_5_1_via_single_branch {n : ℕ}
    {P : Fin (n+1) → Polynomial ℂ} {f : ℂ → ℂ}
    (hlead : P (Fin.last n) = 1)
    (hf : Differentiable ℂ f) (hfo : CRGOrder.FiniteOrder f)
    (hnp : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z)
    (hsol : Solves P f) :
    CRGOrder.IsOrder f 1 ∧ LevinGrowth.FinitePositiveType f 1 := by
  obtain ⟨C,hC,hlim⟩ := lemma_5_1_centralIndex_asymptotic hlead hf hfo hnp hsol
  have hfne : f ≠ 0 := by intro h; exact hnp ⟨0,by simp [h]⟩
  apply WimanValiron.order_and_type_of_centralIndex_linear_bounds hf hfne
    (c := C/2) (C := 2*C) (by positivity) (by positivity)
  filter_upwards [hlim.eventually (eventually_gt_nhds (show C/2 < C by linarith)),
    hlim.eventually (eventually_lt_nhds (show C < 2*C by linarith)),
    eventually_gt_atTop (0 : ℝ)] with r hlo hup hr
  exact ⟨((lt_div_iff₀ hr).mp hlo).le, ((div_lt_iff₀ hr).mp hup).le⟩

#print axioms eventually_near_positive_rootModuli
#print axioms linear_asymptotic_of_endpoint_polynomial
#print axioms centralIndex_asymptotic_of_endpoint_polynomial
#print axioms finiteOrder_solution_deep_WV_data
#print axioms polynomial_exponential_endpoint_product
#print axioms lemma_5_1_centralIndex_asymptotic
#print axioms lemma_5_1_via_single_branch

end LiWangWen
