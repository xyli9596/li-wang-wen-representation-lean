import HelmrathRootClustering

/-!
# Newton root candidates from an actual polynomial differential equation

The actual Wiman--Valiron substitution yields both the coarse Newton bands
and the vanishing polynomial residual required for their root refinement.
-/

set_option autoImplicit false
noncomputable section
open Filter Finset Set
open scoped Topology

namespace HelmrathODE
open HelmrathNewtonBranches HelmrathRootClustering WimanValiron

theorem factor_scaled_term (p : Polynomial ℂ) (j k : ℕ) {z w b : ℂ} (hz : z ≠ 0) :
    p.eval z * z^k * w^j * b =
      (p.eval z / z^p.natDegree * b) * z^(p.natDegree+k) * w^j := by
  rw [pow_add]
  field_simp

/-- The central index approaches a finite set of positive rational-power
root-modulus candidates. No limiting exponent or constant is assumed. -/
theorem polynomial_ode_root_candidates
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (index : ι → ℕ) (hinj : Function.Injective index) (n : ℕ)
    (hindex : ∀ i, index i ≤ n) (a : ι → Polynomial ℂ) (ha : ∀ i, a i ≠ 0)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnp : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z)
    (hode : ∀ z, ∑ i, (a i).eval z * iteratedDeriv (index i) f z = 0) :
    ∃ E : Set ℝ, MeasurableSet E ∧ HelmrathExceptionalSet.FiniteLogarithmicMeasure E ∧
      (atTop ⊓ 𝓟 Eᶜ).NeBot ∧ ∃ C : Finset (ℚ × ℝ),
        (∀ p ∈ C, 0 < p.1 ∧ 0 < p.2) ∧ ∀ ε : ℝ, 0 < ε →
          ∀ᶠ r in atTop ⊓ 𝓟 Eᶜ, ∃ p ∈ C,
            |(centralIndex (taylorCoeff f) r : ℝ) / r^(p.1 : ℝ) - p.2| < ε := by
  classical
  obtain ⟨E, hEm, hE, hnebot, z, hz, hratio⟩ :=
    wimanValiron_at_maximum_points hf hnp (δ := (1 : ℝ)/16) (by norm_num) (by norm_num)
  let l : Filter ℝ := atTop ⊓ 𝓟 Eᶜ
  let N : ℝ → ℕ := fun r => centralIndex (taylorCoeff f) r
  have hr : Tendsto (fun r : ℝ => r) l atTop := tendsto_id.mono_left inf_le_left
  have hpos : ∀ᶠ r in l, 0 < r := hr.eventually (eventually_gt_atTop 0)
  have hzn : Tendsto (fun r => ‖z r‖) l atTop := by
    apply hr.congr'
    filter_upwards [hpos] with r hr
    exact (hz r hr).1.symm
  let b : ℝ → ι → ℂ := fun r i =>
    (a i).eval (z r) / (z r)^(a i).natDegree * derivativeRatio f (N r) (index i) (z r)
  have hblim : ∀ i, Tendsto (fun r => b r i) l (𝓝 (a i).leadingCoeff) := by
    intro i
    simpa only [mul_one] using
      (polynomial_normalized_tendsto (a i) (ha i) hzn).mul (hratio (index i)).2
  obtain ⟨Q, hQ, hb⟩ := eventually_uniform_multiplier_bounds
    (fun i => Polynomial.leadingCoeff_ne_zero.mpr (ha i)) hblim
  let u : ℝ → ι → ℂ := fun r i => (a i).eval (z r) * (z r)^(n-index i) *
    (N r : ℂ)^(index i) * derivativeRatio f (N r) (index i) (z r)
  have hN : Tendsto N l atTop := (taylor_centralIndex_tendsto_atTop hf hnp).mono_left inf_le_left
  have hNr : Tendsto (fun r => (N r : ℝ)) l atTop := tendsto_natCast_atTop_atTop.comp hN
  have hfne : f ≠ 0 := by intro h; exact hnp ⟨0, by simp [h]⟩
  have hbalance : ∀ᶠ r in l,
      (∀ i, radialMonomial (scaledDegree index a n i) (index i) r (N r : ℝ) ≤ Q * ‖u r i‖) ∧
      (∀ i, ‖u r i‖ ≤ Q * radialMonomial (scaledDegree index a n i) (index i) r (N r : ℝ)) ∧
      ∑ i, u r i = 0 := by
    filter_upwards [hpos, hb, hN.eventually (eventually_ge_atTop 1)] with r hr hb hNr
    have hzr := (hz r hr).1
    have hNpos : (0 : ℝ) < N r := by exact_mod_cast hNr
    have hterm : ∀ i, ‖u r i‖ = ‖b r i‖ *
        radialMonomial (scaledDegree index a n i) (index i) r (N r : ℝ) := by
      intro i
      exact norm_scaled_term (a i) (index i) (n-index i) (z r) (N r : ℂ)
        (derivativeRatio f (N r) (index i) (z r)) hr hzr (by simp)
    refine ⟨?_, ?_, ?_⟩
    · intro i
      rw [hterm i]
      have hm := (radialMonomial_pos (scaledDegree index a n i) (index i) hr hNpos).le
      have h := mul_le_mul_of_nonneg_right (hb i).1 hm
      simpa only [one_mul, mul_assoc] using h
    · intro i
      rw [hterm i]
      exact mul_le_mul_of_nonneg_right (hb i).2
        (radialMonomial_pos (scaledDegree index a n i) (index i) hr hNpos).le
    · have hfz : f (z r) ≠ 0 := norm_pos_iff.mp (by
        rw [(hz r hr).2]
        exact circleMaximum_pos hf hfne hr)
      exact scaled_ode_sum index n hindex a (norm_pos_iff.mp (hzr.symm ▸ hr)) hfz
        (Nat.ne_zero_of_lt hNr) (hode (z r))
  let K : ℝ := bandConstant (Fintype.card ι) Q
  have hK : 0 < K := bandConstant_pos Fintype.card_pos hQ
  let degree : ι → ℕ := fun i => (a i).natDegree + (n-index i)
  let c : ι → ℂ := fun i => (a i).leadingCoeff
  have hc : ∀ i, c i ≠ 0 := fun i => Polynomial.leadingCoeff_ne_zero.mpr (ha i)
  let S : Finset ℚ := (candidateSlopes index (scaledDegree index a n)).filter (0 < ·)
  have hbands := eventually_positive_newton_power_bands index (scaledDegree index a n)
    hinj hQ hr hNr hbalance
  have hbands' : ∀ᶠ r in l, ∃ q ∈ S,
      ‖z r‖^(q : ℝ) ≤ K*‖(N r : ℂ)‖ ∧ ‖(N r : ℂ)‖ ≤ K*‖z r‖^(q : ℝ) := by
    filter_upwards [hbands, hpos] with r hrband hrpos
    obtain ⟨q, hq, hqp, hlo, hhi⟩ := hrband
    refine ⟨q, Finset.mem_filter.mpr ⟨hq,hqp⟩, ?_⟩
    simpa only [(hz r hrpos).1, Complex.norm_natCast] using And.intro hlo hhi
  have hbalance' : ∀ᶠ r in l,
      ∑ i, b r i * (z r)^(degree i) * (N r : ℂ)^(index i) = 0 := by
    filter_upwards [hbalance, hpos] with r hrbal hrpos
    have hzne : z r ≠ 0 := norm_pos_iff.mp ((hz r hrpos).1.symm ▸ hrpos)
    have hterm : ∀ i, u r i = b r i * (z r)^(degree i) * (N r : ℂ)^(index i) := by
      intro i
      exact factor_scaled_term (a i) (index i) (n-index i) hzne
    simpa only [hterm] using hrbal.2.2
  let T : Set (ℚ × ℝ) := rootCandidates index degree c S
  have hT : T.Finite := rootCandidates_finite index degree hinj c hc S
  refine ⟨E,hEm,hE,hnebot,hT.toFinset,?_,?_⟩
  · intro p hp
    have hpT : p ∈ T := hT.mem_toFinset.mp hp
    obtain ⟨hq, hcroot⟩ := (mem_rootCandidates index degree c S p.1 p.2).mp hpT
    exact ⟨(Finset.mem_filter.mp hq).2, rootModuli_pos hcroot⟩
  · intro ε hε
    have happ := finite_bands_root_approximation index degree c S hK hzn hblim
      hbands' hbalance' hε
    filter_upwards [happ,hpos] with r hrapp hrpos
    obtain ⟨p,hp,hclose⟩ := hrapp
    refine ⟨p,hT.mem_toFinset.mpr hp,?_⟩
    simpa only [(hz r hrpos).1, Complex.norm_natCast] using hclose

end HelmrathODE

#print axioms HelmrathODE.factor_scaled_term
#print axioms HelmrathODE.polynomial_ode_root_candidates
