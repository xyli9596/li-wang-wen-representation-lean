import HelmrathNewtonBranches
import HelmrathODECoefficients
import WimanValironLimits

/-!
# Actual polynomial differential equations force finite Newton power bands

This module applies the proved Wiman--Valiron theorem at selected maximum
points of an entire nonpolynomial solution of a polynomial-coefficient linear
ODE. The derivative approximations, coefficient leading-term estimates, good
points, and exceptional set are all conclusions, rather than extra inputs.

The conclusion is eventual membership in finitely many positive rational
power bands. Selection of one Newton root branch, the sharper asymptotic
central-index formula, and integration to the maximum modulus remain distinct
steps; the theorem below does not claim those stronger conclusions.
-/

set_option autoImplicit false
noncomputable section
open Filter Finset Set
open scoped Topology

namespace HelmrathODE
open HelmrathNewtonBranches WimanValiron

/-- Polynomial degree after multiplication of the ODE by `z^n / f(z)`. -/
def scaledDegree {ι : Type*} (index : ι → ℕ) (a : ι → Polynomial ℂ) (n : ℕ) (i : ι) : ℤ :=
  ((a i).natDegree + (n - index i) : ℕ)

/-- The norm of an exact substituted term is a radial Newton monomial times
its normalized polynomial and derivative multiplier. -/
theorem norm_scaled_term (p : Polynomial ℂ) (j k : ℕ) (z w b : ℂ)
    {r v : ℝ} (hr : 0 < r) (hz : ‖z‖ = r) (hw : ‖w‖ = v) :
    ‖p.eval z * z^k * w^j * b‖ =
      ‖p.eval z / z^p.natDegree * b‖ *
        radialMonomial ((p.natDegree + k : ℕ) : ℤ) j r v := by
  simp only [norm_mul, norm_pow, norm_div, hz, hw, radialMonomial,
    Int.cast_natCast, Real.rpow_natCast, pow_add]
  field_simp

/-- Exact substitution for a sparse finite collection of derivative orders. -/
theorem scaled_ode_sum {ι : Type*} [Fintype ι] (index : ι → ℕ) (n : ℕ)
    (hindex : ∀ i, index i ≤ n) (a : ι → Polynomial ℂ)
    {f : ℂ → ℂ} {z : ℂ} {N : ℕ} (hz : z ≠ 0) (hfz : f z ≠ 0) (hN : N ≠ 0)
    (hode : ∑ i, (a i).eval z * iteratedDeriv (index i) f z = 0) :
    ∑ i, (a i).eval z * z^(n-index i) * (N : ℂ)^(index i) *
      derivativeRatio f N (index i) z = 0 := by
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  have hterm : ∀ i, (a i).eval z * z^(n-index i) * (N : ℂ)^(index i) *
      derivativeRatio f N (index i) z =
      ((a i).eval z * iteratedDeriv (index i) f z) * (z^n / f z) := by
    intro i
    have hpow : z^n = z^(n-index i) * z^(index i) := by
      rw [← pow_add, Nat.sub_add_cancel (hindex i)]
    rw [hpow, derivativeRatio]
    field_simp
  simp_rw [hterm]
  rw [← sum_mul, hode, zero_mul]

/-- The actual central index of an entire nonpolynomial ODE solution lies,
outside a constructed finite-logarithmic-measure exceptional set, in finitely
many positive rational Newton power bands. The only inputs concern the
function and its polynomial differential equation. -/
theorem polynomial_ode_newton_power_bands
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (index : ι → ℕ) (hinj : Function.Injective index) (n : ℕ)
    (hindex : ∀ i, index i ≤ n) (a : ι → Polynomial ℂ) (ha : ∀ i, a i ≠ 0)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnp : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z)
    (hode : ∀ z, ∑ i, (a i).eval z * iteratedDeriv (index i) f z = 0) :
    ∃ E : Set ℝ, MeasurableSet E ∧ HelmrathExceptionalSet.FiniteLogarithmicMeasure E ∧
      (atTop ⊓ 𝓟 Eᶜ).NeBot ∧ ∃ K : ℝ, 0 < K ∧
        ∀ᶠ r in atTop ⊓ 𝓟 Eᶜ,
          ∃ q ∈ candidateSlopes index (scaledDegree index a n), 0 < q ∧
            r^(q : ℝ) ≤ K * (centralIndex (taylorCoeff f) r : ℝ) ∧
            (centralIndex (taylorCoeff f) r : ℝ) ≤ K * r^(q : ℝ) := by
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
  refine ⟨E, hEm, hE, hnebot, bandConstant (Fintype.card ι) Q,
    bandConstant_pos Fintype.card_pos hQ, ?_⟩
  exact eventually_positive_newton_power_bands index (scaledDegree index a n) hinj hQ hr hNr hbalance

/-- Equal polynomial-coefficient degrees make every candidate slope equal to
one. Consequently the actual central index has two-sided linear bounds off
the constructed exceptional set, without assuming a power asymptotic. -/
theorem common_degree_polynomial_ode_linear_bands
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (index : ι → ℕ) (hinj : Function.Injective index) (n : ℕ)
    (hindex : ∀ i, index i ≤ n) (a : ι → Polynomial ℂ) (ha : ∀ i, a i ≠ 0)
    (D : ℕ) (hdegree : ∀ i, (a i).natDegree = D)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnp : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z)
    (hode : ∀ z, ∑ i, (a i).eval z * iteratedDeriv (index i) f z = 0) :
    ∃ E : Set ℝ, MeasurableSet E ∧ HelmrathExceptionalSet.FiniteLogarithmicMeasure E ∧
      (atTop ⊓ 𝓟 Eᶜ).NeBot ∧ ∃ K : ℝ, 0 < K ∧
        ∀ᶠ r in atTop ⊓ 𝓟 Eᶜ,
          r ≤ K * (centralIndex (taylorCoeff f) r : ℝ) ∧
          (centralIndex (taylorCoeff f) r : ℝ) ≤ K * r := by
  obtain ⟨E, hEm, hE, hnebot, K, hK, hbands⟩ :=
    polynomial_ode_newton_power_bands index hinj n hindex a ha hf hnp hode
  refine ⟨E, hEm, hE, hnebot, K, hK, ?_⟩
  have hdiag : ∀ i, scaledDegree index a n i + (index i : ℤ) = (D + n : ℕ) := by
    intro i
    dsimp only [scaledDegree]
    rw [hdegree i]
    have hi := hindex i
    exact_mod_cast (show D + (n-index i) + index i = D+n by omega)
  filter_upwards [hbands] with r hr
  obtain ⟨q, hq, _hqpos, hlo, hhi⟩ := hr
  obtain ⟨⟨i, j⟩, hij, heq⟩ := Finset.mem_image.mp hq
  have hne : i ≠ j := (Finset.mem_filter.mp hij).2
  have hqone : q = 1 := heq.symm.trans
    (candidateSlope_eq_one_of_common_diagonal index (scaledDegree index a n) hinj hdiag hne)
  simpa only [hqone, Rat.cast_one, Real.rpow_one] using And.intro hlo hhi

end HelmrathODE

#print axioms HelmrathODE.norm_scaled_term
#print axioms HelmrathODE.scaled_ode_sum
#print axioms HelmrathODE.polynomial_ode_newton_power_bands
#print axioms HelmrathODE.common_degree_polynomial_ode_linear_bands
