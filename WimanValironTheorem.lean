import WimanValironExceptionalRadii
import WimanValironWeightedMoments
import WimanValironTaylorMoments
import WimanValironQuantitativeDerivatives
import WimanValironDerivativeAsymptotics

/-!
# Quantitative Wiman--Valiron derivatives outside an exceptional set

This module assembles the actual normal-radius construction, the absolute
Taylor-moment estimates, the angular estimate for the first signed moment,
and the finite falling-factorial calculation. The exceptional set is common
to all fixed derivative orders. Neither coefficient-moment bounds nor
derivative asymptotics are assumptions of the final theorem.
-/

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Topology BigOperators

namespace WimanValiron

/-- The numeric normal-radius moment bound, expressed using the actual
Taylor coefficients and maximum modulus of an entire function. -/
theorem normal_absoluteTaylorMoment_bound (k : ℕ) {α β : ℝ}
    (hα : 0 < α) (hαtwo : α < 2) (hβ : α / 2 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ {f : ℂ → ℂ}, Differentiable ℂ f → f ≠ 0 →
      ∀ {r : ℝ} {N : ℕ}, 1 ≤ N →
        NormalRadiusAt (taylorCoeff f) (comparisonSequence α) r N →
        absoluteTaylorMoment f r N k ≤
          C * circleMaximum f r * (N : ℝ) ^ (β * ((k : ℝ) + 1) - (k : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := normal_normalized_moment_bound k hα hαtwo hβ
  refine ⟨C, hC, ?_⟩
  intro f hf hne r N hN hn
  have had := taylor_admissible hf hne hn.1
  have haN := normal_coefficient_ne_zero (comparisonSequence_pos α) hn had.2.2
  have hnorm := (hbound hN hn haN).2
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hN)
  have heq (n : ℕ) : realCenteredIndex N n = (n : ℝ) / (N : ℝ) - 1 := by
    dsimp [realCenteredIndex]
    field_simp
  simp only [absoluteTaylorMoment, heq] at ⊢
  refine hnorm.trans ?_
  have hterm : term (taylorCoeff f) r N ≤ circleMaximum f r :=
    (term_le_maximumTerm had N).trans (maximumTerm_le_circleMaximum hf hn.1)
  gcongr

/-- The exponents in the first-moment and higher-moment estimates are
stronger than the advertised Wiman--Valiron error exponent. -/
theorem wimanValiron_moment_exponents {δ : ℝ} (hδ : 0 < δ) (hδupper : δ < 1 / 8) :
    ((1 / 2 + δ / 2) * (2 + 1) - 2) / 2 - (-1 / 8 + δ) ≤ -1 / 8 + δ ∧
      ∀ k : ℕ, 2 ≤ k →
        (1 / 2 + δ / 2) * ((k : ℝ) + 1) - (k : ℝ) - (-1 / 8 + δ) ≤
          -1 / 8 + δ := by
  constructor
  · linarith
  · intro k hk
    have hkr : (2 : ℝ) ≤ k := by exact_mod_cast hk
    have hm := mul_le_mul_of_nonpos_left hkr
      (show 1 / 2 + δ / 2 - 1 ≤ 0 by linarith)
    nlinarith

/-- At a normal radius every fixed finite family of actual signed moments
has the classical power saving at a near-maximum point. -/
theorem normal_centered_moments_bound {δ : ℝ} (hδ : 0 < δ) (hδupper : δ < 1 / 8)
    (j : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ {f : ℂ → ℂ}, Differentiable ℂ f → f ≠ 0 →
      ∀ {r : ℝ} {N : ℕ}, 1 ≤ N →
        NormalRadiusAt (taylorCoeff f) (comparisonSequence (1 + δ / 2)) r N →
        ∀ {z : ℂ}, ‖z‖ = r →
          circleMaximum f r * (N : ℝ) ^ (-1 / 8 + δ) ≤ ‖f z‖ →
          ∀ k : ℕ, 1 ≤ k → k ≤ j →
            ‖centeredMoment (taylorWeight f z) (N : ℂ) k‖ ≤
              K * (N : ℝ) ^ (-1 / 8 + δ) := by
  have hα : (0 : ℝ) < 1 + δ / 2 := by linarith
  have hαtwo : 1 + δ / 2 < 2 := by linarith
  have hβ : (1 + δ / 2) / 2 < 1 / 2 + δ / 2 := by linarith
  choose C hC hbound using
    (fun k => normal_absoluteTaylorMoment_bound k hα hαtwo hβ)
  let K : ℝ := 2 * Real.sqrt (C 2) + ∑ k ∈ Finset.range (j + 1), C k
  have hsum : 0 ≤ ∑ k ∈ Finset.range (j + 1), C k :=
    Finset.sum_nonneg (fun k _ => (hC k).le)
  have hK : 0 < K := by
    dsimp [K]
    exact add_pos_of_pos_of_nonneg
      (mul_pos (by norm_num) (Real.sqrt_pos.mpr (hC 2))) hsum
  refine ⟨K, hK, ?_⟩
  intro f hf hne r N hN hn z hz hlower k hk hkj
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : 0 < N := hN
  have hexp := wimanValiron_moment_exponents hδ hδupper
  by_cases hkone : k = 1
  · subst k
    have hb := norm_centeredMoment_one_of_power_second hf hne hn.1 hz hNp (hC 2)
      hlower (hbound 2 hf hne hN hn)
    have hcoeff : 2 * Real.sqrt (C 2) ≤ K := by dsimp [K]; linarith
    refine hb.trans ?_
    exact mul_le_mul hcoeff
      (Real.rpow_le_rpow_of_exponent_le hNr (by simpa using hexp.1))
      (Real.rpow_nonneg (by positivity) _) hK.le
  · have hk2 : 2 ≤ k := by omega
    have hb := norm_centeredMoment_bound_of_absolute hf hne hz hNp
      (circleMaximum_pos hf hne hn.1) (hC k).le hlower (hbound k hf hne hN hn)
    have hcoeff : C k ≤ K := by
      have hmem : k ∈ Finset.range (j + 1) := Finset.mem_range.mpr (by omega)
      have hs := Finset.single_le_sum (fun k _ => (hC k).le) hmem
      dsimp [K]
      have : 0 ≤ 2 * Real.sqrt (C 2) := by positivity
      linarith
    refine hb.trans ?_
    exact mul_le_mul hcoeff (Real.rpow_le_rpow_of_exponent_le hNr (hexp.2 k hk2))
      (Real.rpow_nonneg (by positivity) _) hK.le

/-- The quantitative derivative conclusion at normal radii. All inputs are
properties of the entire function, its central index and the chosen point. -/
theorem normal_derivative_error_bound {δ : ℝ} (hδ : 0 < δ) (hδupper : δ < 1 / 8)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {f : ℂ → ℂ}, Differentiable ℂ f → f ≠ 0 →
      ∀ {r : ℝ} {N : ℕ}, 1 ≤ N →
        NormalRadiusAt (taylorCoeff f) (comparisonSequence (1 + δ / 2)) r N →
        ∀ {z : ℂ}, ‖z‖ = r →
          circleMaximum f r * (N : ℝ) ^ (-1 / 8 + δ) ≤ ‖f z‖ →
          ‖derivativeRatio f N j z - 1‖ ≤ C * (N : ℝ) ^ (-1 / 8 + δ) := by
  obtain ⟨K, hK, hmoment⟩ := normal_centered_moments_bound hδ hδupper j
  let C : ℝ := derivativeMomentConstant j * (K + 1) + 1
  have hD := derivativeMomentConstant_nonneg j
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro f hf hne r N hN hn z hz hlower
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := zero_lt_one.trans_le hNr
  have hpower : 0 < (N : ℝ) ^ (-1 / 8 + δ) := Real.rpow_pos_of_pos hNp _
  have hfz : f z ≠ 0 := norm_pos_iff.mp
    ((mul_pos (circleMaximum_pos hf hne hn.1) hpower).trans_le hlower)
  have hsmall : 1 / (N : ℝ) ≤ (N : ℝ) ^ (-1 / 8 + δ) := by
    calc
      1 / (N : ℝ) = (N : ℝ) ^ (-1 : ℝ) := by simp [Real.rpow_neg_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
  have hb := normalized_deriv_error_le_nat_centered_moments hf hfz hN
    (mul_nonneg hK.le hpower.le) j (hmoment hf hne hN hn hz hlower)
  change ‖derivativeRatio f N j z - 1‖ ≤ _ at hb
  refine hb.trans ?_
  calc
    derivativeMomentConstant j * (K * (N : ℝ) ^ (-1 / 8 + δ) + 1 / (N : ℝ)) ≤
        derivativeMomentConstant j * ((K + 1) * (N : ℝ) ^ (-1 / 8 + δ)) := by
      apply mul_le_mul_of_nonneg_left _ hD
      nlinarith
    _ ≤ C * (N : ℝ) ^ (-1 / 8 + δ) := by
      dsimp [C]
      nlinarith

/-- Quantitative Wiman--Valiron theorem for every fixed derivative order of
a transcendental entire function. One measurable exceptional set of finite
logarithmic measure works for all derivative orders. -/
theorem wimanValiron_quantitative {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnp : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z)
    {δ : ℝ} (hδ : 0 < δ) (hδupper : δ < 1 / 8) :
    ∃ E : Set ℝ, MeasurableSet E ∧
      HelmrathExceptionalSet.FiniteLogarithmicMeasure E ∧
      ∀ j : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ R : ℝ, 0 < R ∧
        ∀ r : ℝ, R ≤ r → r ∉ E →
          1 ≤ centralIndex (taylorCoeff f) r ∧
          ∀ z : ℂ, ‖z‖ = r →
            circleMaximum f r * (centralIndex (taylorCoeff f) r : ℝ) ^ (-1 / 8 + δ) ≤
              ‖f z‖ →
            ‖derivativeRatio f (centralIndex (taylorCoeff f) r) j z - 1‖ ≤
              C * (centralIndex (taylorCoeff f) r : ℝ) ^ (-1 / 8 + δ) := by
  have hne : f ≠ 0 := by
    intro h
    exact hnp ⟨0, by simp [h]⟩
  have hα : (1 : ℝ) < 1 + δ / 2 := by linarith
  obtain ⟨P, hP⟩ := comparisonSequence_bounded hα
  obtain ⟨E, hmeas, hfinite, hnormal⟩ := exists_exceptional_set_normal_radii
    (fun _ hr => taylor_admissible hf hne hr) (comparisonSequence_pos (1 + δ / 2))
    (comparisonSequence_strictMono (1 + δ / 2)).monotone hP
  have hindex := (taylor_centralIndex_tendsto_atTop hf hnp).eventually
    (eventually_ge_atTop 1)
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp hindex
  refine ⟨E, hmeas, hfinite, ?_⟩
  intro j
  obtain ⟨C, hC, hbound⟩ := normal_derivative_error_bound hδ hδupper j
  refine ⟨C, hC, max 1 R₀, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro r hlarge hgood
  have hr : 0 < r := (zero_lt_one.trans_le (le_max_left 1 R₀)).trans_le hlarge
  have hN : 1 ≤ centralIndex (taylorCoeff f) r :=
    hR₀ r ((le_max_right _ _).trans hlarge)
  obtain ⟨N, hn⟩ := hnormal r hr hgood
  have haN := normal_coefficient_ne_zero (comparisonSequence_pos (1 + δ / 2)) hn
    (taylor_admissible hf hne hr).2.2
  have heq : N = centralIndex (taylorCoeff f) r := centralIndex_unique
    (normal_isCentralIndex (comparisonSequence_pos (1 + δ / 2))
      (comparisonSequence_strictMono (1 + δ / 2)) hn haN)
    (centralIndex_spec (taylor_admissible hf hne hr))
  subst N
  exact ⟨hN, fun z hz hlower => hbound hf hne hN hn hz hlower⟩

/-- The customary derivative formula with a quantitatively controlled
relative error, in the near-maximum region of the Wiman--Valiron theorem. -/
theorem wimanValiron_derivative_formula {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnp : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z)
    {δ : ℝ} (hδ : 0 < δ) (hδupper : δ < 1 / 8) :
    ∃ E : Set ℝ, MeasurableSet E ∧
      HelmrathExceptionalSet.FiniteLogarithmicMeasure E ∧
      ∀ j : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ R : ℝ, 0 < R ∧
        ∀ r : ℝ, R ≤ r → r ∉ E → ∀ z : ℂ, ‖z‖ = r →
          circleMaximum f r * (centralIndex (taylorCoeff f) r : ℝ) ^ (-1 / 8 + δ) <
            ‖f z‖ →
          ∃ η : ℂ,
            iteratedDeriv j f z / f z =
              ((centralIndex (taylorCoeff f) r : ℂ) / z) ^ j * (1 + η) ∧
            ‖η‖ ≤ C * (centralIndex (taylorCoeff f) r : ℝ) ^ (-1 / 8 + δ) := by
  obtain ⟨E, hmeas, hfinite, hbound⟩ := wimanValiron_quantitative hf hnp hδ hδupper
  refine ⟨E, hmeas, hfinite, ?_⟩
  intro j
  obtain ⟨C, hC, R, hR, htail⟩ := hbound j
  refine ⟨C, hC, R, hR, ?_⟩
  intro r hr hgood z hz hlower
  obtain ⟨hN, herror⟩ := htail r hr hgood
  have hrpos : 0 < r := hR.trans_le hr
  have hz0 : z ≠ 0 := norm_pos_iff.mp (hz.symm ▸ hrpos)
  have hne : f ≠ 0 := by
    intro h
    exact hnp ⟨0, by simp [h]⟩
  have hM := circleMaximum_pos hf hne hrpos
  have hfz : f z ≠ 0 := norm_pos_iff.mp
    ((mul_nonneg hM.le (Real.rpow_nonneg (by positivity) _)).trans_lt hlower)
  refine ⟨derivativeRatio f (centralIndex (taylorCoeff f) r) j z - 1,
    derivative_eq_with_relative_error hz0 (Nat.ne_zero_of_lt hN) hfz, ?_⟩
  exact herror z hz hlower.le

end WimanValiron

#print axioms WimanValiron.normal_absoluteTaylorMoment_bound
#print axioms WimanValiron.wimanValiron_moment_exponents
#print axioms WimanValiron.normal_centered_moments_bound
#print axioms WimanValiron.normal_derivative_error_bound
#print axioms WimanValiron.wimanValiron_quantitative
#print axioms WimanValiron.wimanValiron_derivative_formula
