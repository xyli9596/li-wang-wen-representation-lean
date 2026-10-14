import WimanValironExceptionalRadii
import WimanValironWeightedMoments
import WimanValironTaylorMoments

/-!
# Unit-constant coefficient estimates from the central-index method

For each fixed moment order and positive exponent loss, the constant in the
normal-radius moment bound can be absorbed into a further small power of the
actual central index. The exceptional set is measurable and has finite
logarithmic measure. The zero-th moment gives the corresponding comparison
of the maximum modulus with the maximum term.
-/

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Topology BigOperators

namespace WimanValiron

/-- The actual maximum modulus is bounded by the sum of absolute Taylor terms. -/
theorem circleMaximum_le_tsum_term {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hne : f ≠ 0) {r : ℝ} (hr : 0 < r) :
    circleMaximum f r ≤ ∑' n, term (taylorCoeff f) r n := by
  obtain ⟨z, hz, heq⟩ := exists_norm_eq_circleMaximum hf.continuous hr.le
  have hnorm : ‖z‖ = r := by simpa only [Metric.mem_sphere, dist_zero_right] using hz
  have hsum : Summable (fun n => term (taylorCoeff f) r n) := by
    simpa only [pow_zero, one_mul] using summable_absoluteTaylorMoment hf hne hr.le 0 0
  rw [← heq]
  exact (hasSum_taylorCoeff hf z).norm_le_of_bounded hsum.hasSum (fun n => by
    simp only [norm_mul, norm_pow, hnorm, term, le_refl])

/-- The normalized coefficient-moment estimate with unit leading constant.
The exceptional set may depend on the fixed order `l` and on `ε`. -/
theorem book_normalized_moment_bound {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnp : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z)
    (l : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ E : Set ℝ, MeasurableSet E ∧
      HelmrathExceptionalSet.FiniteLogarithmicMeasure E ∧
      ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, R ≤ r → r ∉ E →
        1 ≤ centralIndex (taylorCoeff f) r ∧
        Summable (fun n : ℕ => |(n : ℝ)/(centralIndex (taylorCoeff f) r : ℝ)-1|^l *
          term (taylorCoeff f) r n) ∧
        (∑' n : ℕ, |(n : ℝ)/(centralIndex (taylorCoeff f) r : ℝ)-1|^l *
          term (taylorCoeff f) r n) ≤
          maximumTerm (taylorCoeff f) r *
            (centralIndex (taylorCoeff f) r : ℝ)^((1-(l : ℝ))/2+ε) := by
  let σ : ℝ := min (ε/2) (1/4)
  let β : ℝ := 1/2 + σ/((l : ℝ)+1)
  let α : ℝ := 1/2 + β
  have hσ : 0 < σ := lt_min (by linarith) (by norm_num)
  have hσε : σ < ε := (min_le_left _ _).trans_lt (by linarith)
  have hσquarter : σ ≤ 1/4 := min_le_right _ _
  have hL : 0 < (l : ℝ)+1 := by positivity
  have hd : 0 < σ/((l : ℝ)+1) := div_pos hσ hL
  have hdquarter : σ/((l : ℝ)+1) ≤ 1/4 := (div_le_iff₀ hL).mpr (by
    have : (0 : ℝ) ≤ l := Nat.cast_nonneg l
    nlinarith)
  have hαone : 1 < α := by dsimp [α, β]; linarith
  have hαtwo : α < 2 := by dsimp [α, β]; linarith
  have hβ : α/2 < β := by dsimp [α, β]; linarith
  have hexponent : β*((l : ℝ)+1)-(l : ℝ) = (1-(l : ℝ))/2+σ := by
    dsimp [β]
    field_simp
    ring
  have hne : f ≠ 0 := by
    intro h
    exact hnp ⟨0, by simp [h]⟩
  obtain ⟨C, hC, hbound⟩ := normal_normalized_moment_bound l (zero_lt_one.trans hαone)
    hαtwo hβ
  obtain ⟨P, hP⟩ := comparisonSequence_bounded hαone
  obtain ⟨E, hmeas, hfinite, hnormal⟩ := exists_exceptional_set_normal_radii
    (fun _ hr => taylor_admissible hf hne hr) (comparisonSequence_pos α)
    (comparisonSequence_strictMono α).monotone hP
  have hindex := taylor_centralIndex_tendsto_atTop hf hnp
  have hreal : Tendsto (fun r => (centralIndex (taylorCoeff f) r : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hindex
  have hpower := (tendsto_rpow_atTop (sub_pos.mpr hσε)).comp hreal
  have htail := (hindex.eventually (eventually_ge_atTop 1)).and
    (hpower.eventually (eventually_ge_atTop C))
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp htail
  refine ⟨E, hmeas, hfinite, max 1 R₀,
    zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro r hr hgood
  have hrpos : 0 < r := (zero_lt_one.trans_le (le_max_left 1 R₀)).trans_le hr
  obtain ⟨hN1, hCbound⟩ := hR₀ r ((le_max_right _ _).trans hr)
  have hNp : (0 : ℝ) < centralIndex (taylorCoeff f) r := by
    exact_mod_cast (show 0 < centralIndex (taylorCoeff f) r by omega)
  obtain ⟨N, hn⟩ := hnormal r hrpos hgood
  have haN := normal_coefficient_ne_zero (comparisonSequence_pos α) hn
    (taylor_admissible hf hne hrpos).2.2
  have heq : N = centralIndex (taylorCoeff f) r := centralIndex_unique
    (normal_isCentralIndex (comparisonSequence_pos α) (comparisonSequence_strictMono α) hn haN)
    (centralIndex_spec (taylor_admissible hf hne hrpos))
  subst N
  obtain ⟨hsum, hraw⟩ := hbound hN1 hn haN
  refine ⟨hN1, hsum, hraw.trans ?_⟩
  have hμ : 0 < maximumTerm (taylorCoeff f) r :=
    maximumTerm_pos (taylor_admissible hf hne hrpos)
  change C * maximumTerm (taylorCoeff f) r * _ ≤ _
  calc
    _ ≤ (centralIndex (taylorCoeff f) r : ℝ)^(ε-σ) *
        maximumTerm (taylorCoeff f) r *
        (centralIndex (taylorCoeff f) r : ℝ)^(β*((l : ℝ)+1)-(l : ℝ)) := by
      gcongr
      exact hCbound
    _ = maximumTerm (taylorCoeff f) r *
        ((centralIndex (taylorCoeff f) r : ℝ)^(ε-σ) *
          (centralIndex (taylorCoeff f) r : ℝ)^(β*((l : ℝ)+1)-(l : ℝ))) := by ring
    _ = _ := by
      rw [← Real.rpow_add hNp, hexponent]
      congr 2
      ring

/-- The weighted coefficient inequality with an additional real denominator
power. The exceptional set is chosen for this fixed `l` and `ε`; no claim of
one unit-constant exceptional set for every order is made. -/
theorem book_weighted_moment_bound {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnp : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z)
    (l : ℕ) (κ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ E : Set ℝ, MeasurableSet E ∧
      HelmrathExceptionalSet.FiniteLogarithmicMeasure E ∧
      ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, R ≤ r → r ∉ E →
        Summable (fun n : ℕ => |(n : ℝ)-(centralIndex (taylorCoeff f) r : ℝ)|^l /
          (centralIndex (taylorCoeff f) r : ℝ)^((l : ℝ)+κ) * term (taylorCoeff f) r n) ∧
        (∑' n : ℕ, |(n : ℝ)-(centralIndex (taylorCoeff f) r : ℝ)|^l /
          (centralIndex (taylorCoeff f) r : ℝ)^((l : ℝ)+κ) * term (taylorCoeff f) r n) ≤
          maximumTerm (taylorCoeff f) r *
            (centralIndex (taylorCoeff f) r : ℝ)^((1-(l : ℝ)-2*κ)/2+ε) := by
  obtain ⟨E, hmeas, hfinite, R, hR, hbound⟩ := book_normalized_moment_bound hf hnp l hε
  refine ⟨E, hmeas, hfinite, R, hR, ?_⟩
  intro r hr hgood
  obtain ⟨hN1, hsum, hmoment⟩ := hbound r hr hgood
  let N : ℕ := centralIndex (taylorCoeff f) r
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by dsimp [N]; omega)
  have heq : (fun n : ℕ => |(n : ℝ)-(N : ℝ)|^l / (N : ℝ)^((l : ℝ)+κ) *
      term (taylorCoeff f) r n) = (fun n : ℕ =>
        (|(n : ℝ)/(N : ℝ)-1|^l * term (taylorCoeff f) r n)/(N : ℝ)^κ) := by
    funext n
    have hd : (n : ℝ)/(N : ℝ)-1 = ((n : ℝ)-(N : ℝ))/(N : ℝ) := by field_simp
    rw [Real.rpow_add hNp, Real.rpow_natCast, hd, abs_div, abs_of_pos hNp, div_pow]
    ring
  change Summable (fun n : ℕ => |(n : ℝ)-(N : ℝ)|^l / (N : ℝ)^((l : ℝ)+κ) *
      term (taylorCoeff f) r n) ∧ _
  rw [heq]
  refine ⟨hsum.div_const _, ?_⟩
  rw [tsum_div_const]
  calc
    _ ≤ (maximumTerm (taylorCoeff f) r * (N : ℝ)^((1-(l : ℝ))/2+ε))/(N : ℝ)^κ :=
      div_le_div_of_nonneg_right hmoment (Real.rpow_nonneg hNp.le _)
    _ = maximumTerm (taylorCoeff f) r * (N : ℝ)^(((1-(l : ℝ))/2+ε)-κ) := by
      rw [Real.rpow_sub hNp]
      ring
    _ = _ := by congr 2; ring

/-- The maximum-modulus estimate corresponding to the zero-th coefficient
moment, outside a measurable set of finite logarithmic measure. -/
theorem book_maximum_modulus_bound {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnp : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ E : Set ℝ, MeasurableSet E ∧
      HelmrathExceptionalSet.FiniteLogarithmicMeasure E ∧
      ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, R ≤ r → r ∉ E →
        circleMaximum f r ≤ maximumTerm (taylorCoeff f) r *
          (centralIndex (taylorCoeff f) r : ℝ)^(1/2+ε) := by
  obtain ⟨E, hmeas, hfinite, R, hR, hbound⟩ := book_normalized_moment_bound hf hnp 0 hε
  refine ⟨E, hmeas, hfinite, R, hR, ?_⟩
  intro r hr hgood
  have hne : f ≠ 0 := by
    intro h
    exact hnp ⟨0, by simp [h]⟩
  have h := (hbound r hr hgood).2.2
  simp only [Nat.cast_zero, pow_zero, one_mul, sub_zero] at h
  exact (circleMaximum_le_tsum_term hf hne (hR.trans_le hr)).trans h

end WimanValiron

#print axioms WimanValiron.circleMaximum_le_tsum_term
#print axioms WimanValiron.book_normalized_moment_bound
#print axioms WimanValiron.book_weighted_moment_bound
#print axioms WimanValiron.book_maximum_modulus_bound
