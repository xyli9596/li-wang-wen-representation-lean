import HelmrathODEApplication
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Compactness and roots in the Newton argument

A bounded complex variable on which a fixed nonzero polynomial tends to zero
approaches its finite root set. This includes repeated roots, and therefore
does not require simple-root hypotheses or any root multiplicity estimate.
-/

set_option autoImplicit false
noncomputable section
open Filter Finset Set
open scoped Topology

namespace HelmrathRootClustering

theorem eventually_near_roots {α : Type*} {l : Filter α}
    (p : Polynomial ℂ) {w : α → ℂ} {K : ℝ}
    (hw : ∀ᶠ x in l, ‖w x‖ ≤ K)
    (hpw : Tendsto (fun x => p.eval (w x)) l (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in l, ∃ ζ : ℂ, p.IsRoot ζ ∧ dist (w x) ζ < ε := by
  have hlim : Tendsto w l (𝓝ˢ {ζ : ℂ | p.IsRoot ζ}) := by
    apply (isCompact_closedBall (0 : ℂ) K).tendsto_nhdsSet_of_mapClusterPt
    · simpa only [Metric.mem_closedBall, dist_zero_right] using hw
    · intro ζ _ hζ
      have : NeBot (𝓝 ζ ⊓ map w l) := hζ
      have h₁ : Tendsto p.eval (𝓝 ζ ⊓ map w l) (𝓝 (p.eval ζ)) :=
        p.continuous.continuousAt.tendsto.mono_left inf_le_left
      have h₂ : Tendsto p.eval (𝓝 ζ ⊓ map w l) (𝓝 0) :=
        (tendsto_map' hpw).mono_left inf_le_right
      exact tendsto_nhds_unique h₁ h₂
  change {x | ∃ ζ : ℂ, p.IsRoot ζ ∧ dist x ζ < ε} ∈ map w l
  apply hlim
  apply mem_nhdsSet_iff_forall.mpr
  intro ζ hζ
  filter_upwards [Metric.ball_mem_nhds ζ hε] with z hz
  exact ⟨ζ, hζ, hz⟩

/-- A positive annular lower bound removes the zero root from the candidates. -/
theorem eventually_near_nonzero_roots {α : Type*} {l : Filter α}
    (p : Polynomial ℂ) {w : α → ℂ} {κ K : ℝ} (hκ : 0 < κ)
    (hw : ∀ᶠ x in l, κ ≤ ‖w x‖ ∧ ‖w x‖ ≤ K)
    (hpw : Tendsto (fun x => p.eval (w x)) l (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in l, ∃ ζ : ℂ, p.IsRoot ζ ∧ ζ ≠ 0 ∧ |‖w x‖ - ‖ζ‖| < ε := by
  have hδ : 0 < min ε κ := lt_min hε hκ
  filter_upwards [hw, eventually_near_roots p (hw.mono (fun _ h => h.2)) hpw hδ]
    with x hx hxroot
  obtain ⟨ζ, hζ, hdist⟩ := hxroot
  have hne : ζ ≠ 0 := by
    intro h
    rw [h, dist_zero_right] at hdist
    exact (not_lt_of_ge hx.1) (hdist.trans_le (min_le_right _ _))
  exact ⟨ζ, hζ, hne, (abs_norm_sub_norm_le (w x) ζ).trans_lt
    (by simpa only [dist_eq_norm] using hdist.trans_le (min_le_left _ _))⟩

/-- The moduli of the nonzero roots are a finite, positive set. -/
def rootModuli (p : Polynomial ℂ) : Set ℝ :=
  (fun ζ : ℂ => ‖ζ‖) '' {ζ : ℂ | p.IsRoot ζ ∧ ζ ≠ 0}

theorem rootModuli_finite {p : Polynomial ℂ} (hp : p ≠ 0) :
    (rootModuli p).Finite :=
  ((Polynomial.finite_setOfPred_isRoot hp).subset (fun _ h => h.1)).image _

theorem rootModuli_pos {p : Polynomial ℂ} {c : ℝ} (hc : c ∈ rootModuli p) : 0 < c := by
  obtain ⟨ζ, hζ, rfl⟩ := hc
  exact norm_pos_iff.mpr hζ.2

theorem eventually_near_rootModuli {α : Type*} {l : Filter α}
    (p : Polynomial ℂ) {w : α → ℂ} {κ K : ℝ} (hκ : 0 < κ)
    (hw : ∀ᶠ x in l, κ ≤ ‖w x‖ ∧ ‖w x‖ ≤ K)
    (hpw : Tendsto (fun x => p.eval (w x)) l (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in l, ∃ c ∈ rootModuli p, |‖w x‖ - c| < ε := by
  filter_upwards [eventually_near_nonzero_roots p hκ hw hpw hε] with x hx
  obtain ⟨ζ, hζ, hne, hclose⟩ := hx
  exact ⟨‖ζ‖, ⟨ζ, ⟨hζ, hne⟩, rfl⟩, hclose⟩

/-- Exact normalization by a complex power. Only powers of the same base
are combined, so this identity has no argument or branch-cut restriction. -/
theorem normalized_monomial (d j : ℕ) (q M : ℝ) {z v : ℂ} (hz : z ≠ 0) :
    z^d * v^j / z^(M : ℂ) =
      z^(((d : ℝ) + j*q-M : ℝ) : ℂ) * (v/z^(q : ℂ))^j := by
  have hq : z^(q : ℂ) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hz)
  have hM : z^(M : ℂ) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hz)
  have hpow : z^(((d : ℝ) + j*q : ℝ) : ℂ) = z^d * (z^(q : ℂ))^j := by
    push_cast
    rw [Complex.cpow_add _ _ hz, Complex.cpow_natCast, Complex.cpow_nat_mul]
  rw [Complex.ofReal_sub, Complex.cpow_sub _ _ hz, hpow, div_pow]
  field_simp

/-- A strictly submaximal Newton weight disappears after normalization,
even if the arguments of the evaluation points oscillate. -/
theorem cpow_negative_tendsto_zero {α : Type*} {l : Filter α} {z : α → ℂ}
    (hz : Tendsto (fun x => ‖z x‖) l atTop) {a : ℝ} (ha : a < 0) :
    Tendsto (fun x => (z x)^(a : ℂ)) l (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simp_rw [Complex.norm_cpow_real]
  have h : Tendsto (fun r : ℝ => r^a) atTop (𝓝 0) := by
    simpa only [neg_neg] using tendsto_rpow_neg_atTop (neg_pos.mpr ha)
  exact h.comp hz

/-- The polynomial made from terms on the top edge. -/
def edgePolynomial {ι : Type*} [Fintype ι]
    (index degree : ι → ℕ) (c : ι → ℂ) (q M : ℝ) : Polynomial ℂ :=
  ∑ i, Polynomial.monomial (index i) (if (degree i : ℝ) + index i*q = M then c i else 0)

theorem edgePolynomial_eval {ι : Type*} [Fintype ι]
    (index degree : ι → ℕ) (c : ι → ℂ) (q M : ℝ) (w : ℂ) :
    (edgePolynomial index degree c q M).eval w =
      ∑ i, (if (degree i : ℝ) + index i*q = M then c i else 0) * w^(index i) := by
  simp [edgePolynomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial]

theorem edgePolynomial_ne_zero {ι : Type*} [Fintype ι]
    (index degree : ι → ℕ) (hinj : Function.Injective index)
    (c : ι → ℂ) (hc : ∀ i, c i ≠ 0) (q M : ℝ)
    (hmax : ∃ i, (degree i : ℝ) + index i*q = M) :
    edgePolynomial index degree c q M ≠ 0 := by
  classical
  obtain ⟨i, hi⟩ := hmax
  intro hzero
  have hcoeff := congrArg (fun p : Polynomial ℂ => p.coeff (index i)) hzero
  have heq : (edgePolynomial index degree c q M).coeff (index i) = c i := by
    simp only [edgePolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
    rw [Finset.sum_eq_single i]
    · simp [hi]
    · intro j _ hji
      simp [show index j ≠ index i from fun h => hji (hinj h)]
    · simp
  rw [heq, Polynomial.coeff_zero] at hcoeff
  exact hc i hcoeff

theorem edgePolynomial_residual_tendsto_zero {α ι : Type*} [Fintype ι]
    {l : Filter α} (index degree : ι → ℕ) (c : ι → ℂ)
    {z v : α → ℂ} {b : α → ι → ℂ} {q M K : ℝ}
    (hz : Tendsto (fun x => ‖z x‖) l atTop)
    (hb : ∀ i, Tendsto (fun x => b x i) l (𝓝 (c i)))
    (hweight : ∀ i, (degree i : ℝ) + index i*q ≤ M)
    (hw : ∀ᶠ x in l, ‖v x / (z x)^(q : ℂ)‖ ≤ K)
    (hbalance : ∀ᶠ x in l, ∑ i, b x i * (z x)^(degree i) * (v x)^(index i) = 0) :
    Tendsto (fun x => (edgePolynomial index degree c q M).eval
      (v x / (z x)^(q : ℂ))) l (𝓝 0) := by
  classical
  let w : α → ℂ := fun x => v x / (z x)^(q : ℂ)
  let C : ι → ℂ := fun i => if (degree i : ℝ) + index i*q = M then c i else 0
  let B : α → ι → ℂ := fun x i => b x i *
    (z x)^(((degree i : ℝ) + index i*q-M : ℝ) : ℂ)
  have hB : ∀ i, Tendsto (fun x => B x i) l (𝓝 (C i)) := by
    intro i
    by_cases hi : (degree i : ℝ) + index i*q = M
    · have hiC : (((degree i : ℝ) + index i*q-M : ℝ) : ℂ) = 0 := by
        rw [hi, sub_self, Complex.ofReal_zero]
      simpa only [B, C, hiC, Complex.cpow_zero, mul_one, if_pos hi] using hb i
    · have hlt := lt_of_le_of_ne (hweight i) hi
      simpa [B, C, hi] using (hb i).mul (cpow_negative_tendsto_zero hz (sub_neg.mpr hlt))
  have hdiff : ∀ i, Tendsto (fun x => (C i - B x i) * (w x)^(index i)) l (𝓝 0) := by
    intro i
    have he : Tendsto (fun x => C i - B x i) l (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := C i) (f := l)).sub (hB i)
    have hbnd : IsBoundedUnder (· ≤ ·) l (fun x => ‖(w x)^(index i)‖) := by
      apply isBoundedUnder_of_eventually_le (a := K^(index i))
      filter_upwards [hw] with x hx
      simpa only [norm_pow] using pow_le_pow_left₀ (norm_nonneg _) hx (index i)
    exact NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded he hbnd
  have hsum := tendsto_finsetSum Finset.univ (fun i _ => hdiff i)
  simp only [Finset.sum_const_zero] at hsum
  apply hsum.congr'
  filter_upwards [hbalance, hz.eventually (eventually_gt_atTop (0 : ℝ))] with x hx hxz
  have hzne : z x ≠ 0 := norm_pos_iff.mp hxz
  have hnorm : ∑ i, B x i * (w x)^(index i) = 0 := by
    have hterm : ∀ i, B x i * (w x)^(index i) =
        (b x i * (z x)^(degree i) * (v x)^(index i)) / (z x)^(M : ℂ) := by
      intro i
      dsimp [B, w]
      rw [mul_assoc, ← normalized_monomial (degree i) (index i) q M hzne]
      ring
    simp_rw [hterm]
    rw [← Finset.sum_div, hx, zero_div]
  rw [edgePolynomial_eval]
  simp_rw [sub_mul, Finset.sum_sub_distrib]
  rw [hnorm, sub_zero]

/-- The largest Newton weight, without requiring a choice of an edge. -/
def edgeHeight {ι : Type*} [Fintype ι] [Nonempty ι]
    (index degree : ι → ℕ) (q : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => (degree i : ℝ) + index i*q)

theorem weight_le_edgeHeight {ι : Type*} [Fintype ι] [Nonempty ι]
    (index degree : ι → ℕ) (q : ℝ) (i : ι) :
    (degree i : ℝ) + index i*q ≤ edgeHeight index degree q :=
  Finset.le_sup' (fun j => (degree j : ℝ) + index j*q) (Finset.mem_univ i)

theorem exists_weight_eq_edgeHeight {ι : Type*} [Fintype ι] [Nonempty ι]
    (index degree : ι → ℕ) (q : ℝ) :
    ∃ i, (degree i : ℝ) + index i*q = edgeHeight index degree q := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun i => (degree i : ℝ) + index i*q)
  exact ⟨i, hi.symm⟩

/-- A finite collection of Newton slopes produces a finite collection of
positive root moduli. -/
def rootCandidates {ι : Type*} [Fintype ι] [Nonempty ι]
    (index degree : ι → ℕ) (c : ι → ℂ) (S : Finset ℚ) : Set (ℚ × ℝ) :=
  ⋃ q ∈ (S : Set ℚ), (fun r : ℝ => (q,r)) ''
    rootModuli (edgePolynomial index degree c (q : ℝ) (edgeHeight index degree (q : ℝ)))

theorem mem_rootCandidates {ι : Type*} [Fintype ι] [Nonempty ι]
    (index degree : ι → ℕ) (c : ι → ℂ) (S : Finset ℚ) (q : ℚ) (r : ℝ) :
    (q,r) ∈ rootCandidates index degree c S ↔ q ∈ S ∧
      r ∈ rootModuli (edgePolynomial index degree c (q : ℝ) (edgeHeight index degree (q : ℝ))) := by
  simp [rootCandidates, and_comm]

theorem rootCandidates_finite {ι : Type*} [Fintype ι] [Nonempty ι]
    (index degree : ι → ℕ) (hinj : Function.Injective index)
    (c : ι → ℂ) (hc : ∀ i, c i ≠ 0) (S : Finset ℚ) :
    (rootCandidates index degree c S).Finite := by
  apply S.finite_toSet.biUnion
  intro q _
  exact (rootModuli_finite (edgePolynomial_ne_zero index degree hinj c hc
    (q : ℝ) (edgeHeight index degree (q : ℝ))
    (exists_weight_eq_edgeHeight index degree (q : ℝ)))).image _

/-- Every fixed coarse band sharpens to the moduli of roots of its top-edge
polynomial. In particular, a purported one-term edge yields no candidates
and so cannot occur arbitrarily far out. -/
theorem fixed_band_root_approximation {α ι : Type*} [Fintype ι] [Nonempty ι]
    {l : Filter α} (index degree : ι → ℕ) (c : ι → ℂ)
    {z v : α → ℂ} {b : α → ι → ℂ} {q K : ℝ} (hK : 0 < K)
    (hz : Tendsto (fun x => ‖z x‖) l atTop)
    (hb : ∀ i, Tendsto (fun x => b x i) l (𝓝 (c i)))
    (hband : ∀ᶠ x in l, ‖z x‖^q ≤ K*‖v x‖ ∧ ‖v x‖ ≤ K*‖z x‖^q)
    (hbalance : ∀ᶠ x in l, ∑ i, b x i * (z x)^(degree i) * (v x)^(index i) = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in l, ∃ r ∈ rootModuli
      (edgePolynomial index degree c q (edgeHeight index degree q)),
      |‖v x‖ / ‖z x‖^q - r| < ε := by
  let w : α → ℂ := fun x => v x / (z x)^(q : ℂ)
  have hnorm : ∀ x, ‖w x‖ = ‖v x‖ / ‖z x‖^q := by
    intro x
    simp [w, Complex.norm_cpow_real]
  have hw : ∀ᶠ x in l, K⁻¹ ≤ ‖w x‖ ∧ ‖w x‖ ≤ K := by
    filter_upwards [hband, hz.eventually (eventually_gt_atTop (0 : ℝ))] with x hx hxz
    rw [hnorm]
    have hp : 0 < ‖z x‖^q := Real.rpow_pos_of_pos hxz q
    constructor
    · apply (le_div_iff₀ hp).mpr
      have h := (div_le_iff₀ hK).mpr (show ‖z x‖^q ≤ ‖v x‖*K by nlinarith [hx.1])
      simpa only [div_eq_mul_inv, mul_comm] using h
    · exact (div_le_iff₀ hp).mpr hx.2
  have hres := edgePolynomial_residual_tendsto_zero index degree c hz hb
    (weight_le_edgeHeight index degree q) (hw.mono (fun _ h => h.2)) hbalance
  simpa only [hnorm] using eventually_near_rootModuli
    (edgePolynomial index degree c q (edgeHeight index degree q))
    (inv_pos.mpr hK) hw hres hε

/-- Uniform finite-candidate refinement of any finite collection of coarse
power bands, deduced from the exact differential-equation balance. -/
theorem finite_bands_root_approximation {α ι : Type*} [Fintype ι] [Nonempty ι]
    {l : Filter α} (index degree : ι → ℕ) (c : ι → ℂ) (S : Finset ℚ)
    {z v : α → ℂ} {b : α → ι → ℂ} {K : ℝ} (hK : 0 < K)
    (hz : Tendsto (fun x => ‖z x‖) l atTop)
    (hb : ∀ i, Tendsto (fun x => b x i) l (𝓝 (c i)))
    (hbands : ∀ᶠ x in l, ∃ q ∈ S,
      ‖z x‖^(q : ℝ) ≤ K*‖v x‖ ∧ ‖v x‖ ≤ K*‖z x‖^(q : ℝ))
    (hbalance : ∀ᶠ x in l, ∑ i, b x i * (z x)^(degree i) * (v x)^(index i) = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in l, ∃ p ∈ rootCandidates index degree c S,
      |‖v x‖ / ‖z x‖^(p.1 : ℝ) - p.2| < ε := by
  classical
  have hq : ∀ q ∈ S, ∀ᶠ x in l,
      (‖z x‖^(q : ℝ) ≤ K*‖v x‖ ∧ ‖v x‖ ≤ K*‖z x‖^(q : ℝ)) →
      ∃ r ∈ rootModuli (edgePolynomial index degree c (q : ℝ)
        (edgeHeight index degree (q : ℝ))), |‖v x‖ / ‖z x‖^(q : ℝ) - r| < ε := by
    intro q _
    apply eventually_inf_principal.mp
    apply fixed_band_root_approximation index degree c hK
      (hz.mono_left inf_le_left) (fun i => (hb i).mono_left inf_le_left)
      (by exact eventually_inf_principal.mpr (Eventually.of_forall (fun _ h => h)))
      (hbalance.filter_mono inf_le_left) hε
  have hall : ∀ᶠ x in l, ∀ q ∈ S,
      (‖z x‖^(q : ℝ) ≤ K*‖v x‖ ∧ ‖v x‖ ≤ K*‖z x‖^(q : ℝ)) →
      ∃ r ∈ rootModuli (edgePolynomial index degree c (q : ℝ)
        (edgeHeight index degree (q : ℝ))), |‖v x‖ / ‖z x‖^(q : ℝ) - r| < ε :=
    (eventually_all_finite S.finite_toSet).mpr hq
  filter_upwards [hbands, hall] with x hx hxx
  obtain ⟨q, hqS, hqb⟩ := hx
  obtain ⟨r, hr, hclose⟩ := hxx q hqS hqb
  exact ⟨(q,r), (mem_rootCandidates index degree c S q r).mpr ⟨hqS,hr⟩, hclose⟩

end HelmrathRootClustering

#print axioms HelmrathRootClustering.eventually_near_roots
#print axioms HelmrathRootClustering.eventually_near_nonzero_roots
#print axioms HelmrathRootClustering.rootModuli_finite
#print axioms HelmrathRootClustering.rootModuli_pos
#print axioms HelmrathRootClustering.eventually_near_rootModuli
#print axioms HelmrathRootClustering.normalized_monomial
#print axioms HelmrathRootClustering.cpow_negative_tendsto_zero
#print axioms HelmrathRootClustering.edgePolynomial_eval
#print axioms HelmrathRootClustering.edgePolynomial_ne_zero
#print axioms HelmrathRootClustering.edgePolynomial_residual_tendsto_zero
#print axioms HelmrathRootClustering.weight_le_edgeHeight
#print axioms HelmrathRootClustering.exists_weight_eq_edgeHeight
#print axioms HelmrathRootClustering.mem_rootCandidates
#print axioms HelmrathRootClustering.rootCandidates_finite
#print axioms HelmrathRootClustering.fixed_band_root_approximation
#print axioms HelmrathRootClustering.finite_bands_root_approximation
