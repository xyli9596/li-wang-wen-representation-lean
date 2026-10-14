import HelmrathNewtonBalance
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Finite Newton candidates from an actual vanishing balance

A nontrivial finite vanishing sum has two comparable terms. When their
magnitudes are uniformly comparable to radial monomials, this forces the
positive central-index variable into one of finitely many explicitly rational
power bands. No order or power asymptotic is assumed.

These are coarse power bands, not the final Helmrath--Nikolaus asymptotic
`ν(r) ~ c r^ρ`. Refining a band to the moduli of Newton-edge roots and proving
that one such root branch is eventually selected remain separate obligations.
-/

set_option autoImplicit false
noncomputable section
open Filter Finset
open scoped Topology

namespace HelmrathNewtonBranches

/-- A vanishing finite sum with nonzero terms has two comparable magnitudes. -/
theorem exists_comparable_terms {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (u : ι → ℂ) (hpos : ∀ i, 0 < ‖u i‖) (hsum : ∑ i, u i = 0) :
    ∃ i j : ι, i ≠ j ∧ ‖u j‖ ≤ ‖u i‖ ∧
      ‖u i‖ ≤ (Fintype.card ι : ℝ) * ‖u j‖ := by
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun i => ‖u i‖)
    Finset.univ_nonempty
  have heq : ∑ j ∈ Finset.univ.erase i, u j = -u i := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i), hsum, zero_sub]
  have hnorm : ‖u i‖ ≤ ∑ j ∈ Finset.univ.erase i, ‖u j‖ := by
    calc
      ‖u i‖ = ‖∑ j ∈ Finset.univ.erase i, u j‖ := by rw [heq, norm_neg]
      _ ≤ _ := norm_sum_le _ _
  have hne : (Finset.univ.erase i).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty] at hnorm
    exact (not_le_of_gt (hpos i)) hnorm
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image (Finset.univ.erase i) (fun j => ‖u j‖) hne
  refine ⟨i, j, (Finset.mem_erase.mp hj).1.symm, hi j (Finset.mem_univ j), ?_⟩
  calc
    ‖u i‖ ≤ ∑ k ∈ Finset.univ.erase i, ‖u k‖ := hnorm
    _ ≤ ∑ _k ∈ Finset.univ.erase i, ‖u j‖ :=
      Finset.sum_le_sum (fun k hk => hmax k hk)
    _ = ((Finset.univ.erase i).card : ℝ) * ‖u j‖ := by simp
    _ ≤ (Fintype.card ι : ℝ) * ‖u j‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact_mod_cast (Finset.card_le_card (Finset.erase_subset i Finset.univ))

/-- Uniform two-sided magnitude bounds transfer comparability to monomials. -/
theorem exists_comparable_monomials {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (u : ι → ℂ) (m : ι → ℝ) {Q : ℝ} (hQ : 1 ≤ Q)
    (hm : ∀ i, 0 < m i) (hlower : ∀ i, m i ≤ Q * ‖u i‖)
    (hupper : ∀ i, ‖u i‖ ≤ Q * m i) (hsum : ∑ i, u i = 0) :
    ∃ i j : ι, i ≠ j ∧
      m i ≤ ((Fintype.card ι : ℝ) * Q^2) * m j ∧
      m j ≤ ((Fintype.card ι : ℝ) * Q^2) * m i := by
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  have hu : ∀ i, 0 < ‖u i‖ := by
    intro i
    by_contra h
    have hz : ‖u i‖ = 0 := le_antisymm (le_of_not_gt h) (norm_nonneg _)
    have h := hlower i
    rw [hz, mul_zero] at h
    exact (not_le_of_gt (hm i)) h
  obtain ⟨i, j, hij, hji, hijbound⟩ := exists_comparable_terms u hu hsum
  have hcard : (1 : ℝ) ≤ Fintype.card ι := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
  refine ⟨i, j, hij, ?_, ?_⟩
  · calc
      m i ≤ Q * ‖u i‖ := hlower i
      _ ≤ Q * ((Fintype.card ι : ℝ) * ‖u j‖) :=
        mul_le_mul_of_nonneg_left hijbound hQpos.le
      _ ≤ Q * ((Fintype.card ι : ℝ) * (Q * m j)) := by
        gcongr
        exact hupper j
      _ = _ := by ring
  · calc
      m j ≤ Q * ‖u j‖ := hlower j
      _ ≤ Q * ‖u i‖ := mul_le_mul_of_nonneg_left hji hQpos.le
      _ ≤ Q * (Q * m i) := mul_le_mul_of_nonneg_left (hupper i) hQpos.le
      _ ≤ ((Fintype.card ι : ℝ) * Q^2) * m i := by
        have h := mul_le_mul_of_nonneg_right hcard (mul_nonneg (sq_nonneg Q) (hm i).le)
        nlinarith

/-- The radial magnitude of a Newton monomial. -/
def radialMonomial (d : ℤ) (j : ℕ) (r v : ℝ) : ℝ := r^(d : ℝ) * v^j

theorem radialMonomial_pos (d : ℤ) (j : ℕ) {r v : ℝ} (hr : 0 < r) (hv : 0 < v) :
    0 < radialMonomial d j r v := by unfold radialMonomial; positivity

theorem log_radialMonomial (d : ℤ) (j : ℕ) {r v : ℝ} (hr : 0 < r) (hv : 0 < v) :
    Real.log (radialMonomial d j r v) = (d : ℝ) * Real.log r + (j : ℝ) * Real.log v := by
  rw [radialMonomial, Real.log_mul (Real.rpow_pos_of_pos hr _).ne' (pow_pos hv j).ne',
    Real.log_rpow hr, Real.log_pow]

/-- The rational slope at which two Newton monomials have the same radial weight. -/
def candidateSlope {ι : Type*} (index : ι → ℕ) (degree : ι → ℤ) (i j : ι) : ℚ :=
  ((degree j - degree i : ℤ) : ℚ) / ((index i : ℚ) - (index j : ℚ))

/-- There are only finitely many slopes determined by distinct participating terms. -/
def candidateSlopes {ι : Type*} [Fintype ι] [DecidableEq ι]
    (index : ι → ℕ) (degree : ι → ℤ) : Finset ℚ :=
  ((Finset.univ.product Finset.univ).filter (fun ij : ι × ι => ij.1 ≠ ij.2)).image
    (fun ij => candidateSlope index degree ij.1 ij.2)

theorem candidateSlope_mem {ι : Type*} [Fintype ι] [DecidableEq ι]
    (index : ι → ℕ) (degree : ι → ℤ) {i j : ι} (hij : i ≠ j) :
    candidateSlope index degree i j ∈ candidateSlopes index degree := by
  apply Finset.mem_image.mpr
  exact ⟨(i, j), by simp [hij], rfl⟩

/-- Integer exponents of distinct derivative orders are separated by at least one. -/
theorem one_le_abs_nat_sub {i j : ℕ} (hij : i ≠ j) : (1 : ℝ) ≤ |(i : ℝ) - j| := by
  rcases lt_or_gt_of_ne hij with h | h
  · have hcast : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
    rw [abs_of_neg (by linarith : (i : ℝ) - j < 0)]
    linarith
  · have hcast : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
    rw [abs_of_pos (by linarith : 0 < (i : ℝ) - j)]
    linarith

/-- Comparable monomials constrain the logarithm of the central-index variable
without assuming that its logarithmic growth rate has a limit. -/
theorem log_band_of_comparable {ι : Type*} (index : ι → ℕ) (degree : ι → ℤ)
    (hinj : Function.Injective index) {i j : ι} (hij : i ≠ j) {r v K : ℝ}
    (hr : 0 < r) (hv : 0 < v) (hK : 0 < K)
    (hijm : radialMonomial (degree i) (index i) r v ≤ K * radialMonomial (degree j) (index j) r v)
    (hjim : radialMonomial (degree j) (index j) r v ≤ K * radialMonomial (degree i) (index i) r v) :
    |Real.log v - (candidateSlope index degree i j : ℝ) * Real.log r| ≤ Real.log K := by
  have hmi := radialMonomial_pos (degree i) (index i) hr hv
  have hmj := radialMonomial_pos (degree j) (index j) hr hv
  have hlij := Real.log_le_log hmi hijm
  have hlji := Real.log_le_log hmj hjim
  rw [Real.log_mul hK.ne' hmj.ne'] at hlij
  rw [Real.log_mul hK.ne' hmi.ne'] at hlji
  have hlogs : |Real.log (radialMonomial (degree i) (index i) r v) -
      Real.log (radialMonomial (degree j) (index j) r v)| ≤ Real.log K := by
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hidx : index i ≠ index j := fun h => hij (hinj h)
  have hden : (index i : ℝ) - index j ≠ 0 :=
    sub_ne_zero.mpr (by exact_mod_cast hidx)
  have hq : (candidateSlope index degree i j : ℝ) =
      ((degree j : ℝ) - degree i) / ((index i : ℝ) - index j) := by
    simp [candidateSlope]
  have heq : Real.log (radialMonomial (degree i) (index i) r v) -
      Real.log (radialMonomial (degree j) (index j) r v) =
      ((index i : ℝ) - index j) *
        (Real.log v - (candidateSlope index degree i j : ℝ) * Real.log r) := by
    rw [log_radialMonomial _ _ hr hv, log_radialMonomial _ _ hr hv, hq]
    field_simp
    ring
  rw [heq, abs_mul] at hlogs
  have hsep := one_le_abs_nat_sub hidx
  have hnonneg := abs_nonneg (Real.log v - (candidateSlope index degree i j : ℝ) * Real.log r)
  nlinarith

/-- A logarithmic band is an actual two-sided power bound. -/
theorem power_band_of_log_band {r v K ρ : ℝ} (hr : 0 < r) (hv : 0 < v) (hK : 0 < K)
    (hband : |Real.log v - ρ * Real.log r| ≤ Real.log K) :
    r^ρ ≤ K*v ∧ v ≤ K*r^ρ := by
  have hlo := (abs_le.mp hband).1
  have hhi := (abs_le.mp hband).2
  have hp : 0 < r^ρ := Real.rpow_pos_of_pos hr _
  constructor
  · apply (Real.log_le_log_iff hp (mul_pos hK hv)).mp
    rw [Real.log_rpow hr, Real.log_mul hK.ne' hv.ne']
    linarith
  · apply (Real.log_le_log_iff hv (mul_pos hK hp)).mp
    rw [Real.log_mul hK.ne' hp.ne', Real.log_rpow hr]
    linarith

/-- The uniform band constant depends only on the number of participating
terms and the common coefficient comparison factor. -/
def bandConstant (m : ℕ) (Q : ℝ) : ℝ := (m : ℝ) * Q^2

theorem bandConstant_pos {m : ℕ} {Q : ℝ} (hm : 0 < m) (hQ : 1 ≤ Q) :
    0 < bandConstant m Q := by
  unfold bandConstant
  have hQr : 0 < Q := zero_lt_one.trans_le hQ
  positivity

/-- An exact finite balance forces one of finitely many explicit rational
power bands. In particular, no preexisting limit for `log v / log r` is used. -/
theorem exists_newton_power_band {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (index : ι → ℕ) (degree : ι → ℤ) (hinj : Function.Injective index)
    (u : ι → ℂ) {r v Q : ℝ} (hr : 0 < r) (hv : 0 < v) (hQ : 1 ≤ Q)
    (hlower : ∀ i, radialMonomial (degree i) (index i) r v ≤ Q * ‖u i‖)
    (hupper : ∀ i, ‖u i‖ ≤ Q * radialMonomial (degree i) (index i) r v)
    (hsum : ∑ i, u i = 0) :
    ∃ q ∈ candidateSlopes index degree,
      r^(q : ℝ) ≤ bandConstant (Fintype.card ι) Q * v ∧
      v ≤ bandConstant (Fintype.card ι) Q * r^(q : ℝ) := by
  obtain ⟨i, j, hij, hijm, hjim⟩ := exists_comparable_monomials u
    (fun i => radialMonomial (degree i) (index i) r v) hQ
    (fun i => radialMonomial_pos (degree i) (index i) hr hv) hlower hupper hsum
  have hK := bandConstant_pos (Fintype.card_pos : 0 < Fintype.card ι) hQ
  have hlog := log_band_of_comparable index degree hinj hij hr hv hK hijm hjim
  exact ⟨candidateSlope index degree i j, candidateSlope_mem index degree hij,
    power_band_of_log_band hr hv hK hlog⟩

/-- A central-index variable exceeding the uniform band constant cannot
lie in any nonpositive candidate-power band beyond radius one. -/
theorem positive_slope_of_power_upper {r v K ρ : ℝ} (hr : 1 ≤ r)
    (hK : 0 < K) (hv : K < v) (hupper : v ≤ K * r^ρ) : 0 < ρ := by
  by_contra h
  have hp : r^ρ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hr (le_of_not_gt h)
  have hbound := mul_le_mul_of_nonneg_left hp hK.le
  nlinarith

/-- The same actual finite balance yields a positive rational candidate as
soon as the central-index variable exceeds a fixed coefficient-dependent bound. -/
theorem exists_positive_newton_power_band
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (index : ι → ℕ) (degree : ι → ℤ) (hinj : Function.Injective index)
    (u : ι → ℂ) {r v Q : ℝ} (hr : 1 ≤ r) (hQ : 1 ≤ Q)
    (hv : bandConstant (Fintype.card ι) Q < v)
    (hlower : ∀ i, radialMonomial (degree i) (index i) r v ≤ Q * ‖u i‖)
    (hupper : ∀ i, ‖u i‖ ≤ Q * radialMonomial (degree i) (index i) r v)
    (hsum : ∑ i, u i = 0) :
    ∃ q ∈ candidateSlopes index degree, 0 < q ∧
      r^(q : ℝ) ≤ bandConstant (Fintype.card ι) Q * v ∧
      v ≤ bandConstant (Fintype.card ι) Q * r^(q : ℝ) := by
  have hK := bandConstant_pos (Fintype.card_pos : 0 < Fintype.card ι) hQ
  obtain ⟨q, hq, hlo, hhi⟩ := exists_newton_power_band index degree hinj u
    (zero_lt_one.trans_le hr) (hK.trans hv) hQ hlower hupper hsum
  have hqp : (0 : ℝ) < q := positive_slope_of_power_upper hr hK hv hhi
  exact ⟨q, hq, by exact_mod_cast hqp, hlo, hhi⟩

/-- The balance may hold only on a filter of good radii. Divergence of the
actual central index still eventually excludes all nonpositive candidates. -/
theorem eventually_positive_newton_power_bands
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (index : ι → ℕ) (degree : ι → ℤ) (hinj : Function.Injective index)
    {l : Filter ℝ} {v : ℝ → ℝ} {u : ℝ → ι → ℂ} {Q : ℝ} (hQ : 1 ≤ Q)
    (hr : Tendsto (fun r : ℝ => r) l atTop) (hv : Tendsto v l atTop)
    (hbalance : ∀ᶠ r in l,
      (∀ i, radialMonomial (degree i) (index i) r (v r) ≤ Q * ‖u r i‖) ∧
      (∀ i, ‖u r i‖ ≤ Q * radialMonomial (degree i) (index i) r (v r)) ∧
      ∑ i, u r i = 0) :
    ∀ᶠ r in l, ∃ q ∈ candidateSlopes index degree, 0 < q ∧
      r^(q : ℝ) ≤ bandConstant (Fintype.card ι) Q * v r ∧
      v r ≤ bandConstant (Fintype.card ι) Q * r^(q : ℝ) := by
  filter_upwards [hbalance, hr.eventually (eventually_ge_atTop 1),
    hv.eventually (eventually_gt_atTop (bandConstant (Fintype.card ι) Q))]
    with r hbalance hr hv
  exact exists_positive_newton_power_band index degree hinj (u r) hr hQ hv
    hbalance.1 hbalance.2.1 hbalance.2.2

/-- Equal original coefficient degrees give slope one after the usual
`z^(n-j)` scaling of the differential equation. -/
theorem candidateSlope_eq_one_of_common_diagonal {ι : Type*}
    (index : ι → ℕ) (degree : ι → ℤ) (hinj : Function.Injective index)
    {D : ℤ} (hdegree : ∀ i, degree i + (index i : ℤ) = D)
    {i j : ι} (hij : i ≠ j) : candidateSlope index degree i j = 1 := by
  have hidx : index i ≠ index j := fun h => hij (hinj h)
  have hden : (index i : ℚ) - index j ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hidx)
  have hnum : degree j - degree i = (index i : ℤ) - index j := by
    have hi := hdegree i
    have hj := hdegree j
    omega
  unfold candidateSlope
  rw [hnum]
  push_cast
  exact div_self hden

/-- In the common-degree case the actual balance already proves a linear
two-sided central-index bound. This finite-type bound needs no branch limit. -/
theorem linear_band_of_common_degree
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (index : ι → ℕ) (degree : ι → ℤ) (hinj : Function.Injective index)
    {D : ℤ} (hdegree : ∀ i, degree i + (index i : ℤ) = D)
    (u : ι → ℂ) {r v Q : ℝ} (hr : 0 < r) (hv : 0 < v) (hQ : 1 ≤ Q)
    (hlower : ∀ i, radialMonomial (degree i) (index i) r v ≤ Q * ‖u i‖)
    (hupper : ∀ i, ‖u i‖ ≤ Q * radialMonomial (degree i) (index i) r v)
    (hsum : ∑ i, u i = 0) :
    r ≤ bandConstant (Fintype.card ι) Q * v ∧
      v ≤ bandConstant (Fintype.card ι) Q * r := by
  obtain ⟨q, hq, hlo, hhi⟩ := exists_newton_power_band index degree hinj u
    hr hv hQ hlower hupper hsum
  obtain ⟨⟨i, j⟩, hij, heq⟩ := Finset.mem_image.mp hq
  have hne : i ≠ j := (Finset.mem_filter.mp hij).2
  have hqone : q = 1 := heq.symm.trans
    (candidateSlope_eq_one_of_common_diagonal index degree hinj hdegree hne)
  simpa only [hqone, Rat.cast_one, Real.rpow_one] using And.intro hlo hhi

#print axioms exists_comparable_terms
#print axioms exists_comparable_monomials
#print axioms radialMonomial_pos
#print axioms log_radialMonomial
#print axioms candidateSlope_mem
#print axioms one_le_abs_nat_sub
#print axioms log_band_of_comparable
#print axioms power_band_of_log_band
#print axioms bandConstant_pos
#print axioms exists_newton_power_band
#print axioms positive_slope_of_power_upper
#print axioms exists_positive_newton_power_band
#print axioms eventually_positive_newton_power_bands
#print axioms candidateSlope_eq_one_of_common_diagonal
#print axioms linear_band_of_common_degree

end HelmrathNewtonBranches
