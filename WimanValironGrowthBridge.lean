import WimanValironCircleBounds
import LiWangWenGrowth
import HelmrathExceptionalSet

/-!
# From the actual central index to exponential type

An eventual linear upper bound on the central index controls successive
maximum terms. Iterating that elementary estimate and summing the Taylor
series gives a global exponential bound for the entire function itself.
Finite logarithmic measure exceptions can be removed by monotonicity.
-/

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Topology

namespace WimanValiron

/-- Comparing maximum terms uses the maximizing index at the outer radius. -/
theorem maximumTerm_le_radius_ratio {a : ℕ → ℂ} {r s : ℝ}
    (hr : Admissible a r) (hs : Admissible a s) :
    maximumTerm a s ≤ maximumTerm a r * (s / r) ^ centralIndex a s := by
  unfold maximumTerm
  rw [term_change_radius a (ne_of_gt hr.1) s]
  exact mul_le_mul_of_nonneg_right (term_le_maximumTerm hr _)
    (pow_nonneg (div_nonneg hs.1.le hr.1.le) _)

/-- A central-index bound controls one unit of radial growth. -/
theorem maximumTerm_add_one_le {a : ℕ → ℂ} {r C : ℝ}
    (hr : Admissible a r) (hs : Admissible a (r + 1))
    (hr1 : 1 ≤ r) (hC : 0 ≤ C)
    (hν : (centralIndex a (r + 1) : ℝ) ≤ C * (r + 1)) :
    maximumTerm a (r + 1) ≤ maximumTerm a r * Real.exp (2 * C) := by
  have hratio : (r + 1) / r ≤ Real.exp (1 / r) := by
    calc
      (r + 1) / r = 1 / r + 1 := by field_simp; ring
      _ ≤ _ := Real.add_one_le_exp _
  have hexponent : (centralIndex a (r + 1) : ℝ) * (1 / r) ≤ 2 * C := by
    rw [mul_one_div]
    apply (div_le_iff₀ hr.1).mpr
    nlinarith
  calc
    maximumTerm a (r + 1)
        ≤ maximumTerm a r * ((r + 1) / r) ^ centralIndex a (r + 1) :=
      maximumTerm_le_radius_ratio hr hs
    _ ≤ maximumTerm a r * (Real.exp (1 / r)) ^ centralIndex a (r + 1) := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (div_nonneg hs.1.le hr.1.le) hratio _)
        (maximumTerm_pos hr).le
    _ = maximumTerm a r * Real.exp ((centralIndex a (r + 1) : ℝ) * (1 / r)) := by
      rw [Real.exp_nat_mul]
    _ ≤ maximumTerm a r * Real.exp (2 * C) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) (maximumTerm_pos hr).le

/-- Integer radial steps integrate a linear central-index bound without
requiring differentiability of the maximum-term function. -/
theorem maximumTerm_add_nat_le {a : ℕ → ℂ} {R C : ℝ}
    (ha : ∀ r > 0, Admissible a r) (hR : 1 ≤ R) (hC : 0 ≤ C)
    (hν : ∀ r ≥ R, (centralIndex a r : ℝ) ≤ C * r) (n : ℕ) :
    maximumTerm a (R + n) ≤ maximumTerm a R * Real.exp (2 * C * n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hr : 1 ≤ R + (n : ℝ) := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hpos : 0 < R + (n : ℝ) := zero_lt_one.trans_le hr
    have hs : 0 < R + (n : ℝ) + 1 := by positivity
    calc
      maximumTerm a (R + (n + 1 : ℕ))
          = maximumTerm a (R + (n : ℝ) + 1) := by congr 1; push_cast; ring
      _ ≤ maximumTerm a (R + n) * Real.exp (2 * C) :=
        maximumTerm_add_one_le (ha _ hpos) (ha _ hs) hr hC
          (hν _ (by nlinarith [Nat.cast_nonneg (α := ℝ) n]))
      _ ≤ (maximumTerm a R * Real.exp (2 * C * n)) * Real.exp (2 * C) :=
        mul_le_mul_of_nonneg_right ih (Real.exp_pos _).le
      _ = maximumTerm a R * Real.exp (2 * C * (n + 1 : ℕ)) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        push_cast
        ring

/-- An eventual linear central-index bound gives an exponential bound on
the actual maximum term at every positive radius. -/
theorem maximumTerm_le_exp_of_centralIndex_le {a : ℕ → ℂ} {R C : ℝ}
    (ha : ∀ r > 0, Admissible a r) (hR : 1 ≤ R) (hC : 0 ≤ C)
    (hν : ∀ r ≥ R, (centralIndex a r : ℝ) ≤ C * r)
    {r : ℝ} (hr : 0 < r) :
    maximumTerm a r ≤ maximumTerm a R * Real.exp (2 * C) * Real.exp (2 * C * r) := by
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hceil : r ≤ (⌈r⌉₊ : ℝ) := Nat.le_ceil r
  have hceil' : (⌈r⌉₊ : ℝ) ≤ r + 1 := (Nat.ceil_lt_add_one hr.le).le
  calc
    maximumTerm a r ≤ maximumTerm a (R + (⌈r⌉₊ : ℝ)) :=
      maximumTerm_le (ha r hr) (ha _ (by positivity)) (by linarith)
    _ ≤ maximumTerm a R * Real.exp (2 * C * (⌈r⌉₊ : ℝ)) :=
      maximumTerm_add_nat_le ha hR hC hν _
    _ ≤ maximumTerm a R * Real.exp (2 * C * (r + 1)) := by
      apply mul_le_mul_of_nonneg_left _ (maximumTerm_pos (ha _ hRpos)).le
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left hceil' (by positivity)
    _ = maximumTerm a R * Real.exp (2 * C) * Real.exp (2 * C * r) := by
      rw [mul_assoc (maximumTerm a R), ← Real.exp_add]
      congr 2
      ring

/-- A global exponential-type bound follows from the eventual upper bound
on the genuine Taylor central index. The zero function is included. -/
theorem exponentialBound_of_centralIndex_le {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {C R : ℝ} (hC : 0 ≤ C)
    (hν : ∀ r ≥ R, (centralIndex (taylorCoeff f) r : ℝ) ≤ C * r) :
    LiWangWen.ExponentialBound f := by
  by_cases hne : f = 0
  · subst f
    exact LiWangWen.bound_const (0 : ℂ)
  have ha := fun r hr => taylor_admissible hf hne (r := r) hr
  let R' := max 1 R
  have hR' : 1 ≤ R' := le_max_left _ _
  have hμ : 0 < maximumTerm (taylorCoeff f) R' :=
    maximumTerm_pos (ha _ (zero_lt_one.trans_le hR'))
  refine ⟨2 * maximumTerm (taylorCoeff f) R' * Real.exp (4 * C), 4 * C,
    by positivity, by positivity, fun z => ?_⟩
  let s : ℝ := 2 * ‖z‖ + 1
  have hs : 0 < s := by dsimp [s]; positivity
  have hzs : ‖z‖ < s := by dsimp [s]; nlinarith [norm_nonneg z]
  have hden : 1 / 2 ≤ 1 - ‖z‖ / s := by
    have : ‖z‖ / s ≤ 1 / 2 := (div_le_iff₀ hs).mpr (by dsimp [s]; linarith)
    linarith
  have hbound := maximumTerm_le_exp_of_centralIndex_le ha hR' hC
    (fun r hr => hν r ((le_max_right 1 R).trans hr)) hs
  calc
    ‖f z‖ ≤ maximumTerm (taylorCoeff f) s / (1 - ‖z‖ / s) :=
      norm_le_maximumTerm_div hf hne hzs
    _ ≤ 2 * maximumTerm (taylorCoeff f) s := by
      apply (div_le_iff₀ (by linarith : 0 < 1 - ‖z‖ / s)).mpr
      nlinarith [maximumTerm_pos (ha s hs)]
    _ ≤ 2 * (maximumTerm (taylorCoeff f) R' * Real.exp (2 * C) *
        Real.exp (2 * C * s)) := mul_le_mul_of_nonneg_left hbound (by norm_num)
    _ = (2 * maximumTerm (taylorCoeff f) R' * Real.exp (4 * C)) *
        Real.exp (4 * C * ‖z‖) := by
      calc
        _ = (2 * maximumTerm (taylorCoeff f) R') *
            (Real.exp (2 * C) * Real.exp (2 * C * s)) := by ring
        _ = (2 * maximumTerm (taylorCoeff f) R') *
            Real.exp (2 * C + 2 * C * s) := by rw [Real.exp_add]
        _ = (2 * maximumTerm (taylorCoeff f) R') *
            Real.exp (4 * C + 4 * C * ‖z‖) := by congr 2; dsimp [s]; ring
        _ = _ := by rw [Real.exp_add]; ring

/-- The same bridge in filter form, as produced by asymptotic estimates. -/
theorem exponentialBound_of_centralIndex_eventually_le {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {C : ℝ} (hC : 0 ≤ C)
    (hν : ∀ᶠ r : ℝ in atTop, (centralIndex (taylorCoeff f) r : ℝ) ≤ C * r) :
    LiWangWen.ExponentialBound f := by
  obtain ⟨R, hR⟩ := eventually_atTop.mp hν
  exact exponentialBound_of_centralIndex_le hf hC hR

/-- Monotonicity removes a zero-density radial exception from a linear upper
bound. The constant is doubled by choosing a good radius in `[r, 2r]`. -/
theorem centralIndex_eventually_le_of_zero_density_exception {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hne : f ≠ 0) {E : Set ℝ}
    (hE : LevinDensity.ZeroRadialDensity E) {C : ℝ} (hC : 0 ≤ C)
    (hν : ∀ᶠ r : ℝ in atTop ⊓ 𝓟 Eᶜ,
      (centralIndex (taylorCoeff f) r : ℝ) ≤ C * r) :
    ∀ᶠ r : ℝ in atTop, (centralIndex (taylorCoeff f) r : ℝ) ≤ (2 * C) * r := by
  obtain ⟨R, hR⟩ := eventually_atTop.mp (Filter.eventually_inf_principal.mp hν)
  filter_upwards [HelmrathExceptionalSet.exists_good_radius hE
    (show (0 : ℝ) ≤ 1 by norm_num) (show (1 : ℝ) < 2 by norm_num),
    eventually_ge_atTop (max 1 R)] with r hs hr
  obtain ⟨s, hs, hsE⟩ := hs
  have hrpos : 0 < r := zero_lt_one.trans_le ((le_max_left _ _).trans hr)
  have hrs : r ≤ s := by simpa using hs.1
  have hspos : 0 < s := hrpos.trans_le hrs
  have hmono : (centralIndex (taylorCoeff f) r : ℝ) ≤ centralIndex (taylorCoeff f) s := by
    exact_mod_cast centralIndex_le (taylor_admissible hf hne hrpos)
      (taylor_admissible hf hne hspos) hrs
  have hbound := hR s (((le_max_right _ _).trans hr).trans hrs) hsE
  calc
    (centralIndex (taylorCoeff f) r : ℝ) ≤ centralIndex (taylorCoeff f) s := hmono
    _ ≤ C * s := hbound
    _ ≤ (2 * C) * r := by nlinarith [mul_le_mul_of_nonneg_left hs.2 hC]

/-- A bound outside an actual finite-logarithmic-measure set suffices for a
global exponential bound for the entire function. -/
theorem exponentialBound_of_centralIndex_le_off_finite_logarithmic_set
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {E : Set ℝ}
    (hEm : MeasurableSet E) (hE : HelmrathExceptionalSet.FiniteLogarithmicMeasure E)
    {C : ℝ} (hC : 0 ≤ C)
    (hν : ∀ᶠ r : ℝ in atTop ⊓ 𝓟 Eᶜ,
      (centralIndex (taylorCoeff f) r : ℝ) ≤ C * r) :
    LiWangWen.ExponentialBound f := by
  by_cases hne : f = 0
  · subst f
    exact LiWangWen.bound_const (0 : ℂ)
  exact exponentialBound_of_centralIndex_eventually_le hf (by positivity)
    (centralIndex_eventually_le_of_zero_density_exception hf hne
      (HelmrathExceptionalSet.zero_density_of_finite_logarithmic_measure hEm hE) hC hν)

#print axioms maximumTerm_le_radius_ratio
#print axioms maximumTerm_add_one_le
#print axioms maximumTerm_add_nat_le
#print axioms maximumTerm_le_exp_of_centralIndex_le
#print axioms exponentialBound_of_centralIndex_le
#print axioms exponentialBound_of_centralIndex_eventually_le
#print axioms centralIndex_eventually_le_of_zero_density_exception
#print axioms exponentialBound_of_centralIndex_le_off_finite_logarithmic_set

end WimanValiron
