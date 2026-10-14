import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Tactic

/-!
# Polynomial coefficients in the Wiman--Valiron substitution

These estimates are derived from actual polynomial coefficients. In particular,
no leading-term approximation is required as an extra ODE hypothesis.
-/

set_option autoImplicit false
noncomputable section
open Filter Finset Asymptotics
open scoped Topology

namespace HelmrathODE

/-- The leading coefficient is the limit of the normalized polynomial along
any points whose moduli tend to infinity; their arguments may vary freely. -/
theorem polynomial_normalized_tendsto {α : Type*} {l : Filter α}
    (p : Polynomial ℂ) (hp : p ≠ 0) {z : α → ℂ}
    (hz : Tendsto (fun x => ‖z x‖) l atTop) :
    Tendsto (fun x => p.eval (z x) / (z x)^p.natDegree) l (𝓝 p.leadingCoeff) := by
  have hzc : Tendsto z l (Bornology.cobounded ℂ) :=
    tendsto_norm_atTop_iff_cobounded.mp hz
  have hlead : ∀ᶠ x in l, p.leadingCoeff * (z x)^p.natDegree ≠ 0 := by
    filter_upwards [hz.eventually (eventually_gt_atTop (0 : ℝ))] with x hx
    exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hp)
      (pow_ne_zero _ (norm_pos_iff.mp hx))
  have heq := (Polynomial.isEquivalent_cobounded_leading_monomial (P := p)).comp_tendsto hzc
  have hlim := (isEquivalent_iff_tendsto_one hlead).mp heq
  have h := hlim.const_mul p.leadingCoeff
  simp only [mul_one] at h
  convert h using 1
  funext x
  dsimp only [Pi.div_apply, Function.comp_def]
  field_simp [Polynomial.leadingCoeff_ne_zero.mpr hp]

/-- A finite family of nonzero limiting multipliers admits a common positive
two-sided bound. This will be applied to normalized coefficients times the
actual normalized derivative ratios. -/
theorem eventually_uniform_multiplier_bounds {α ι : Type*} [Fintype ι]
    {l : Filter α} {a : α → ι → ℂ} {c : ι → ℂ}
    (hc : ∀ i, c i ≠ 0) (ha : ∀ i, Tendsto (fun x => a x i) l (𝓝 (c i))) :
    ∃ Q : ℝ, 1 ≤ Q ∧ ∀ᶠ x in l, ∀ i, 1 ≤ Q * ‖a x i‖ ∧ ‖a x i‖ ≤ Q := by
  classical
  let b : ι → ℝ := fun i => 2 * ‖c i‖ + 2 / ‖c i‖
  let Q : ℝ := 1 + ∑ i, b i
  have hcp : ∀ i, 0 < ‖c i‖ := fun i => norm_pos_iff.mpr (hc i)
  have hb : ∀ i, 0 ≤ b i := by intro i; dsimp [b]; positivity
  have hQ : 1 ≤ Q := by
    dsimp [Q]
    exact le_add_of_nonneg_right (sum_nonneg (fun i _ => hb i))
  have hbQ : ∀ i, b i ≤ Q := by
    intro i
    have hi := single_le_sum (fun j _ => hb j) (mem_univ i)
    dsimp [Q]
    linarith
  refine ⟨Q, hQ, ?_⟩
  rw [eventually_all]
  intro i
  have hlo := (ha i).norm.eventually_const_lt (show ‖c i‖ / 2 < ‖c i‖ by linarith [hcp i])
  have hhi := (ha i).norm.eventually_lt_const (show ‖c i‖ < 2 * ‖c i‖ by linarith [hcp i])
  filter_upwards [hlo, hhi] with x hxlo hxhi
  have hbq := hbQ i
  dsimp [b] at hbq
  have hinv : 2 / ‖c i‖ ≤ Q := by linarith [hcp i]
  have hmul : 2 ≤ Q * ‖c i‖ := (div_le_iff₀ (hcp i)).mp hinv
  constructor
  · nlinarith
  · have hdiv : 0 < 2 / ‖c i‖ := div_pos (by norm_num) (hcp i)
    linarith

end HelmrathODE

#print axioms HelmrathODE.polynomial_normalized_tendsto
#print axioms HelmrathODE.eventually_uniform_multiplier_bounds
