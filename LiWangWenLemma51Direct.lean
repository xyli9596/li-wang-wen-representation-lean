import LiWangWenWimanValironUpper
import LiWangWenWimanValironLowerBound

/-!
# A direct repair of Lemma 5.1 using two-sided central-index bounds

This proof retains the Wiman--Valiron order of reasoning. It uses neither
Fourier classification nor an exponential-sum representation of the solution,
and it does not assume or prove convergence of the central-index/radius ratio.
The vertical estimate follows from finite-order periodic reduction; grouped
coefficient noncancellation, local angular movement, and the actual ODE give
the two central-index bounds. The maximum-term bridge supplies order and type.
-/

noncomputable section
open Filter
open scoped Topology

namespace LiWangWen

/-- The sufficient replacement for the unneeded assertion `nu(r) ~ C*r`. -/
theorem lemma_5_1_centralIndex_linear_bounds {n : ℕ}
    {P : Fin (n+1) → Polynomial ℂ} (hlead : P (Fin.last n) = 1)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hfo : CRGOrder.FiniteOrder f)
    (hnp : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z) (hsol : Solves P f) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ r : ℝ in atTop,
      c*r ≤ (WimanValiron.centralIndex (WimanValiron.taylorCoeff f) r : ℝ) ∧
      (WimanValiron.centralIndex (WimanValiron.taylorCoeff f) r : ℝ) ≤ C*r := by
  obtain ⟨c,hc,hlo⟩ := monic_direct_centralIndex_eventually_linear_lower hf hnp hlead hsol
  obtain ⟨C,hC,hhi⟩ := finiteOrder_solution_direct_centralIndex_linear_upper
    (by simp [hlead]) hf hnp hfo hsol
  refine ⟨c,C+1,hc,by positivity,?_⟩
  filter_upwards [hlo,hhi,eventually_ge_atTop (0 : ℝ)] with r hrlo hrhi hr
  exact ⟨hrlo,hrhi.trans (by nlinarith)⟩

/-- The complete direct proof of the actual statement of Lemma 5.1. -/
theorem lemma_5_1_direct {n : ℕ} {P : Fin (n+1) → Polynomial ℂ}
    (hlead : P (Fin.last n) = 1) {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hfo : CRGOrder.FiniteOrder f)
    (hnp : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z) (hsol : Solves P f) :
    CRGOrder.IsOrder f 1 ∧ LevinGrowth.FinitePositiveType f 1 := by
  obtain ⟨c,C,hc,hC,hbounds⟩ := lemma_5_1_centralIndex_linear_bounds hlead hf hfo hnp hsol
  have hne : f ≠ 0 := by intro h; exact hnp ⟨0,by simp [h]⟩
  exact WimanValiron.order_and_type_of_centralIndex_linear_bounds hf hne hc hC.le hbounds

#print axioms lemma_5_1_centralIndex_linear_bounds
#print axioms lemma_5_1_direct
end LiWangWen
