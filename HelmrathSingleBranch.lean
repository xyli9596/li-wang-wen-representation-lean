import HelmrathRootApplication
import HelmrathBranchSelection

/-!
# The single central-index branch for an actual polynomial ODE

This combines Wiman--Valiron substitution, Newton root clustering, and
monotone branch selection. The conclusion holds at all sufficiently large
radii, without an exceptional set.
-/

noncomputable section
open Filter Set
open scoped Topology

namespace HelmrathODE
open WimanValiron

theorem polynomial_ode_single_branch
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (index : ι → ℕ) (hinj : Function.Injective index) (n : ℕ)
    (hindex : ∀ i, index i ≤ n) (a : ι → Polynomial ℂ) (ha : ∀ i, a i ≠ 0)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnp : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z)
    (hode : ∀ z, ∑ i, (a i).eval z * iteratedDeriv (index i) f z = 0) :
    ∃ q : ℚ, 0 < q ∧ ∃ c : ℝ, 0 < c ∧
      Tendsto (fun r : ℝ => (centralIndex (taylorCoeff f) r : ℝ)/r^(q : ℝ))
        atTop (𝓝 c) := by
  obtain ⟨E, hEm, hE, _, C, hC, happ⟩ :=
    polynomial_ode_root_candidates index hinj n hindex a ha hf hnp hode
  have hfne : f ≠ 0 := by
    intro h
    exact hnp ⟨0, by simp [h]⟩
  have hmono : MonotoneOn (fun r => (centralIndex (taylorCoeff f) r : ℝ)) (Ioi 0) := by
    intro r hr s hs hrs
    change (centralIndex (taylorCoeff f) r : ℝ) ≤ (centralIndex (taylorCoeff f) s : ℝ)
    exact_mod_cast taylor_centralIndex_monotone hf hfne hr hs hrs
  obtain ⟨p, hp, hlim⟩ := HelmrathBranchSelection.exists_single_power_branch_finset
    C hEm hE hmono hC happ
  exact ⟨p.1, (hC p hp).1, p.2, (hC p hp).2, hlim⟩

#print axioms polynomial_ode_single_branch
end HelmrathODE
