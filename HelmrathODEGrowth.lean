import HelmrathODEApplication
import WimanValironGrowthBridge

/-!
# Exponential type for common-degree polynomial differential equations

This is a complete application of the actual Wiman--Valiron derivative theorem,
the finite Newton-band argument, and the maximum-term growth bridge. It concerns
polynomial coefficients in the independent variable, and must not be confused
with the distinct exponential-polynomial-coefficient lemma in Li--Wang--Wen.
-/

set_option autoImplicit false
noncomputable section
open Filter Finset Set
open scoped Topology

namespace HelmrathODE

/-- Every entire solution of a polynomial-coefficient ODE whose participating
nonzero coefficients all have the same degree has a global exponential bound.
Polynomial solutions, including zero, are included. -/
theorem common_degree_polynomial_ode_exponentialBound
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (index : ι → ℕ) (hinj : Function.Injective index) (n : ℕ)
    (hindex : ∀ i, index i ≤ n) (a : ι → Polynomial ℂ) (ha : ∀ i, a i ≠ 0)
    (D : ℕ) (hdegree : ∀ i, (a i).natDegree = D)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hode : ∀ z, ∑ i, (a i).eval z * iteratedDeriv (index i) f z = 0) :
    LiWangWen.ExponentialBound f := by
  by_cases hp : ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z
  · obtain ⟨p, hp⟩ := hp
    have heq : f = fun z => p.eval z := funext hp
    rw [heq]
    exact LiWangWen.bound_poly_comp p LiWangWen.bound_id
  obtain ⟨E, hEm, hE, _hnebot, K, hK, hbands⟩ :=
    common_degree_polynomial_ode_linear_bands index hinj n hindex a ha D hdegree hf hp hode
  exact WimanValiron.exponentialBound_of_centralIndex_le_off_finite_logarithmic_set
    hf hEm hE hK.le (hbands.mono (fun _ h => h.2))

/-- The same actual common-degree ODE application also gives finite order. -/
theorem common_degree_polynomial_ode_finiteOrder
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (index : ι → ℕ) (hinj : Function.Injective index) (n : ℕ)
    (hindex : ∀ i, index i ≤ n) (a : ι → Polynomial ℂ) (ha : ∀ i, a i ≠ 0)
    (D : ℕ) (hdegree : ∀ i, (a i).natDegree = D)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hode : ∀ z, ∑ i, (a i).eval z * iteratedDeriv (index i) f z = 0) :
    CRGOrder.FiniteOrder f :=
  (common_degree_polynomial_ode_exponentialBound index hinj n hindex a ha D hdegree hf hode).finiteOrder

end HelmrathODE

#print axioms HelmrathODE.common_degree_polynomial_ode_exponentialBound
#print axioms HelmrathODE.common_degree_polynomial_ode_finiteOrder
