import LiWangWenTheorem35Direct
import LiWangWenRepresentation
import LiWangWenLaurentNormalization

set_option autoImplicit false
noncomputable section
open Polynomial
open scoped BigOperators

namespace LiWangWen

/-- A nontrivial finite-order solution space contains a nonzero translation
 eigenfunction; no diagonalizability of the translation is required. -/
theorem finiteOrder_solution_has_eigenfunction {n : ℕ}
    {P : Fin (n+1) → Polynomial ℂ} (hlead : (P (Fin.last n)).eval 1 ≠ 0)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hfo : CRGOrder.FiniteOrder f)
    (hsol : Solves P f) (hne : f ≠ 0) :
    ∃ g : ℂ → ℂ, ∃ c : ℂ, g ≠ 0 ∧ c ≠ 0 ∧
      Differentiable ℂ g ∧ CRGOrder.FiniteOrder g ∧ Solves P g ∧
      ∀ z, g (z+exponentialPeriod) = c*g z := by
  let a : Fin (n+1) → ℂ → ℂ := fun j z => (P j).eval (Complex.exp z)
  have ha : ∀ j, Differentiable ℂ (a j) :=
    fun j => (P j).differentiable.comp Complex.differentiable_exp
  have hl : a (Fin.last n) 0 ≠ 0 := by simpa [a] using hlead
  have hp : ∀ j, Function.Periodic (a j) exponentialPeriod := by
    intro j
    simpa only [a, frequencyPeriod, div_one, one_mul, Function.comp_def] using
      frequency_coefficients_periodic P (ω := 1) one_ne_zero j
  let V := powerBoundSolutionSpace a
  let T := powerBoundTranslateEquiv a exponentialPeriod hp
  let v : V := ⟨f, ⟨hf,hsol⟩, power_bound_of_finiteOrder hf hfo⟩
  let := powerBoundSolutionSpace_finiteDimensional ha hl
  have hv : v ≠ 0 := by
    intro h
    apply hne
    exact congrArg Subtype.val h
  let : Nontrivial V := nontrivial_of_ne v 0 hv
  obtain ⟨c,hc⟩ := Module.End.exists_eigenvalue T.toLinearMap
  obtain ⟨w,hw⟩ := hc.exists_hasEigenvector
  have hcn : c ≠ 0 := by
    intro h
    have ht : T w = T 0 := by simpa [h] using hw.apply_eq_smul
    exact hw.2 (T.injective ht)
  have hwn : (w : ℂ → ℂ) ≠ 0 := by
    intro h
    exact hw.2 (Subtype.ext h)
  refine ⟨w,c,hwn,hcn,w.property.1.1,w.property.2.finiteOrder,w.property.1.2,?_⟩
  intro z
  have he := congrArg (fun x : V => (x : ℂ → ℂ) z) hw.apply_eq_smul
  exact he

/-- Extract a normalized polynomial solution from any nonzero finite-order
 entire solution of the original equation. -/
theorem finiteOrder_solution_has_normalized_polynomial_solution {n : ℕ}
    {P : Fin (n+1) → Polynomial ℂ} (hlead : (P (Fin.last n)).eval 1 ≠ 0)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hfo : CRGOrder.FiniteOrder f)
    (hsol : Solves P f) (hne : f ≠ 0) :
    ∃ a : ℂ, ∃ u : Polynomial ℂ, u.eval 0 ≠ 0 ∧
      transformedOperator P a u = 0 ∧ indicial P a = 0 := by
  obtain ⟨g,c,hgn,hcn,hg,hgfo,hgs,hge⟩ :=
    finiteOrder_solution_has_eigenfunction hlead hf hfo hsol hne
  obtain ⟨a,p,ha,hp,hper,hrep⟩ := IncePeriodic.eigenfunction_factorization
    exponentialPeriod_ne_zero hcn hg hge
  have hpne : p ≠ 0 := by
    intro h
    apply hgn
    funext z
    simp [hrep z,h]
  have hgb := finiteOrder_solution_exponentialBound_direct hlead hg hgfo hgs
  have hpb : ExponentialBound p := by
    have h := hgb.remove_exponential a
    have he : (fun z => Complex.exp (-a*z)*g z) = p := by
      funext z
      rw [hrep z,← mul_assoc,← Complex.exp_add]
      simp
    rwa [he] at h
  obtain ⟨m,u,hu0,hpu⟩ := finite_fourier_normalized_lift hp hper
    (periodic_exponentialBound_finiteFourier_support hp hper hpb) hpne
  have he : g = lift (a+(m : ℂ)) u := by
    funext z
    rw [hrep z,hpu]
    dsimp [lift]
    rw [add_mul,Complex.exp_add]
    ring
  have hs : Solves P (lift (a+(m : ℂ)) u) := by rwa [← he]
  exact ⟨a+(m : ℂ),u,hu0,(transformed_eq_zero_iff P _ u).mpr hs,
    indicial_eq_zero_of_normalized_solution P _ u hu0 hs⟩

/-- Corollary 3.3 in the exact shifted-Euler formulation of (3.3).
 Both sides concern nontrivial solutions. -/
theorem corollary_3_3 {n : ℕ} {P : Fin (n+1) → Polynomial ℂ}
    (hlead : P (Fin.last n) = 1) :
    (∃ f : ℂ → ℂ, Differentiable ℂ f ∧ CRGOrder.FiniteOrder f ∧
      Solves P f ∧ f ≠ 0) ↔
    (∃ a : ℂ, ∃ u : Polynomial ℂ, u.eval 0 ≠ 0 ∧
      transformedOperator P a u = 0 ∧ indicial P a = 0) := by
  constructor
  · rintro ⟨f,hf,hfo,hsol,hne⟩
    exact finiteOrder_solution_has_normalized_polynomial_solution
      (by simp [hlead]) hf hfo hsol hne
  · rintro ⟨a,u,hu0,hs,_ha⟩
    have hun : u ≠ 0 := by intro h; simp [h] at hu0
    exact ⟨lift a u,lift_entire a u,(bound_lift a u).finiteOrder,
      (transformed_eq_zero_iff P a u).mp hs,lift_ne_zero_of_polynomial_ne_zero a hun⟩

/-- Extract a normalized polynomial solution through the factorial-recurrence
 representation, without using the direct Wiman--Valiron growth bound. -/
theorem finiteOrder_solution_has_normalized_polynomial_solution_recurrence {n : ℕ}
    {P : Fin (n+1) → Polynomial ℂ} (hlead : (P (Fin.last n)).eval 1 ≠ 0)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hfo : CRGOrder.FiniteOrder f)
    (hsol : Solves P f) (hne : f ≠ 0) :
    ∃ a : ℂ, ∃ u : Polynomial ℂ, u.eval 0 ≠ 0 ∧
      transformedOperator P a u = 0 ∧ indicial P a = 0 := by
  obtain ⟨g,c,hgn,hcn,hg,hgfo,hgs,hge⟩ :=
    finiteOrder_solution_has_eigenfunction hlead hf hfo hsol hne
  obtain ⟨a,p,ha,hp,hper,hrep⟩ := IncePeriodic.eigenfunction_factorization
    exponentialPeriod_ne_zero hcn hg hge
  have hpne : p ≠ 0 := by
    intro h
    apply hgn
    funext z
    simp [hrep z,h]
  have hgb := finiteOrder_solution_exponentialBound_of_leading_eval hlead hg hgfo hgs
  have hpb : ExponentialBound p := by
    have h := hgb.remove_exponential a
    have he : (fun z => Complex.exp (-a*z)*g z) = p := by
      funext z
      rw [hrep z,← mul_assoc,← Complex.exp_add]
      simp
    rwa [he] at h
  obtain ⟨m,u,hu0,hpu⟩ := finite_fourier_normalized_lift hp hper
    (periodic_exponentialBound_finiteFourier_support hp hper hpb) hpne
  have he : g = lift (a+(m : ℂ)) u := by
    funext z
    rw [hrep z,hpu]
    dsimp [lift]
    rw [add_mul,Complex.exp_add]
    ring
  have hs : Solves P (lift (a+(m : ℂ)) u) := by rwa [← he]
  exact ⟨a+(m : ℂ),u,hu0,(transformed_eq_zero_iff P _ u).mpr hs,
    indicial_eq_zero_of_normalized_solution P _ u hu0 hs⟩

/-- The factorial-recurrence route to Corollary 3.3 in the exact shifted-Euler formulation of (3.3).
 Both sides concern nontrivial solutions. -/
theorem corollary_3_3_recurrence {n : ℕ} {P : Fin (n+1) → Polynomial ℂ}
    (hlead : P (Fin.last n) = 1) :
    (∃ f : ℂ → ℂ, Differentiable ℂ f ∧ CRGOrder.FiniteOrder f ∧
      Solves P f ∧ f ≠ 0) ↔
    (∃ a : ℂ, ∃ u : Polynomial ℂ, u.eval 0 ≠ 0 ∧
      transformedOperator P a u = 0 ∧ indicial P a = 0) := by
  constructor
  · rintro ⟨f,hf,hfo,hsol,hne⟩
    exact finiteOrder_solution_has_normalized_polynomial_solution_recurrence
      (by simp [hlead]) hf hfo hsol hne
  · rintro ⟨a,u,hu0,hs,_ha⟩
    have hun : u ≠ 0 := by intro h; simp [h] at hu0
    exact ⟨lift a u,lift_entire a u,(bound_lift a u).finiteOrder,
      (transformed_eq_zero_iff P a u).mp hs,lift_ne_zero_of_polynomial_ne_zero a hun⟩

#print axioms finiteOrder_solution_has_eigenfunction
#print axioms finiteOrder_solution_has_normalized_polynomial_solution
#print axioms corollary_3_3
#print axioms finiteOrder_solution_has_normalized_polynomial_solution_recurrence
#print axioms corollary_3_3_recurrence
end LiWangWen
