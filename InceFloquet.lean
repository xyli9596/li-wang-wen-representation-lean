import IncePeriodic
import InceSolutionSpace
import InceExponentialConjugation
import InceFiniteDifference
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.List.OfFn

/-!
# Scalar Floquet representations on finite-dimensional translation spaces

A Floquet term is an exponential times a monomial times an actual entire
periodic function. Finite sums of these terms are explicit scalar Floquet
representations. The spectral step below uses the generalized eigenspace
decomposition of an invertible translation operator over the complex numbers.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace IncePeriodic

/-- One scalar Floquet term, with an actual entire periodic coefficient. -/
structure FloquetTerm (h : ℂ) where
  exponent : ℂ
  degree : ℕ
  coefficient : ℂ → ℂ
  entire : Differentiable ℂ coefficient
  periodic : Function.Periodic coefficient h

/-- Evaluation of an exponential-polynomial term with periodic coefficient. -/
def FloquetTerm.eval {h : ℂ} (t : FloquetTerm h) (z : ℂ) : ℂ :=
  Complex.exp (t.exponent * z) * z ^ t.degree * t.coefficient z

/-- An explicit finite scalar Floquet sum. Repeated exponents are allowed. -/
def HasFloquetRepresentation (h : ℂ) (f : ℂ → ℂ) : Prop :=
  ∃ terms : List (FloquetTerm h), ∀ z, f z = (terms.map (fun t => t.eval z)).sum

theorem hasFloquetRepresentation_zero (h : ℂ) :
    HasFloquetRepresentation h (0 : ℂ → ℂ) := by
  exact ⟨[], by simp⟩

/-- Scalar Floquet representations are closed under addition. -/
theorem HasFloquetRepresentation.add {h : ℂ} {f g : ℂ → ℂ}
    (hf : HasFloquetRepresentation h f) (hg : HasFloquetRepresentation h g) :
    HasFloquetRepresentation h (f + g) := by
  obtain ⟨s, hs⟩ := hf
  obtain ⟨t, ht⟩ := hg
  refine ⟨s ++ t, ?_⟩
  intro z
  simp only [List.map_append, List.sum_append, Pi.add_apply, hs, ht]

/-- A finite polynomial in the variable with entire periodic coefficients
gives the corresponding finite list of scalar Floquet terms. -/
theorem hasFloquetRepresentation_of_polynomial {h a : ℂ} {f : ℂ → ℂ}
    (k : ℕ) (p : ℕ → ℂ → ℂ)
    (hp : ∀ j < k, Differentiable ℂ (p j) ∧ Function.Periodic (p j) h)
    (hf : ∀ z, f z = Complex.exp (a * z) * ∑ j ∈ Finset.range k, z ^ j * p j z) :
    HasFloquetRepresentation h f := by
  let t : Fin k → FloquetTerm h := fun j =>
    ⟨a, j.val, p j.val, (hp j.val j.isLt).1, (hp j.val j.isLt).2⟩
  refine ⟨List.ofFn t, ?_⟩
  intro z
  rw [hf, List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_apply, FloquetTerm.eval, t]
  rw [Fin.sum_univ_eq_sum_range (fun j => Complex.exp (a * z) * z ^ j * p j z)]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Every power of an invertible linear map is injective. -/
theorem linearEquiv_pow_injective {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : V ≃ₗ[ℂ] V) (k : ℕ) : Function.Injective (T.toLinearMap ^ k) := by
  induction k with
  | zero => intro v w hvw; simpa only [pow_zero, Module.End.one_apply] using hvw
  | succ k ih =>
    intro v w hvw
    apply ih
    apply T.injective
    simpa [pow_succ', Module.End.mul_apply] using hvw

/-- The zero multiplier contributes only the zero vector for an invertible
translation operator. -/
theorem zero_multiplier_kernel {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : V ≃ₗ[ℂ] V) (k : ℕ) {v : V}
    (hv : ((T.toLinearMap - (0 : ℂ) • 1) ^ k) v = 0) : v = 0 := by
  apply linearEquiv_pow_injective T k
  simpa only [zero_smul, sub_zero, map_zero] using hv

/-- The generalized eigenspaces supply the spectral decomposition itself;
only the analytic representation for each nonzero multiplier is an input to
this intermediate assembly lemma. -/
theorem floquet_of_generalized_kernels (h : ℂ)
    (V : Submodule ℂ (ℂ → ℂ)) [FiniteDimensional ℂ V]
    (T : V ≃ₗ[ℂ] V)
    (hblock : ∀ (c : ℂ), c ≠ 0 → ∀ (k : ℕ) (v : V),
      ((T.toLinearMap - c • 1) ^ k) v = 0 →
        HasFloquetRepresentation h (v : ℂ → ℂ)) :
    ∀ v : V, HasFloquetRepresentation h (v : ℂ → ℂ) := by
  intro v
  have hv : v ∈ ⨆ c : ℂ, Module.End.maxGenEigenspace T.toLinearMap c := by
    rw [Module.End.iSup_maxGenEigenspace_eq_top]
    trivial
  refine Submodule.iSup_induction
    (motive := fun v : V => HasFloquetRepresentation h (v : ℂ → ℂ))
    (fun c : ℂ => Module.End.maxGenEigenspace T.toLinearMap c) hv ?_ ?_ ?_
  · intro c v hv
    obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace T.toLinearMap c v).mp hv
    by_cases hc : c = 0
    · subst c
      have hz := zero_multiplier_kernel T k hk
      subst v
      exact hasFloquetRepresentation_zero h
    · exact hblock c hc k v hk
  · exact hasFloquetRepresentation_zero h
  · intro v w hv hw
    exact hv.add hw

/-- Every function in a finite-dimensional space of entire functions on which
translation acts invertibly has an actual finite scalar Floquet sum. -/
theorem finiteDimensional_floquet {h : ℂ} (hh : h ≠ 0)
    (V : Submodule ℂ (ℂ → ℂ)) [FiniteDimensional ℂ V]
    (hV : ∀ v : V, Differentiable ℂ (v : ℂ → ℂ))
    (T : V ≃ₗ[ℂ] V)
    (hT : ∀ (v : V) z, (T v : ℂ → ℂ) z = (v : ℂ → ℂ) (z + h)) :
    ∀ v : V, HasFloquetRepresentation h (v : ℂ → ℂ) := by
  apply floquet_of_generalized_kernels h V T
  intro c hc k v hk
  have hkernel := difference_pow_eq_zero_of_generalizedEigenvector
    T (difference h) hT (fun _ _ => rfl) hh hc k v hk
  have he := exponentialRemoval_entire (Complex.log c / h) (hV v)
  obtain ⟨p, hp, hrep⟩ := finite_difference_representation hh he hkernel
  apply hasFloquetRepresentation_of_polynomial (a := Complex.log c / h) k p hp
  intro z
  calc
    (v : ℂ → ℂ) z = Complex.exp ((Complex.log c / h) * z) *
        exponentialRemoval V (Complex.log c / h) v z :=
      reconstruct_factor (v : ℂ → ℂ) (Complex.log c / h) z
    _ = _ := by rw [hrep]

/-- Ince's scalar Floquet representation for actual entire solutions of a
linear differential equation with entire periodic coefficients. Finiteness
of the solution space and its invertible translation action are proved from
the differential equation, rather than supplied as hypotheses. -/
theorem entire_solution_floquet {n : ℕ} {a : Fin (n + 1) → ℂ → ℂ}
    (ha : ∀ j, Differentiable ℂ (a j)) (hlead : a (Fin.last n) 0 ≠ 0)
    {h : ℂ} (hh : h ≠ 0) (hp : ∀ j, Function.Periodic (a j) h)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hsol : Solves a f) :
    HasFloquetRepresentation h f := by
  let := solutionSpace_finiteDimensional ha hlead
  exact finiteDimensional_floquet hh (solutionSpace a) (fun v => v.property.1)
    (translateEquiv a h hp) (translateEquiv_apply a h hp) ⟨f, hf, hsol⟩

end IncePeriodic

#print axioms IncePeriodic.hasFloquetRepresentation_zero
#print axioms IncePeriodic.HasFloquetRepresentation.add
#print axioms IncePeriodic.hasFloquetRepresentation_of_polynomial
#print axioms IncePeriodic.linearEquiv_pow_injective
#print axioms IncePeriodic.zero_multiplier_kernel
#print axioms IncePeriodic.floquet_of_generalized_kernels
#print axioms IncePeriodic.finiteDimensional_floquet
#print axioms IncePeriodic.entire_solution_floquet
