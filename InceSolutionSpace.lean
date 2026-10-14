import IncePeriodic
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# The actual entire solution space of a scalar linear differential equation

Entire coefficients and a leading coefficient nonzero at the origin imply
uniqueness from the first `n` derivatives there. The proof differentiates the
equation, proves vanishing of all Taylor coefficients by strong induction,
and uses the convergent entire Taylor expansion. Consequently the entire
solution space has dimension at most `n`. No existence of a fundamental
system, uniqueness hypothesis, or finite-dimensionality hypothesis is used.
Periodic coefficients make translation by a period a linear automorphism.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace IncePeriodic

theorem entire_iteratedDeriv {f : ℂ → ℂ} (hf : Differentiable ℂ f) (k : ℕ) :
    Differentiable ℂ (iteratedDeriv k f) :=
  hf.contDiff.differentiable_iteratedDeriv' k

theorem iteratedDeriv_iteratedDeriv (k j : ℕ) (f : ℂ → ℂ) :
    iteratedDeriv k (iteratedDeriv j f) = iteratedDeriv (k+j) f := by
  simp only [iteratedDeriv_eq_iterate, Function.iterate_add_apply]

/-- The product-rule expansion of a differentiated scalar equation. -/
theorem differentiated_equation {n : ℕ} {a : Fin (n+1) → ℂ → ℂ} {f : ℂ → ℂ}
    (ha : ∀ j, Differentiable ℂ (a j)) (hf : Differentiable ℂ f)
    (hsol : Solves a f) (k : ℕ) (z : ℂ) :
    ∑ j : Fin (n+1), ∑ i ∈ Finset.range (k+1),
      (k.choose i : ℂ) * iteratedDeriv i (a j) z *
        iteratedDeriv (k-i+j.val) f z = 0 := by
  have heq : (fun w => ∑ j, a j w * iteratedDeriv j.val f w) = 0 := funext hsol
  have hd := congrArg (fun g : ℂ → ℂ => iteratedDeriv k g z) heq
  rw [iteratedDeriv_fun_sum] at hd
  · simpa only [iteratedDeriv_fun_mul (ha _).contDiff.contDiffAt
      (entire_iteratedDeriv hf _).contDiff.contDiffAt,
      iteratedDeriv_iteratedDeriv, iteratedDeriv_const_zero] using hd
  · intro j _
    exact ((ha j).mul (entire_iteratedDeriv hf j.val)).contDiff.contDiffAt

/-- Zero initial jet forces every derivative to vanish, including in order zero. -/
theorem all_derivatives_zero_of_zero_jet {n : ℕ} {a : Fin (n+1) → ℂ → ℂ}
    {f : ℂ → ℂ} (ha : ∀ j, Differentiable ℂ (a j))
    (hlead : a (Fin.last n) 0 ≠ 0) (hf : Differentiable ℂ f)
    (hsol : Solves a f) (hjet : ∀ j < n, iteratedDeriv j f 0 = 0) :
    ∀ m, iteratedDeriv m f 0 = 0 := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hmn : m < n
    · exact hjet m hmn
    have hnm : n ≤ m := Nat.le_of_not_gt hmn
    let k := m-n
    have hkn : k+n = m := Nat.sub_add_cancel hnm
    have hd := differentiated_equation ha hf hsol k 0
    have hout : (∑ j : Fin (n+1), ∑ i ∈ Finset.range (k+1),
        (k.choose i : ℂ) * iteratedDeriv i (a j) 0 *
          iteratedDeriv (k-i+j.val) f 0) = a (Fin.last n) 0 * iteratedDeriv m f 0 := by
      rw [Finset.sum_eq_single (Fin.last n)]
      · rw [Finset.sum_eq_single 0]
        · simp [hkn]
        · intro i hi hi0
          have hi' : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          have hlt : k-i+(Fin.last n).val < m := by simp only [Fin.val_last]; omega
          rw [ih _ hlt, mul_zero]
        · simp
      · intro j _ hj
        apply Finset.sum_eq_zero
        intro i hi
        have hj' : j.val < n := by
          have := j.isLt
          have hjn : j.val ≠ n := by
            intro he
            apply hj
            exact Fin.ext he
          omega
        have hlt : k-i+j.val < m := by omega
        rw [ih _ hlt, mul_zero]
      · simp
    rw [hout] at hd
    exact (mul_eq_zero.mp hd).resolve_left hlead

/-- Global uniqueness follows from the actual convergent Taylor expansion. -/
theorem eq_zero_of_zero_jet {n : ℕ} {a : Fin (n+1) → ℂ → ℂ} {f : ℂ → ℂ}
    (ha : ∀ j, Differentiable ℂ (a j)) (hlead : a (Fin.last n) 0 ≠ 0)
    (hf : Differentiable ℂ f) (hsol : Solves a f)
    (hjet : ∀ j < n, iteratedDeriv j f 0 = 0) : f = 0 := by
  have hall := all_derivatives_zero_of_zero_jet ha hlead hf hsol hjet
  funext z
  have ht := Complex.taylorSeries_eq_of_entire' 0 z hf
  simpa only [hall, mul_zero, zero_mul, tsum_zero, Pi.zero_apply] using ht.symm

/-- Entire solutions, as an actual subspace of functions. -/
def solutionSpace {n : ℕ} (a : Fin (n+1) → ℂ → ℂ) : Submodule ℂ (ℂ → ℂ) where
  carrier := {f | Differentiable ℂ f ∧ Solves a f}
  zero_mem' := ⟨differentiable_const 0, by intro z; simp⟩
  add_mem' := by
    intro f g hf hg
    refine ⟨hf.1.add hg.1, ?_⟩
    intro z
    simp only [iteratedDeriv_add hf.1.contDiff.contDiffAt hg.1.contDiff.contDiffAt,
      mul_add, Finset.sum_add_distrib, hf.2 z, hg.2 z, add_zero]
  smul_mem' := by
    intro c f hf
    refine ⟨hf.1.const_smul c, ?_⟩
    intro z
    simp only [iteratedDeriv_const_smul_field, smul_eq_mul]
    simp_rw [← mul_assoc, mul_comm (a _ z) c, mul_assoc, ← Finset.mul_sum, hf.2 z, mul_zero]

@[simp] theorem mem_solutionSpace {n : ℕ} {a : Fin (n+1) → ℂ → ℂ} {f : ℂ → ℂ} :
    f ∈ solutionSpace a ↔ Differentiable ℂ f ∧ Solves a f := Iff.rfl

/-- The first `n` derivatives at the origin, as a linear map on entire solutions. -/
def jetMap {n : ℕ} (a : Fin (n+1) → ℂ → ℂ) :
    solutionSpace a →ₗ[ℂ] (Fin n → ℂ) where
  toFun f j := iteratedDeriv j.val (f : ℂ → ℂ) 0
  map_add' f g := by
    funext j
    exact iteratedDeriv_add f.property.1.contDiff.contDiffAt g.property.1.contDiff.contDiffAt
  map_smul' c f := by
    funext j
    exact iteratedDeriv_const_smul_field c (f : ℂ → ℂ)

theorem jetMap_injective {n : ℕ} {a : Fin (n+1) → ℂ → ℂ}
    (ha : ∀ j, Differentiable ℂ (a j)) (hlead : a (Fin.last n) 0 ≠ 0) :
    Function.Injective (jetMap a) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro f hf
  apply Subtype.ext
  apply eq_zero_of_zero_jet ha hlead f.property.1 f.property.2
  intro j hj
  exact congrFun hf ⟨j, hj⟩

theorem solutionSpace_finiteDimensional {n : ℕ} {a : Fin (n+1) → ℂ → ℂ}
    (ha : ∀ j, Differentiable ℂ (a j)) (hlead : a (Fin.last n) 0 ≠ 0) :
    FiniteDimensional ℂ (solutionSpace a) :=
  FiniteDimensional.of_injective (jetMap a) (jetMap_injective ha hlead)

theorem finrank_solutionSpace_le {n : ℕ} {a : Fin (n+1) → ℂ → ℂ}
    (ha : ∀ j, Differentiable ℂ (a j)) (hlead : a (Fin.last n) 0 ≠ 0) :
    Module.finrank ℂ (solutionSpace a) ≤ n := by
  simpa using LinearMap.finrank_le_finrank_of_injective (jetMap_injective ha hlead)

/-- Translation by a coefficient period and its inverse on the entire solution space. -/
def translateEquiv {n : ℕ} (a : Fin (n+1) → ℂ → ℂ) (h : ℂ)
    (hp : ∀ j, Function.Periodic (a j) h) :
    solutionSpace a ≃ₗ[ℂ] solutionSpace a where
  toFun f := ⟨fun z => (f : ℂ → ℂ) (z+h),
    f.property.1.comp (differentiable_id.add_const h), solves_translate hp f.property.2⟩
  invFun f := ⟨fun z => (f : ℂ → ℂ) (z+(-h)),
    f.property.1.comp (differentiable_id.add_const (-h)),
    solves_translate (fun j => (hp j).neg) f.property.2⟩
  left_inv f := by apply Subtype.ext; funext z; simp
  right_inv f := by apply Subtype.ext; funext z; simp
  map_add' f g := rfl
  map_smul' c f := rfl

@[simp] theorem translateEquiv_apply {n : ℕ} (a : Fin (n+1) → ℂ → ℂ) (h : ℂ)
    (hp : ∀ j, Function.Periodic (a j) h) (f : solutionSpace a) (z : ℂ) :
    (translateEquiv a h hp f : ℂ → ℂ) z = (f : ℂ → ℂ) (z+h) := rfl

#print axioms differentiated_equation
#print axioms all_derivatives_zero_of_zero_jet
#print axioms eq_zero_of_zero_jet
#print axioms jetMap_injective
#print axioms solutionSpace_finiteDimensional
#print axioms finrank_solutionSpace_le
#print axioms translateEquiv_apply
end IncePeriodic
