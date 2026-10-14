import IncePeriodic
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# Exponential conjugation of translation Jordan blocks

Removing an exponential factor turns the generalized eigenspace of translation
with multiplier `μ` into the kernel of an iterated finite difference. The proof
is an exact algebraic identity for every power, not a hypothesis about Floquet
solutions. The difference operator is first described by its pointwise action
so the identity can be reused by any concrete finite-difference interface.
-/

set_option autoImplicit false
noncomputable section

namespace IncePeriodic

/-- Multiplication by the inverse exponential on a subspace of functions. -/
def exponentialRemoval (V : Submodule ℂ (ℂ → ℂ)) (b : ℂ) :
    V →ₗ[ℂ] (ℂ → ℂ) where
  toFun f z := Complex.exp (-b*z) * (f : ℂ → ℂ) z
  map_add' f g := by funext z; exact mul_add _ _ _
  map_smul' c f := by funext z; simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

@[simp] theorem exponentialRemoval_apply (V : Submodule ℂ (ℂ → ℂ)) (b : ℂ)
    (f : V) (z : ℂ) :
    exponentialRemoval V b f z = Complex.exp (-b*z) * (f : ℂ → ℂ) z := rfl

theorem exponentialRemoval_entire {V : Submodule ℂ (ℂ → ℂ)} (b : ℂ) {f : V}
    (hf : Differentiable ℂ (f : ℂ → ℂ)) :
    Differentiable ℂ (exponentialRemoval V b f) :=
  (Complex.differentiable_exp.comp ((differentiable_const (-b)).mul differentiable_id)).mul hf

theorem logarithmicExponent_multiplier {h μ : ℂ} (hh : h ≠ 0) (hμ : μ ≠ 0) :
    Complex.exp ((Complex.log μ / h)*h) = μ := by
  rw [div_mul_cancel₀ _ hh, Complex.exp_log hμ]

/-- One exact conjugation step, for any endomorphism with the finite-difference action. -/
theorem difference_exponentialRemoval {V : Submodule ℂ (ℂ → ℂ)}
    (T : V ≃ₗ[ℂ] V) (D : Module.End ℂ (ℂ → ℂ)) {h b μ : ℂ}
    (hT : ∀ (f : V) z, (T f : ℂ → ℂ) z = (f : ℂ → ℂ) (z+h))
    (hD : ∀ (g : ℂ → ℂ) z, D g z = g (z+h)-g z)
    (hb : Complex.exp (b*h) = μ) (f : V) :
    D (exponentialRemoval V b f) =
      μ⁻¹ • exponentialRemoval V b ((T.toLinearMap-μ • 1) f) := by
  have hμ : μ ≠ 0 := hb ▸ Complex.exp_ne_zero _
  funext z
  rw [hD]
  simp only [exponentialRemoval_apply, Pi.smul_apply, smul_eq_mul,
    LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
    Submodule.coe_sub, Submodule.coe_smul, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, LinearEquiv.coe_coe, hT]
  rw [mul_add, Complex.exp_add]
  have he : Complex.exp (-b*h) = μ⁻¹ := by
    rw [neg_mul, Complex.exp_neg, hb]
  rw [he]
  field_simp

/-- Exact power conjugation for an arbitrary translation Jordan block. -/
theorem difference_pow_exponentialRemoval {V : Submodule ℂ (ℂ → ℂ)}
    (T : V ≃ₗ[ℂ] V) (D : Module.End ℂ (ℂ → ℂ)) {h b μ : ℂ}
    (hT : ∀ (f : V) z, (T f : ℂ → ℂ) z = (f : ℂ → ℂ) (z+h))
    (hD : ∀ (g : ℂ → ℂ) z, D g z = g (z+h)-g z)
    (hb : Complex.exp (b*h) = μ) (k : ℕ) (f : V) :
    (D^k) (exponentialRemoval V b f) =
      (μ⁻¹)^k • exponentialRemoval V b (((T.toLinearMap-μ • 1)^k) f) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_smul,
      difference_exponentialRemoval T D hT hD hb, smul_smul,
      pow_succ', pow_succ', Module.End.mul_apply]
    congr 1
    ring

/-- The vanishing generalized eigenvector equation implies vanishing finite differences. -/
theorem difference_pow_eq_zero_of_generalizedEigenvector
    {V : Submodule ℂ (ℂ → ℂ)} (T : V ≃ₗ[ℂ] V)
    (D : Module.End ℂ (ℂ → ℂ)) {h μ : ℂ}
    (hT : ∀ (f : V) z, (T f : ℂ → ℂ) z = (f : ℂ → ℂ) (z+h))
    (hD : ∀ (g : ℂ → ℂ) z, D g z = g (z+h)-g z)
    (hh : h ≠ 0) (hμ : μ ≠ 0) (k : ℕ) (f : V)
    (hk : ((T.toLinearMap-μ • 1)^k) f = 0) :
    (D^k) (fun z => Complex.exp (-(Complex.log μ/h)*z) * (f : ℂ → ℂ) z) = 0 := by
  change (D^k) (exponentialRemoval V (Complex.log μ/h) f) = 0
  rw [difference_pow_exponentialRemoval T D hT hD
    (logarithmicExponent_multiplier hh hμ), hk, map_zero, smul_zero]

#print axioms exponentialRemoval_entire
#print axioms logarithmicExponent_multiplier
#print axioms difference_exponentialRemoval
#print axioms difference_pow_exponentialRemoval
#print axioms difference_pow_eq_zero_of_generalizedEigenvector
end IncePeriodic
