import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-! Elementary steps of Ince, Ordinary Differential Equations, §15.7,
pp. 381--382: translation invariance and scalar Floquet factors.
The existence of a full fundamental system and arbitrary Jordan blocks is
not claimed in this module. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace IncePeriodic

def Solves {n : ℕ} (a : Fin (n+1) → ℂ → ℂ) (f : ℂ → ℂ) : Prop :=
  ∀ z, ∑ j, a j z * iteratedDeriv j.val f z = 0

/-- Periodic coefficients imply that translation by a period preserves solutions. -/
theorem solves_translate {n : ℕ} {a : Fin (n+1) → ℂ → ℂ} {f : ℂ → ℂ}
    {h : ℂ} (ha : ∀ j, Function.Periodic (a j) h) (hf : Solves a f) :
    Solves a (fun z => f (z+h)) := by
  intro z
  have hz := hf (z+h)
  simpa only [iteratedDeriv_comp_add_const, fun j => ha j z] using hz

/-- Removing the exponential factor of a translation eigenfunction leaves a periodic function. -/
theorem periodic_factor {f : ℂ → ℂ} {a h : ℂ}
    (hf : ∀ z, f (z+h) = Complex.exp (a*h) * f z) :
    Function.Periodic (fun z => Complex.exp (-a*z) * f z) h := by
  intro z
  dsimp only
  rw [hf, mul_add, Complex.exp_add]
  have he : Complex.exp (-a*h) * Complex.exp (a*h) = 1 := by
    rw [← Complex.exp_add]
    simp
  calc
    (Complex.exp (-a*z) * Complex.exp (-a*h)) * (Complex.exp (a*h) * f z) =
      (Complex.exp (-a*z) * f z) * (Complex.exp (-a*h) * Complex.exp (a*h)) := by ring
    _ = Complex.exp (-a*z) * f z := by rw [he, mul_one]

theorem reconstruct_factor (f : ℂ → ℂ) (a z : ℂ) :
    f z = Complex.exp (a*z) * (Complex.exp (-a*z) * f z) := by
  rw [← mul_assoc, ← Complex.exp_add]
  simp

/-- The simple multiplier case in §15.7. The translation eigenfunction is an
explicit hypothesis; this does not assume or prove that every solution is one. -/
theorem eigenfunction_factorization {f : ℂ → ℂ} {h c : ℂ}
    (hh : h ≠ 0) (hc : c ≠ 0) (he : Differentiable ℂ f)
    (hf : ∀ z, f (z+h) = c*f z) :
    ∃ a : ℂ, ∃ p : ℂ → ℂ, Complex.exp (a*h) = c ∧
      Differentiable ℂ p ∧ Function.Periodic p h ∧
      ∀ z, f z = Complex.exp (a*z) * p z := by
  let a := Complex.log c / h
  have ha : Complex.exp (a*h) = c := by
    dsimp [a]
    rw [div_mul_cancel₀ _ hh, Complex.exp_log hc]
  refine ⟨a, (fun z => Complex.exp (-a*z) * f z), ha, ?_, ?_, reconstruct_factor f a⟩
  · exact (Complex.differentiable_exp.comp ((differentiable_const (-a)).mul differentiable_id)).mul he
  · apply periodic_factor
    simpa only [ha] using hf

/-- The first nontrivial Jordan step: a periodic difference is removed by a
linear polynomial in z. This is the algebraic calculation on p. 382. -/
theorem periodic_of_jordan_step {q p : ℂ → ℂ} {h : ℂ} (hh : h ≠ 0)
    (hp : Function.Periodic p h) (hq : ∀ z, q (z+h) = q z + p z) :
    Function.Periodic (fun z => q z - (z/h)*p z) h := by
  intro z
  dsimp only
  rw [hq, hp]
  field_simp [hh]
  ring

/-- Entirety is preserved by the polynomial subtraction in the Jordan step. -/
theorem entire_jordan_remainder {q p : ℂ → ℂ} (h : ℂ)
    (hq : Differentiable ℂ q) (hp : Differentiable ℂ p) :
    Differentiable ℂ (fun z => q z - (z/h)*p z) :=
  hq.sub ((differentiable_id.div_const h).mul hp)

#print axioms solves_translate
#print axioms periodic_factor
#print axioms reconstruct_factor
#print axioms eigenfunction_factorization
#print axioms periodic_of_jordan_step
#print axioms entire_jordan_remainder
end IncePeriodic
