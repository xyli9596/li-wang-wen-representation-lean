import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Polynomial primitives for finite differences

Every monomial has a polynomial primitive for a nonzero complex translation.
The explicit primitive uses Bernoulli polynomials, whose shift identity is
already proved in mathlib. Its degree is at most one more than the monomial's.
-/

set_option autoImplicit false
noncomputable section

namespace IncePeriodic
open Polynomial

def complexBernoulli (n : ℕ) : Polynomial ℂ :=
  (Polynomial.bernoulli n).map (algebraMap ℚ ℂ)

theorem complexBernoulli_shift (n : ℕ) (z : ℂ) :
    (complexBernoulli n).eval (1+z) =
      (complexBernoulli n).eval z + (n : ℂ)*z^(n-1) := by
  have hm : (complexBernoulli n).comp (1+X) =
      complexBernoulli n + C (n : ℂ)*X^(n-1) := by
    simpa [complexBernoulli, Polynomial.map_comp] using
      congrArg (Polynomial.map (algebraMap ℚ ℂ))
        (Polynomial.bernoulli_comp_one_add_X n)
  have he := congrArg (Polynomial.eval z) hm
  simpa only [eval_comp, eval_add, eval_one, eval_X, eval_mul, eval_C, eval_pow] using he

theorem complexBernoulli_natDegree_le (n : ℕ) :
    (complexBernoulli n).natDegree ≤ n := by
  apply (Polynomial.natDegree_map_le).trans
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  rw [Polynomial.coeff_bernoulli, if_neg (Nat.not_le.mpr hi)]

/-- An explicit polynomial whose difference across `h` is `z^k`. -/
def differencePrimitive (h : ℂ) (k : ℕ) : Polynomial ℂ :=
  C (h^k / ((k : ℂ)+1)) *
    (complexBernoulli (k+1)).comp (C h⁻¹ * X)

theorem differencePrimitive_difference {h : ℂ} (hh : h ≠ 0) (k : ℕ) (z : ℂ) :
    (differencePrimitive h k).eval (z+h) - (differencePrimitive h k).eval z = z^k := by
  have hk : (k : ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have hz : h⁻¹*(z+h) = 1+h⁻¹*z := by field_simp; ring
  simp only [differencePrimitive, eval_mul, eval_C, eval_comp, eval_X]
  rw [hz, complexBernoulli_shift]
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  calc
    _ = (h^k*(h⁻¹*z)^k)*(((k : ℂ)+1)/((k : ℂ)+1)) := by ring
    _ = z^k := by
      rw [div_self hk, mul_one, ← mul_pow]
      simp [hh]

theorem differencePrimitive_natDegree_le (h : ℂ) (k : ℕ) :
    (differencePrimitive h k).natDegree ≤ k+1 := by
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  apply Polynomial.natDegree_comp_le.trans
  have hlin : (C h⁻¹ * X : Polynomial ℂ).natDegree ≤ 1 :=
    (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
  calc
    (complexBernoulli (k+1)).natDegree * (C h⁻¹ * X : Polynomial ℂ).natDegree
        ≤ (k+1)*1 := Nat.mul_le_mul (complexBernoulli_natDegree_le _) hlin
    _ = k+1 := Nat.mul_one _

theorem exists_polynomial_difference_primitive {h : ℂ} (hh : h ≠ 0) (k : ℕ) :
    ∃ Q : Polynomial ℂ, Q.natDegree ≤ k+1 ∧
      ∀ z, Q.eval (z+h)-Q.eval z = z^k :=
  ⟨differencePrimitive h k, differencePrimitive_natDegree_le h k,
    differencePrimitive_difference hh k⟩

#print axioms complexBernoulli_shift
#print axioms complexBernoulli_natDegree_le
#print axioms differencePrimitive_difference
#print axioms differencePrimitive_natDegree_le
#print axioms exists_polynomial_difference_primitive
end IncePeriodic
