import LiWangWenDifferenceGrowth
import LiWangWenPolynomiality
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Polynomial.Taylor

/-!
# Cancellation-safe extraction of periodic coefficients

An exponential bound on a polynomial in `z` with periodic coefficients
bounds each coefficient separately. Fixed-node Lagrange interpolation
recovers each coefficient from finitely many translates of the whole sum.
Consequently entire coefficients composed with `exp` must be polynomials.
-/

set_option autoImplicit false
noncomputable section
open Polynomial
open scoped BigOperators

namespace LiWangWen

/-- Periodic coefficients of a finite monomial expansion inherit the actual
exponential bound of the whole sum, allowing cancellation between terms. -/
theorem periodic_monomial_coefficients_exp_bound {k : ℕ} {h : ℂ}
    (hh : h ≠ 0) (p : Fin k → ℂ → ℂ)
    (hp : ∀ j, Function.Periodic (p j) h)
    (hg : ExponentialBound (fun z => ∑ j : Fin k, z^j.val * p j z)) :
    ∀ j, ExponentialBound (p j) := by
  classical
  let g : ℂ → ℂ := fun z => ∑ j : Fin k, z^j.val * p j z
  let P : ℂ → Polynomial ℂ := fun z => ∑ j : Fin k, C (p j z) * X^j.val
  let v : Fin k → ℂ := fun i => (i.val : ℂ)*h
  let L : Fin k → Polynomial ℂ := Lagrange.basis Finset.univ v
  have hv : Set.InjOn v (Finset.univ : Finset (Fin k)) := by
    intro i hi j hj hij
    apply Fin.ext
    have hc : (i.val : ℂ) = (j.val : ℂ) := mul_right_cancel₀ hh hij
    exact_mod_cast hc
  have hinterp (z : ℂ) :
      taylor z (P z) = Lagrange.interpolate Finset.univ v (fun i => g (z+v i)) := by
    apply Lagrange.eq_interpolate_of_eval_eq _ hv
    · simp only [degree_taylor, Finset.card_univ, Fintype.card_fin]
      exact degree_sum_fin_lt (fun j => p j z)
    · intro i hi
      rw [taylor_eval]
      dsimp [P, g]
      simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
      apply Finset.sum_congr rfl
      intro j hj
      rw [show p j (z+v i) = p j z from (hp j).nat_mul i.val z]
      ring
  have hcoeff (z : ℂ) (j : Fin k) : (P z).coeff j.val = p j z := by
    simp [P, Fin.val_inj]
  have hrecover (z : ℂ) (j : Fin k) :
      p j z = ∑ i : Fin k, g (z+v i) * (hasseDeriv j.val (L i)).eval (-z) := by
    have he := congrArg (fun Q : Polynomial ℂ => (taylor (-z) Q).coeff j.val) (hinterp z)
    simpa only [taylor_taylor, neg_add_cancel, taylor_zero, hcoeff,
      Lagrange.interpolate_apply, map_sum, taylor_mul, taylor_C,
      finsetSum_coeff, coeff_C_mul, taylor_coeff, L] using he
  intro j
  have hb : ExponentialBound (fun z =>
      ∑ i : Fin k, g (z+v i) * (hasseDeriv j.val (L i)).eval (-z)) := by
    apply bound_sum
    intro i hi
    exact (hg.translate (v i)).mul (bound_poly_comp _ bound_id.neg)
  have he : p j = (fun z =>
      ∑ i : Fin k, g (z+v i) * (hasseDeriv j.val (L i)).eval (-z)) :=
    funext (fun z => hrecover z j)
  rw [he]
  exact hb

/-- The same extraction theorem in the natural-number range notation used
by the finite-difference representation theorem. -/
theorem periodic_monomial_coefficients_exp_bound_range {k : ℕ} {h : ℂ}
    (hh : h ≠ 0) (p : ℕ → ℂ → ℂ)
    (hp : ∀ j < k, Function.Periodic (p j) h)
    (hg : ExponentialBound (fun z => ∑ j ∈ Finset.range k, z^j * p j z)) :
    ∀ j < k, ExponentialBound (p j) := by
  have hf : ExponentialBound (fun z => ∑ j : Fin k, z^j.val * p j.val z) := by
    have he : (fun z => ∑ j : Fin k, z^j.val * p j.val z) =
        (fun z => ∑ j ∈ Finset.range k, z^j * p j z) := by
      funext z
      exact Fin.sum_univ_eq_sum_range (fun j => z^j * p j z) k
    rw [he]
    exact hg
  have hb := periodic_monomial_coefficients_exp_bound hh
    (fun j : Fin k => p j.val) (fun j => hp j.val j.isLt) hf
  exact fun j hj => hb ⟨j, hj⟩

/-- The coefficient conclusion of Lemma 5.2 for a general finite monomial
sum. Growth is assumed only for the entire sum, not for individual terms. -/
theorem polynomial_coefficients_of_exp_bound {k : ℕ} (u : Fin k → ℂ → ℂ)
    (hu : ∀ j, Differentiable ℂ (u j))
    (hg : ExponentialBound (fun z => ∑ j : Fin k, z^j.val * u j (Complex.exp z))) :
    ∀ j, ∃ Q : Polynomial ℂ, ∀ w, u j w = Q.eval w := by
  have hp (j : Fin k) : Function.Periodic (fun z => u j (Complex.exp z)) exponentialPeriod := by
    intro z
    simp only [exponentialPeriod, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  have hb := periodic_monomial_coefficients_exp_bound exponentialPeriod_ne_zero
    (fun j z => u j (Complex.exp z)) hp hg
  exact fun j => polynomial_of_exp_bound (hu j) (hb j)

/-- Entire exp-coefficients remain polynomial when the whole sum also has
one common exponential factor. Cancellation is handled before extraction. -/
theorem polynomial_coefficients_of_exponential_sum_bound {k : ℕ} (a : ℂ)
    (u : Fin k → ℂ → ℂ) (hu : ∀ j, Differentiable ℂ (u j))
    (hg : ExponentialBound (fun z => Complex.exp (a*z) *
      ∑ j : Fin k, z^j.val * u j (Complex.exp z))) :
    ∀ j, ∃ Q : Polynomial ℂ, ∀ w, u j w = Q.eval w := by
  apply polynomial_coefficients_of_exp_bound u hu
  simpa only [← mul_assoc, ← Complex.exp_add, neg_mul, neg_add_cancel,
    Complex.exp_zero, one_mul] using hg.remove_exponential a

/-- Natural-number range version of the cancellation-safe polynomiality
criterion, matching `finite_difference_representation` directly. -/
theorem polynomial_coefficients_of_exp_bound_range {k : ℕ} (u : ℕ → ℂ → ℂ)
    (hu : ∀ j < k, Differentiable ℂ (u j))
    (hg : ExponentialBound (fun z => ∑ j ∈ Finset.range k, z^j * u j (Complex.exp z))) :
    ∀ j < k, ∃ Q : Polynomial ℂ, ∀ w, u j w = Q.eval w := by
  have hf : ExponentialBound (fun z => ∑ j : Fin k, z^j.val * u j.val (Complex.exp z)) := by
    have he : (fun z => ∑ j : Fin k, z^j.val * u j.val (Complex.exp z)) =
        (fun z => ∑ j ∈ Finset.range k, z^j * u j (Complex.exp z)) := by
      funext z
      exact Fin.sum_univ_eq_sum_range (fun j => z^j * u j (Complex.exp z)) k
    rw [he]
    exact hg
  have hb := polynomial_coefficients_of_exp_bound
    (fun j : Fin k => u j.val) (fun j => hu j.val j.isLt) hf
  exact fun j hj => hb ⟨j, hj⟩

#print axioms periodic_monomial_coefficients_exp_bound
#print axioms periodic_monomial_coefficients_exp_bound_range
#print axioms polynomial_coefficients_of_exp_bound
#print axioms polynomial_coefficients_of_exponential_sum_bound
#print axioms polynomial_coefficients_of_exp_bound_range
end LiWangWen
