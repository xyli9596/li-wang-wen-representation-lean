import LiWangWenFiniteOrderFloquet
import LiWangWenFourierRecurrence
import Mathlib.Algebra.Polynomial.Roots

/-!
# Actual differential equations for coefficients of a Floquet block

Polynomial-valued periodicity gives coefficient uniqueness without a growth
assumption. Leibniz's rule is then applied to the actual differential equation,
retaining every lower-degree term of every generalized Floquet block.
-/

noncomputable section
open Polynomial
open scoped BigOperators

namespace LiWangWen

/-- A periodic polynomial-valued function whose diagonal evaluation vanishes
is identically zero: every fixed polynomial has infinitely many distinct roots. -/
theorem periodic_polynomial_eq_zero {h : ℂ} (hh : h ≠ 0)
    (Q : ℂ → Polynomial ℂ) (hQ : Function.Periodic Q h)
    (hz : ∀ z, (Q z).eval z = 0) : ∀ z, Q z = 0 := by
  intro z
  apply Polynomial.eq_zero_of_infinite_isRoot
  have hinj : Function.Injective (fun n : ℕ => z+(n:ℂ)*h) := by
    intro n m hnm
    have hc : (n : ℂ) = m := mul_right_cancel₀ hh (add_left_cancel hnm)
    exact_mod_cast hc
  have hinf := Set.infinite_range_of_injective hinj
  apply hinf.mono
  rintro x ⟨n, rfl⟩
  have hp := hQ.nat_mul n z
  change (Q z).eval (z+(n:ℂ)*h) = 0
  rw [← hp]
  exact hz (z+(n:ℂ)*h)

/-- The polynomial contributed by differentiating one monomial coefficient. -/
def floquetDerivativePolynomial (a : ℂ) (p : ℂ → ℂ) (m d : ℕ) (z : ℂ) : Polynomial ℂ :=
  ∑ i ∈ Finset.range (d+1),
    C ((d.choose i : ℂ)*((shiftedDeriv a)^[d-i] p) z) *
      Polynomial.derivative^[i] ((X : Polynomial ℂ)^m)

theorem floquetDerivativePolynomial_periodic (a : ℂ) {p : ℂ → ℂ} {h : ℂ}
    (hp : Function.Periodic p h) (m d : ℕ) :
    Function.Periodic (floquetDerivativePolynomial a p m d) h := by
  intro z
  unfold floquetDerivativePolynomial
  apply Finset.sum_congr rfl
  intro i hi
  rw [iterate_shiftedDeriv_periodic a hp (d-i) z]

/-- Evaluation of the formal polynomial agrees with the actual Leibniz rule. -/
theorem floquetDerivativePolynomial_eval (a : ℂ) {p : ℂ → ℂ}
    (hp : Differentiable ℂ p) (m d : ℕ) (z : ℂ) :
    iteratedDeriv d (fun w => w^m*(Complex.exp (a*w)*p w)) z =
      Complex.exp (a*z)*(floquetDerivativePolynomial a p m d z).eval z := by
  have he : Differentiable ℂ (fun w => Complex.exp (a*w)*p w) :=
    (Complex.differentiable_exp.comp ((differentiable_const a).mul differentiable_id)).mul hp
  have hm : Differentiable ℂ (fun w : ℂ => w^m) := by fun_prop
  rw [iteratedDeriv_fun_mul hm.contDiff.contDiffAt he.contDiff.contDiffAt]
  simp only [floquetDerivativePolynomial, eval_finsetSum, eval_mul, eval_C, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [iteratedDeriv_exp_mul a hp, iteratedDeriv_pow,
    Polynomial.iterate_derivative_X_pow_eq_C_mul, eval_mul, eval_C, eval_pow, eval_X]
  ring_nf

/-- The complete polynomial in the free monomial variable after applying the
actual ODE to a Floquet block and removing its common exponential. -/
def floquetEquationPolynomial {n : ℕ} (P : Fin (n+1) → Polynomial ℂ)
    (a : ℂ) (k : ℕ) (p : ℕ → ℂ → ℂ) (z : ℂ) : Polynomial ℂ :=
  ∑ d : Fin (n+1), C ((P d).eval (Complex.exp z)) *
    ∑ m ∈ Finset.range k, floquetDerivativePolynomial a (p m) m d.val z

theorem floquetEquationPolynomial_periodic {n : ℕ}
    (P : Fin (n+1) → Polynomial ℂ) (a : ℂ) (k : ℕ) (p : ℕ → ℂ → ℂ)
    (hp : ∀ m < k, Function.Periodic (p m) exponentialPeriod) :
    Function.Periodic (floquetEquationPolynomial P a k p) exponentialPeriod := by
  intro z
  unfold floquetEquationPolynomial
  apply Finset.sum_congr rfl
  intro d hd
  simp only [exponentialPeriod, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  exact floquetDerivativePolynomial_periodic a (hp m (Finset.mem_range.mp hm)) m d.val z

/-- All polynomial coefficients vanish for an actual solution block. -/
theorem floquetEquationPolynomial_eq_zero {n : ℕ}
    {P : Fin (n+1) → Polynomial ℂ} (a : ℂ) (k : ℕ) (p : ℕ → ℂ → ℂ)
    (hp : ∀ m < k, Differentiable ℂ (p m) ∧ Function.Periodic (p m) exponentialPeriod)
    (hsol : Solves P (fun z => Complex.exp (a*z)*∑ m ∈ Finset.range k, z^m*p m z)) :
    ∀ z, floquetEquationPolynomial P a k p z = 0 := by
  apply periodic_polynomial_eq_zero exponentialPeriod_ne_zero _
    (floquetEquationPolynomial_periodic P a k p (fun m hm => (hp m hm).2))
  intro z
  have hrep : (fun z => Complex.exp (a*z)*∑ m ∈ Finset.range k, z^m*p m z) =
      (fun z => ∑ m ∈ Finset.range k, z^m*(Complex.exp (a*z)*p m z)) := by
    funext w
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    ring_nf
  have hd (d : ℕ) :
      iteratedDeriv d (fun z => Complex.exp (a*z)*∑ m ∈ Finset.range k, z^m*p m z) z =
      Complex.exp (a*z)*(∑ m ∈ Finset.range k, floquetDerivativePolynomial a (p m) m d z).eval z := by
    rw [hrep, iteratedDeriv_fun_sum]
    · simp only [eval_finsetSum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      exact floquetDerivativePolynomial_eval a (hp m (Finset.mem_range.mp hm)).1 m d z
    · intro m hm
      exact ((differentiable_id.pow m).mul
        ((Complex.differentiable_exp.comp ((differentiable_const a).mul differentiable_id)).mul
          (hp m (Finset.mem_range.mp hm)).1)).contDiff.contDiffAt
  have hz := hsol z
  simp_rw [hd] at hz
  have heq : (∑ d : Fin (n+1), (P d).eval (Complex.exp z)*
      (Complex.exp (a*z)*(∑ m ∈ Finset.range k, floquetDerivativePolynomial a (p m) m d.val z).eval z)) =
      Complex.exp (a*z)*(floquetEquationPolynomial P a k p z).eval z := by
    simp only [floquetEquationPolynomial, eval_finsetSum, eval_mul, eval_C, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    ring_nf
  rw [heq] at hz
  exact (mul_eq_zero.mp hz).resolve_left (Complex.exp_ne_zero _)

/-- One coefficient of the Leibniz polynomial, expressed as a finite linear
combination of shifted derivatives of one periodic coefficient. -/
def floquetMonomialContribution (a : ℂ) (p : ℂ → ℂ) (m d j : ℕ) (z : ℂ) : ℂ :=
  ∑ i ∈ Finset.range (d+1), (d.choose i : ℂ) *
    (Polynomial.derivative^[i] ((X : Polynomial ℂ)^m)).coeff j *
    ((shiftedDeriv a)^[d-i] p) z

theorem floquetDerivativePolynomial_coeff (a : ℂ) (p : ℂ → ℂ)
    (m d j : ℕ) (z : ℂ) :
    (floquetDerivativePolynomial a p m d z).coeff j = floquetMonomialContribution a p m d j z := by
  simp only [floquetDerivativePolynomial, floquetMonomialContribution, finsetSum_coeff, coeff_C_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring_nf

theorem floquetMonomialContribution_eq_zero_of_lt (a : ℂ) (p : ℂ → ℂ)
    {m j : ℕ} (hmj : m < j) (d : ℕ) (z : ℂ) :
    floquetMonomialContribution a p m d j z = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  have hne : m ≠ j+i := by omega
  simp [Polynomial.coeff_iterate_derivative, hne.symm]

theorem floquetMonomialContribution_diagonal (a : ℂ) (p : ℂ → ℂ)
    (j d : ℕ) (z : ℂ) :
    floquetMonomialContribution a p j d j z = ((shiftedDeriv a)^[d] p) z := by
  unfold floquetMonomialContribution
  rw [Finset.sum_eq_single 0]
  · simp
  · intro i hi hi0
    simp [Polynomial.coeff_iterate_derivative, hi0]
  · simp

/-- The exact coefficient equations include every generalized-block correction. -/
theorem floquet_block_coefficient_equation {n : ℕ}
    {P : Fin (n+1) → Polynomial ℂ} (a : ℂ) (k : ℕ) (p : ℕ → ℂ → ℂ)
    (hp : ∀ m < k, Differentiable ℂ (p m) ∧ Function.Periodic (p m) exponentialPeriod)
    (hsol : Solves P (fun z => Complex.exp (a*z)*∑ m ∈ Finset.range k, z^m*p m z))
    (j : ℕ) (z : ℂ) :
    ∑ d : Fin (n+1), (P d).eval (Complex.exp z)*
      ∑ m ∈ Finset.range k, floquetMonomialContribution a (p m) m d.val j z = 0 := by
  have h := congrArg (fun Q : Polynomial ℂ => Q.coeff j)
    (floquetEquationPolynomial_eq_zero a k p hp hsol z)
  simpa only [floquetEquationPolynomial, finsetSum_coeff, coeff_C_mul,
    floquetDerivativePolynomial_coeff, coeff_zero] using h

/-- Isolating the diagonal leaves only coefficients with strictly larger
monomial degree, which is the required triangular descending induction. -/
theorem floquet_block_triangular_equation {n : ℕ}
    {P : Fin (n+1) → Polynomial ℂ} (a : ℂ) (k : ℕ) (p : ℕ → ℂ → ℂ)
    (hp : ∀ m < k, Differentiable ℂ (p m) ∧ Function.Periodic (p m) exponentialPeriod)
    (hsol : Solves P (fun z => Complex.exp (a*z)*∑ m ∈ Finset.range k, z^m*p m z))
    {j : ℕ} (hj : j < k) (z : ℂ) :
    (∑ d : Fin (n+1), (P d).eval (Complex.exp z)*((shiftedDeriv a)^[d.val] (p j)) z) +
      ∑ d : Fin (n+1), (P d).eval (Complex.exp z)*
        ∑ m ∈ (Finset.range k).filter (j < ·), floquetMonomialContribution a (p m) m d.val j z = 0 := by
  have h := floquet_block_coefficient_equation a k p hp hsol j z
  have hsplit (d : Fin (n+1)) :
      (∑ m ∈ Finset.range k, floquetMonomialContribution a (p m) m d.val j z) =
      ((shiftedDeriv a)^[d.val] (p j)) z +
      ∑ m ∈ (Finset.range k).filter (j < ·), floquetMonomialContribution a (p m) m d.val j z := by
    rw [← floquetMonomialContribution_diagonal a (p j) j d.val z]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_range.mpr hj)]
    rw [add_comm]
    congr 1
    rw [Finset.sum_filter]
    calc
      _ = ∑ m ∈ (Finset.range k).erase j,
          if j < m then floquetMonomialContribution a (p m) m d.val j z else 0 := by
        apply Finset.sum_congr rfl
        intro m hm
        have hmj : m ≠ j := (Finset.mem_erase.mp hm).1
        by_cases hlt : j < m
        · simp only [hlt, if_true]
        · have hlow : m < j := lt_of_le_of_ne (le_of_not_gt hlt) hmj
          simp only [hlt, if_false, floquetMonomialContribution_eq_zero_of_lt a (p m) hlow]
      _ = _ := by
        apply Finset.sum_subset (Finset.erase_subset j (Finset.range k))
        intro m hm hmnot
        have hmeq : m = j := by simpa [hm] using hmnot
        subst m
        simp
  simp_rw [hsplit, mul_add] at h
  rwa [Finset.sum_add_distrib] at h

#print axioms periodic_polynomial_eq_zero
#print axioms floquetDerivativePolynomial_periodic
#print axioms floquetDerivativePolynomial_eval
#print axioms floquetEquationPolynomial_periodic
#print axioms floquetEquationPolynomial_eq_zero
#print axioms floquetDerivativePolynomial_coeff
#print axioms floquetMonomialContribution_eq_zero_of_lt
#print axioms floquetMonomialContribution_diagonal
#print axioms floquet_block_coefficient_equation
#print axioms floquet_block_triangular_equation

end LiWangWen
