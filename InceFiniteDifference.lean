import InceDifferencePolynomial
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Entire functions annihilated by a finite difference

If the `k`th finite difference of an entire function vanishes, that function
is a polynomial of degree less than `k` with entire periodic coefficients.
The proof constructs an antidifference of each monomial using Bernoulli
polynomials and applies induction to the actual difference equation.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace IncePeriodic

/-- Translation by `h` minus the identity, on the space of functions. -/
def difference (h : ℂ) : Module.End ℂ (ℂ → ℂ) where
  toFun g z := g (z+h)-g z
  map_add' f g := by funext z; simp only [Pi.add_apply]; ring
  map_smul' c f := by
    funext z
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp] theorem difference_apply (h : ℂ) (g : ℂ → ℂ) (z : ℂ) :
    difference h g z = g (z+h)-g z := rfl

theorem difference_entire {h : ℂ} {g : ℂ → ℂ} (hg : Differentiable ℂ g) :
    Differentiable ℂ (difference h g) :=
  (hg.comp (differentiable_id.add_const h)).sub hg

/-- Solving the vanishing finite-difference equation, without any assumption
of a polynomial or periodic representation. -/
theorem finite_difference_representation {h : ℂ} {g : ℂ → ℂ} {k : ℕ}
    (hh : h ≠ 0) (hg : Differentiable ℂ g)
    (hkernel : (difference h ^ k) g = 0) :
    ∃ p : ℕ → ℂ → ℂ,
      (∀ j < k, Differentiable ℂ (p j) ∧ Function.Periodic (p j) h) ∧
      ∀ z, g z = ∑ j ∈ Finset.range k, z ^ j * p j z := by
  induction k generalizing g with
  | zero =>
    have hz : g = 0 := by simpa using hkernel
    refine ⟨fun _ _ => 0, by simp, ?_⟩
    intro z
    simp [hz]
  | succ k ih =>
    have hd : (difference h ^ k) (difference h g) = 0 := by
      simpa only [pow_succ, Module.End.mul_apply] using hkernel
    obtain ⟨p, hp, hrep⟩ := ih (difference_entire hg) hd
    let Q : ℕ → Polynomial ℂ := differencePrimitive h
    let F : ℂ → ℂ := fun z => ∑ i ∈ Finset.range k, (Q i).eval z * p i z
    have hF : Differentiable ℂ F := by
      apply Differentiable.fun_sum
      intro i hi
      exact (Q i).differentiable.mul (hp i (Finset.mem_range.mp hi)).1
    have hFD (z : ℂ) : F (z+h)-F z = difference h g z := by
      rw [hrep]
      dsimp [F]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [(hp i (Finset.mem_range.mp hi)).2 z, ← sub_mul]
      rw [show (Q i).eval (z+h)-(Q i).eval z = z^i from
        differencePrimitive_difference hh i z]
    let r : ℂ → ℂ := g-F
    have hr : Differentiable ℂ r := hg.sub hF
    have hrp : Function.Periodic r h := by
      intro z
      have hz := hFD z
      simp only [difference_apply] at hz
      dsimp [r]
      linear_combination -hz
    let q : ℕ → ℂ → ℂ := fun j z =>
      ∑ i ∈ Finset.range k, (Q i).coeff j * p i z
    have hq (j : ℕ) : Differentiable ℂ (q j) := by
      apply Differentiable.fun_sum
      intro i hi
      exact (differentiable_const _).mul (hp i (Finset.mem_range.mp hi)).1
    have hqp (j : ℕ) : Function.Periodic (q j) h := by
      intro z
      apply Finset.sum_congr rfl
      intro i hi
      rw [(hp i (Finset.mem_range.mp hi)).2 z]
    have hqrep (z : ℂ) : ∑ j ∈ Finset.range (k+1), z^j*q j z = F z := by
      dsimp [q, F]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Polynomial.eval_eq_sum_range' (n := k+1) (p := Q i)
        (by have := differencePrimitive_natDegree_le h i
            have := Finset.mem_range.mp hi
            dsimp [Q]
            omega)]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    let s : ℕ → ℂ → ℂ := fun j z => q j z + if j = 0 then r z else 0
    refine ⟨s, ?_, ?_⟩
    · intro j hj
      constructor
      · by_cases hj0 : j = 0
        · subst j
          dsimp [s]
          exact (hq 0).add hr
        · simpa [s, hj0] using hq j
      · intro z
        dsimp [s]
        rw [hqp j z]
        by_cases hj0 : j = 0
        · simp only [hj0, hrp z]
        · simp only [hj0, if_false]
    · intro z
      dsimp [s]
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, hqrep]
      have hs : (∑ j ∈ Finset.range (k+1), z^j*(if j = 0 then r z else 0)) = r z := by
        simp
      rw [hs]
      dsimp [r]
      ring

#print axioms difference_entire
#print axioms finite_difference_representation
end IncePeriodic
