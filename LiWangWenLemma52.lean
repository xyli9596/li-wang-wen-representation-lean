import LiWangWenCoefficientExtraction

/-!
# Lemma 5.2 for polynomial factors of distinct degrees

The exponential bound is imposed on the whole sum. Passing to monomial
coefficients and solving the resulting triangular system extracts every
periodic coefficient, even when cancellation occurs in the original sum.
The factors are nonzero, as required for their degrees to be natural numbers.
-/

set_option autoImplicit false
noncomputable section
open Polynomial
open scoped BigOperators

namespace LiWangWen

/-- Polynomial factors of strictly increasing degrees admit the same
cancellation-safe periodic coefficient extraction as monomials. -/
theorem periodic_polynomial_coefficients_exp_bound {k : ℕ} {h : ℂ}
    (hh : h ≠ 0) (F : Fin k → Polynomial ℂ)
    (hF : ∀ j, F j ≠ 0) (hdeg : StrictMono (fun j => (F j).natDegree))
    (p : Fin k → ℂ → ℂ) (hp : ∀ j, Function.Periodic (p j) h)
    (hg : ExponentialBound (fun z => ∑ j : Fin k, (F j).eval z * p j z)) :
    ∀ j, ExponentialBound (p j) := by
  classical
  let D := (Finset.univ.sup fun j : Fin k => (F j).natDegree) + 1
  have hD (j : Fin k) : (F j).natDegree < D := by
    exact Nat.lt_succ_of_le (Finset.le_sup (f := fun j : Fin k => (F j).natDegree)
      (Finset.mem_univ j))
  let q (d : ℕ) (z : ℂ) := ∑ j : Fin k, (F j).coeff d * p j z
  have hqper (d : ℕ) : Function.Periodic (q d) h := by
    intro z
    simp only [q]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hp j z]
  have hexpand : (fun z => ∑ d ∈ Finset.range D, z^d * q d z) =
      (fun z => ∑ j : Fin k, (F j).eval z * p j z) := by
    funext z
    simp only [q, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Polynomial.eval_eq_sum_range' (hD j), Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  have hqbound := periodic_monomial_coefficients_exp_bound_range hh q
    (fun d _ => hqper d) (hexpand ▸ hg)
  have hall (d : ℕ) : ∀ j : Fin k, k-j.val = d → ExponentialBound (p j) := by
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro j hj
      let c := (F j).coeff (F j).natDegree
      have hc : c ≠ 0 := by
        simpa only [c, coeff_natDegree] using leadingCoeff_ne_zero.mpr (hF j)
      let tail (z : ℂ) := ∑ i ∈ Finset.univ.erase j,
        (F i).coeff (F j).natDegree * p i z
      have htail : ExponentialBound tail := by
        apply bound_sum
        intro i hi
        have hij : i ≠ j := (Finset.mem_erase.mp hi).1
        rcases lt_or_gt_of_ne hij with hlt | hgt
        · have hz := coeff_eq_zero_of_natDegree_lt (hdeg hlt)
          simpa only [hz, zero_mul] using bound_const (0 : ℂ)
        · exact (ih (k-i.val) (by have hv := hgt; change j.val < i.val at hv; omega)
            i rfl).const_mul ((F i).coeff (F j).natDegree)
      have heq (z : ℂ) : q (F j).natDegree z = tail z + c * p j z := by
        exact (Finset.sum_erase_add _ _ (Finset.mem_univ j)).symm
      have hb := ((hqbound (F j).natDegree (hD j)).sub htail).const_mul c⁻¹
      have he : (fun z => c⁻¹ * (q (F j).natDegree z-tail z)) = p j := by
        funext z
        rw [heq]
        simp [hc]
      rwa [he] at hb
  exact fun j => hall (k-j.val) j rfl

/-- Lemma 5.2 in its full distinct-degree polynomial basis, with the weaker
assumption of an upper exponential bound rather than exact order and type. -/
theorem lemma_5_2 {k : ℕ} (F : Fin k → Polynomial ℂ)
    (hF : ∀ j, F j ≠ 0) (hdeg : StrictMono (fun j => (F j).natDegree))
    (u : Fin k → ℂ → ℂ) (hu : ∀ j, Differentiable ℂ (u j))
    (hg : ExponentialBound (fun z => ∑ j : Fin k,
      (F j).eval z * u j (Complex.exp z))) :
    ∀ j, ∃ Q : Polynomial ℂ, ∀ w, u j w = Q.eval w := by
  have hp (j : Fin k) : Function.Periodic (fun z => u j (Complex.exp z))
      exponentialPeriod := by
    intro z
    simp only [exponentialPeriod, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  have hb := periodic_polynomial_coefficients_exp_bound exponentialPeriod_ne_zero
    F hF hdeg (fun j z => u j (Complex.exp z)) hp hg
  exact fun j => polynomial_of_exp_bound (hu j) (hb j)

/-- A common exponential factor is harmless in the distinct-degree version. -/
theorem lemma_5_2_with_exponential_factor {k : ℕ} (a : ℂ)
    (F : Fin k → Polynomial ℂ) (hF : ∀ j, F j ≠ 0)
    (hdeg : StrictMono (fun j => (F j).natDegree))
    (u : Fin k → ℂ → ℂ) (hu : ∀ j, Differentiable ℂ (u j))
    (hg : ExponentialBound (fun z => Complex.exp (a*z) *
      ∑ j : Fin k, (F j).eval z * u j (Complex.exp z))) :
    ∀ j, ∃ Q : Polynomial ℂ, ∀ w, u j w = Q.eval w := by
  apply lemma_5_2 F hF hdeg u hu
  simpa only [← mul_assoc, ← Complex.exp_add, neg_mul, neg_add_cancel,
    Complex.exp_zero, one_mul] using hg.remove_exponential a

/-- For a continuous function, finite positive type at order one supplies
the global upper bound used by the coefficient extraction theorem. -/
theorem exponentialBound_of_finitePositiveType_one {g : ℂ → ℂ}
    (hg : Continuous g) (ht : LevinGrowth.FinitePositiveType g 1) :
    ExponentialBound g := by
  obtain ⟨⟨C, hC, R, _hR, hbound⟩, _⟩ := ht
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
    hg.continuousOn
  let A := max 1 M
  have hA : 1 ≤ A := le_max_left _ _
  refine ⟨A, C, zero_le_one.trans hA, hC.le, fun z => ?_⟩
  by_cases hz : R ≤ ‖z‖
  · calc
      ‖g z‖ ≤ Real.exp (C * ‖z‖) := by simpa only [Real.rpow_one] using hbound z hz
      _ ≤ A * Real.exp (C * ‖z‖) :=
        le_mul_of_one_le_left (Real.exp_pos _).le hA
  · have hMz : ‖g z‖ ≤ M := hM z (by
      simpa only [Metric.mem_closedBall, dist_zero_right] using (le_of_not_ge hz))
    calc
      ‖g z‖ ≤ M := hMz
      _ ≤ A := le_max_right _ _
      _ ≤ A * Real.exp (C * ‖z‖) := le_mul_of_one_le_right (zero_le_one.trans hA)
        (Real.one_le_exp (mul_nonneg hC.le (norm_nonneg z)))

/-- The paper's mean-type hypothesis implies the full Lemma 5.2 conclusion.
The explicit order-one assumption is redundant once positive finite type at
that exponent is given. -/
theorem lemma_5_2_mean_type {k : ℕ} (F : Fin k → Polynomial ℂ)
    (hF : ∀ j, F j ≠ 0) (hdeg : StrictMono (fun j => (F j).natDegree))
    (u : Fin k → ℂ → ℂ) (hu : ∀ j, Differentiable ℂ (u j))
    (hg : LevinGrowth.FinitePositiveType
      (fun z => ∑ j : Fin k, (F j).eval z * u j (Complex.exp z)) 1) :
    ∀ j, ∃ Q : Polynomial ℂ, ∀ w, u j w = Q.eval w := by
  apply lemma_5_2 F hF hdeg u hu
  apply exponentialBound_of_finitePositiveType_one _ hg
  apply continuous_finsetSum
  intro j hj
  exact (F j).continuous.mul ((hu j).continuous.comp Complex.continuous_exp)

#print axioms periodic_polynomial_coefficients_exp_bound
#print axioms lemma_5_2
#print axioms lemma_5_2_with_exponential_factor
#print axioms exponentialBound_of_finitePositiveType_one
#print axioms lemma_5_2_mean_type

end LiWangWen
