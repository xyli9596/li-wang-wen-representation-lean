import LiWangWenLemma52
import LiWangWenPeriodicExponentialType

/-!
# Lemma 5.2′ with coefficients holomorphic on the punctured plane

An exponential bound on the whole polynomial-periodic sum is enough.
The coefficient extraction theorem supplies bounds for the individual
compositions with `exp`; the periodic Fourier theorem proves finite support,
and Fourier uniqueness reconstructs each composition. Applying the identity
at `log w` gives a finite Laurent polynomial at every nonzero `w`.

The origin is not part of the Laurent conclusion. If each coefficient is
also differentiable at zero, the ordinary-polynomial conclusion holds on all
of `ℂ`. No finite-support or Laurent-representation hypothesis is assumed.
-/

set_option autoImplicit false
noncomputable section
open Polynomial
open scoped BigOperators

namespace LiWangWen

/-- A function holomorphic off zero becomes entire after composition with exp. -/
theorem punctured_comp_exp_differentiable {u : ℂ → ℂ}
    (hu : DifferentiableOn ℂ u ({0}ᶜ : Set ℂ)) :
    Differentiable ℂ (fun z => u (Complex.exp z)) := by
  intro z
  have hz : Complex.exp z ∈ ({0}ᶜ : Set ℂ) := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using Complex.exp_ne_zero z
  exact (hu.differentiableAt (isOpen_compl_singleton.mem_nhds hz)).comp z
    (Complex.differentiable_exp z)

/-- The finite Laurent representation is a conclusion of the exponential
bound, including equality at every nonzero point of the original variable. -/
theorem laurent_polynomial_of_exp_bound {u : ℂ → ℂ}
    (hu : DifferentiableOn ℂ u ({0}ᶜ : Set ℂ))
    (hb : ExponentialBound (fun z => u (Complex.exp z))) :
    ∃ s : Finset ℤ, ∃ c : ℤ → ℂ, ∀ w : ℂ, w ≠ 0 →
      u w = ∑ m ∈ s, c m * w ^ m := by
  have hp := punctured_comp_exp_differentiable hu
  have hper : Function.Periodic (fun z => u (Complex.exp z)) exponentialPeriod := by
    intro z
    simp only [exponentialPeriod, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  have hs := periodic_exponentialBound_finiteFourier_support hp hper hb
  obtain ⟨s,hrep⟩ := finite_fourier_support_representation
    (fun z => u (Complex.exp z)) hp hper hs
  refine ⟨s,verticalFourierCoeff (fun z => u (Complex.exp z)),?_⟩
  intro w hw
  have h := hrep (Complex.log w)
  simpa only [Complex.exp_int_mul, Complex.exp_log hw] using h

/-- Cancellation-safe coefficient bounds for the punctured-plane variant.
Only periodicity is needed in this extraction step; holomorphy is used
later for Fourier reconstruction. -/
theorem punctured_polynomial_coefficients_exp_bound {k : ℕ}
    (F : Fin k → Polynomial ℂ) (hF : ∀ j, F j ≠ 0)
    (hdeg : StrictMono (fun j => (F j).natDegree))
    (u : Fin k → ℂ → ℂ)
    (hg : ExponentialBound (fun z => ∑ j : Fin k,
      (F j).eval z * u j (Complex.exp z))) :
    ∀ j, ExponentialBound (fun z => u j (Complex.exp z)) := by
  have hp (j : Fin k) : Function.Periodic (fun z => u j (Complex.exp z))
      exponentialPeriod := by
    intro z
    simp only [exponentialPeriod, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  exact periodic_polynomial_coefficients_exp_bound exponentialPeriod_ne_zero
    F hF hdeg (fun j z => u j (Complex.exp z)) hp hg

/-- Lemma 5.2′: nonzero polynomial factors of strictly increasing degrees,
punctured-plane holomorphic coefficients, and one exponential bound for the
whole sum imply a finite Laurent polynomial for every coefficient. -/
theorem lemma_5_2_prime {k : ℕ} (F : Fin k → Polynomial ℂ)
    (hF : ∀ j, F j ≠ 0) (hdeg : StrictMono (fun j => (F j).natDegree))
    (u : Fin k → ℂ → ℂ)
    (hu : ∀ j, DifferentiableOn ℂ (u j) ({0}ᶜ : Set ℂ))
    (hg : ExponentialBound (fun z => ∑ j : Fin k,
      (F j).eval z * u j (Complex.exp z))) :
    ∀ j, ∃ s : Finset ℤ, ∃ c : ℤ → ℂ, ∀ w : ℂ, w ≠ 0 →
      u j w = ∑ m ∈ s, c m * w ^ m := by
  have hb := punctured_polynomial_coefficients_exp_bound F hF hdeg u hg
  exact fun j => laurent_polynomial_of_exp_bound (hu j) (hb j)

/-- The literal symmetric Laurent range used in the manuscript. The finite
set obtained from Fourier reconstruction is padded with zero coefficients. -/
theorem lemma_5_2_prime_symmetric {k : ℕ} (F : Fin k → Polynomial ℂ)
    (hF : ∀ j, F j ≠ 0) (hdeg : StrictMono (fun j => (F j).natDegree))
    (u : Fin k → ℂ → ℂ)
    (hu : ∀ j, DifferentiableOn ℂ (u j) ({0}ᶜ : Set ℂ))
    (hg : ExponentialBound (fun z => ∑ j : Fin k,
      (F j).eval z * u j (Complex.exp z))) :
    ∀ j, ∃ N : ℕ, ∃ c : ℤ → ℂ, ∀ w : ℂ, w ≠ 0 →
      u j w = ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), c m * w ^ m := by
  classical
  intro j
  obtain ⟨s,c,hrep⟩ := lemma_5_2_prime F hF hdeg u hu hg j
  let N := s.sup Int.natAbs
  let a : ℤ → ℂ := fun m => if m ∈ s then c m else 0
  have hsub : s ⊆ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    intro m hm
    have hnat : m.natAbs ≤ N := Finset.le_sup (f := Int.natAbs) hm
    have hint : (m.natAbs : ℤ) ≤ (N : ℤ) := by exact_mod_cast hnat
    rw [Int.natCast_natAbs] at hint
    exact Finset.mem_Icc.mpr (abs_le.mp hint)
  refine ⟨N,a,?_⟩
  intro w hw
  rw [hrep w hw]
  calc
    (∑ m ∈ s, c m * w ^ m) = ∑ m ∈ s, a m * w ^ m := by
      apply Finset.sum_congr rfl
      intro m hm
      simp only [a, if_pos hm]
    _ = _ := Finset.sum_subset hsub (fun m _ hm => by simp only [a, if_neg hm, zero_mul])

/-- The same complete statement with a separately named whole sum `g`. -/
theorem lemma_5_2_prime_of_representation {k : ℕ} (F : Fin k → Polynomial ℂ)
    (hF : ∀ j, F j ≠ 0) (hdeg : StrictMono (fun j => (F j).natDegree))
    (u : Fin k → ℂ → ℂ)
    (hu : ∀ j, DifferentiableOn ℂ (u j) ({0}ᶜ : Set ℂ))
    {g : ℂ → ℂ} (hrep : ∀ z, g z = ∑ j : Fin k,
      (F j).eval z * u j (Complex.exp z)) (hg : ExponentialBound g) :
    ∀ j, ∃ s : Finset ℤ, ∃ c : ℤ → ℂ, ∀ w : ℂ, w ≠ 0 →
      u j w = ∑ m ∈ s, c m * w ^ m := by
  apply lemma_5_2_prime F hF hdeg u hu
  have heq : g = (fun z => ∑ j : Fin k,
      (F j).eval z * u j (Complex.exp z)) := funext hrep
  rwa [← heq]

/-- The manuscript's full named-sum statement with a symmetric Laurent range. -/
theorem lemma_5_2_prime_of_representation_symmetric {k : ℕ}
    (F : Fin k → Polynomial ℂ) (hF : ∀ j, F j ≠ 0)
    (hdeg : StrictMono (fun j => (F j).natDegree))
    (u : Fin k → ℂ → ℂ)
    (hu : ∀ j, DifferentiableOn ℂ (u j) ({0}ᶜ : Set ℂ))
    {g : ℂ → ℂ} (hrep : ∀ z, g z = ∑ j : Fin k,
      (F j).eval z * u j (Complex.exp z)) (hg : ExponentialBound g) :
    ∀ j, ∃ N : ℕ, ∃ c : ℤ → ℂ, ∀ w : ℂ, w ≠ 0 →
      u j w = ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), c m * w ^ m := by
  apply lemma_5_2_prime_symmetric F hF hdeg u hu
  have heq : g = (fun z => ∑ j : Fin k,
      (F j).eval z * u j (Complex.exp z)) := funext hrep
  rwa [← heq]

/-- If the punctured coefficients are also holomorphic at zero, Lemma 5.2′
has the ordinary-polynomial conclusion, including equality at zero. -/
theorem lemma_5_2_prime_holomorphic_at_zero {k : ℕ} (F : Fin k → Polynomial ℂ)
    (hF : ∀ j, F j ≠ 0) (hdeg : StrictMono (fun j => (F j).natDegree))
    (u : Fin k → ℂ → ℂ)
    (hu : ∀ j, DifferentiableOn ℂ (u j) ({0}ᶜ : Set ℂ))
    (hu0 : ∀ j, DifferentiableAt ℂ (u j) 0)
    (hg : ExponentialBound (fun z => ∑ j : Fin k,
      (F j).eval z * u j (Complex.exp z))) :
    ∀ j, ∃ Q : Polynomial ℂ, ∀ w : ℂ, u j w = Q.eval w := by
  have hb := punctured_polynomial_coefficients_exp_bound F hF hdeg u hg
  intro j
  apply polynomial_of_exp_bound _ (hb j)
  intro w
  by_cases hw : w = 0
  · simpa only [hw] using hu0 j
  · exact (hu j).differentiableAt (isOpen_compl_singleton.mem_nhds hw)

/-- In particular, entire coefficients in Lemma 5.2′ are ordinary polynomials. -/
theorem lemma_5_2_prime_entire {k : ℕ} (F : Fin k → Polynomial ℂ)
    (hF : ∀ j, F j ≠ 0) (hdeg : StrictMono (fun j => (F j).natDegree))
    (u : Fin k → ℂ → ℂ) (hu : ∀ j, Differentiable ℂ (u j))
    (hg : ExponentialBound (fun z => ∑ j : Fin k,
      (F j).eval z * u j (Complex.exp z))) :
    ∀ j, ∃ Q : Polynomial ℂ, ∀ w : ℂ, u j w = Q.eval w :=
  lemma_5_2_prime_holomorphic_at_zero F hF hdeg u
    (fun j => (hu j).differentiableOn) (fun j => hu j 0) hg

#print axioms punctured_comp_exp_differentiable
#print axioms laurent_polynomial_of_exp_bound
#print axioms punctured_polynomial_coefficients_exp_bound
#print axioms lemma_5_2_prime
#print axioms lemma_5_2_prime_symmetric
#print axioms lemma_5_2_prime_of_representation
#print axioms lemma_5_2_prime_of_representation_symmetric
#print axioms lemma_5_2_prime_holomorphic_at_zero
#print axioms lemma_5_2_prime_entire

end LiWangWen
