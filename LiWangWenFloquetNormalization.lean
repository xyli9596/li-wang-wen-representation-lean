import LiWangWenFloquetIndicial
import LiWangWenLaurentNormalization
import LiWangWenTheorem35Direct

set_option autoImplicit false
noncomputable section
open Polynomial
open scoped BigOperators

namespace LiWangWen

/-- A Fourier lower bound, rather than a prescribed individual minimum,
 permits a common polynomial normalization for an entire Floquet block. -/
theorem finite_fourier_lift_of_lower_bound {p : ℂ → ℂ}
    (hp : Differentiable ℂ p) (hper : Function.Periodic p exponentialPeriod)
    (hs : (Function.support (verticalFourierCoeff p)).Finite)
    (m : ℤ) (hlow : ∀ l < m, verticalFourierCoeff p l = 0) :
    ∃ u : Polynomial ℂ, p = lift (m : ℂ) u := by
  classical
  let s := hs.toFinset
  have hz : ∀ l ∉ s, verticalFourierCoeff p l = 0 := by
    intro l hl
    exact not_not.mp (fun h => hl (hs.mem_toFinset.mpr h))
  have hmin (l : ℤ) (hl : l ∈ s) : m ≤ l := by
    by_contra h
    exact (hs.mem_toFinset.mp hl) (hlow l (lt_of_not_ge h))
  let u : Polynomial ℂ := ∑ l ∈ s, C (verticalFourierCoeff p l)*X^(l-m).toNat
  refine ⟨u,?_⟩
  funext z
  rw [finite_fourier_reconstruction p hp hper s hz z]
  dsimp [lift,u]
  simp only [eval_finsetSum,eval_mul,eval_C,eval_pow,eval_X,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  have hc : ((l-m).toNat : ℂ) = (l : ℂ)-(m : ℂ) := by
    exact_mod_cast Int.toNat_of_nonneg (sub_nonneg.mpr (hmin l hl))
  have he : Complex.exp ((m : ℂ)*z)*Complex.exp z ^ (l-m).toNat =
      Complex.exp ((l : ℂ)*z) := by
    rw [← Complex.exp_nat_mul,← Complex.exp_add]
    congr 1
    rw [hc]
    ring
  rw [← he]
  ring

/-- Normalize a nonzero actual solution block using its common lowest
 Fourier frequency, preserving every monomial degree. The finite Fourier
 support is supplied by either of the two independently proved routes. -/
theorem normalized_floquet_solution_block_of_finiteFourier {n : ℕ}
    {P : Fin (n+1) → Polynomial ℂ}
    (b : FiniteOrderFloquetBlock exponentialPeriod)
    (hsol : Solves P b.eval) (hne : b.eval ≠ 0)
    (hs : ∀ j < b.length,
      (Function.support (verticalFourierCoeff (b.coefficient j))).Finite) :
    ∃ a : ℂ, ∃ u : ℕ → Polynomial ℂ, indicial P a = 0 ∧
      ∀ z, b.eval z = Complex.exp (a*z)*
        ∑ j ∈ Finset.range b.length, z^j*(u j).eval (Complex.exp z) := by
  classical
  let S (j : ℕ) : Finset ℤ := if hj : j < b.length then (hs j hj).toFinset else ∅
  let s := (Finset.range b.length).biUnion S
  have hmem (j : ℕ) (hj : j < b.length) (m : ℤ) :
      m ∈ S j ↔ verticalFourierCoeff (b.coefficient j) m ≠ 0 := by
    simp only [S,dif_pos hj]
    exact (hs j hj).mem_toFinset
  have hsn : s.Nonempty := by
    by_contra h
    have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have hpzero (j : ℕ) (hj : j < b.length) : b.coefficient j = 0 := by
      funext z
      have hz : ∀ m ∉ (∅ : Finset ℤ), verticalFourierCoeff (b.coefficient j) m = 0 := by
        intro m hm
        by_contra hc
        have hms : m ∈ s := Finset.mem_biUnion.mpr
          ⟨j,Finset.mem_range.mpr hj,(hmem j hj m).mpr hc⟩
        simp [hempty] at hms
      simpa using finite_fourier_reconstruction (b.coefficient j) (b.regular j hj).1
        (b.regular j hj).2.1 ∅ hz z
    apply hne
    funext z
    simp only [FiniteOrderFloquetBlock.eval,Pi.zero_apply]
    rw [Finset.sum_eq_zero]
    · simp
    · intro j hj
      rw [hpzero j (Finset.mem_range.mp hj)]
      simp
  let m := s.min' hsn
  have hm : m ∈ s := Finset.min'_mem s hsn
  have hlow : ∀ j < b.length, ∀ t < m, verticalFourierCoeff (b.coefficient j) t = 0 := by
    intro j hj t ht
    by_contra h
    have hts : t ∈ s := Finset.mem_biUnion.mpr
      ⟨j,Finset.mem_range.mpr hj,(hmem j hj t).mpr h⟩
    have hmt := Finset.min'_le s t hts
    omega
  let J := (Finset.range b.length).filter
    (fun j => verticalFourierCoeff (b.coefficient j) m ≠ 0)
  have hJn : J.Nonempty := by
    obtain ⟨j,hj,hjm⟩ := Finset.mem_biUnion.mp hm
    exact ⟨j,Finset.mem_filter.mpr ⟨hj,(hmem j (Finset.mem_range.mp hj) m).mp hjm⟩⟩
  let j := J.max' hJn
  have hjmem : j ∈ J := Finset.max'_mem J hJn
  have hj : j < b.length := Finset.mem_range.mp (Finset.mem_filter.mp hjmem).1
  have hjne : verticalFourierCoeff (b.coefficient j) m ≠ 0 :=
    (Finset.mem_filter.mp hjmem).2
  have hhigher : ∀ l < b.length, j < l → verticalFourierCoeff (b.coefficient l) m = 0 := by
    intro l hl hjl
    by_contra hc
    have hlj := Finset.le_max' J l (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hl,hc⟩)
    omega
  have hroot : indicial P (b.exponent+(m : ℂ)) = 0 :=
    floquet_indicial_root_at_lowest_frequency b.exponent b.length b.coefficient
      (fun l hl => ⟨(b.regular l hl).1,(b.regular l hl).2.1⟩) hsol m hlow hj hjne hhigher
  have hup : ∀ j < b.length, ∃ u : Polynomial ℂ,
      b.coefficient j = lift (m : ℂ) u := by
    intro j hj
    exact finite_fourier_lift_of_lower_bound (b.regular j hj).1
      (b.regular j hj).2.1 (hs j hj) m (hlow j hj)
  let u : ℕ → Polynomial ℂ := fun j => if hj : j < b.length then (hup j hj).choose else 0
  have hu (j : ℕ) (hj : j < b.length) : b.coefficient j = lift (m : ℂ) (u j) := by
    simpa only [u,dif_pos hj] using (hup j hj).choose_spec
  refine ⟨b.exponent+(m : ℂ),u,hroot,?_⟩
  intro z
  simp only [FiniteOrderFloquetBlock.eval,add_mul,Complex.exp_add,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hu j (Finset.mem_range.mp hj)]
  dsimp [lift]
  ring

/-- The direct Wiman--Valiron route proves the Fourier-support premise and
then applies the common normalization argument. -/
theorem normalized_floquet_solution_block {n : ℕ}
    {P : Fin (n+1) → Polynomial ℂ} (hlead : (P (Fin.last n)).eval 1 ≠ 0)
    (b : FiniteOrderFloquetBlock exponentialPeriod)
    (hsol : Solves P b.eval) (hne : b.eval ≠ 0) :
    ∃ a : ℂ, ∃ u : ℕ → Polynomial ℂ, indicial P a = 0 ∧
      ∀ z, b.eval z = Complex.exp (a*z)*
        ∑ j ∈ Finset.range b.length, z^j*(u j).eval (Complex.exp z) := by
  apply normalized_floquet_solution_block_of_finiteFourier b hsol hne
  intro j hj
  exact periodic_exponentialBound_finiteFourier_support (b.regular j hj).1
    (b.regular j hj).2.1 (direct_floquet_coefficients_exponentialBound hlead b hsol j hj)

/-- The factorial-recurrence route proves the same normalization directly
from finite-order Floquet coefficients, without the direct growth theorem. -/
theorem normalized_floquet_solution_block_recurrence {n : ℕ}
    {P : Fin (n+1) → Polynomial ℂ} (hlead : (P (Fin.last n)).eval 1 ≠ 0)
    (b : FiniteOrderFloquetBlock exponentialPeriod)
    (hsol : Solves P b.eval) (hne : b.eval ≠ 0) :
    ∃ a : ℂ, ∃ u : ℕ → Polynomial ℂ, indicial P a = 0 ∧
      ∀ z, b.eval z = Complex.exp (a*z)*
        ∑ j ∈ Finset.range b.length, z^j*(u j).eval (Complex.exp z) := by
  have hP : ∃ d, P d ≠ 0 := ⟨Fin.last n, fun h => hlead (by rw [h,eval_zero])⟩
  exact normalized_floquet_solution_block_of_finiteFourier b hsol hne
    (floquet_block_coefficients_finiteFourier_of_nonzero P hP
      b.exponent b.length b.coefficient b.regular hsol)

#print axioms finite_fourier_lift_of_lower_bound
#print axioms normalized_floquet_solution_block_of_finiteFourier
#print axioms normalized_floquet_solution_block
#print axioms normalized_floquet_solution_block_recurrence
end LiWangWen
