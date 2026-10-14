import LiWangWenWimanValironUpper
import LiWangWenFiniteOrderFloquet
import LiWangWenPeriodicExponentialType
import LiWangWenExponentialSumAlgebra

/-!
# Theorem 3.5 through the direct Wiman--Valiron upper bound

This route first proves finite exponential type, then extracts exponential
bounds for actual entire periodic Floquet coefficients. Contour translation
and Fourier uniqueness turn those coefficients into finite Laurent sums.
No factorial-decay recurrence or central-index branch selection is used.
-/

set_option autoImplicit false
noncomputable section
open Polynomial
open scoped BigOperators

namespace LiWangWen

/-- The direct upper bound also includes polynomial and zero solutions. -/
theorem finiteOrder_solution_exponentialBound_direct {n : ℕ}
    {P : Fin (n+1) → Polynomial ℂ}
    (hlead : (P (Fin.last n)).eval 1 ≠ 0)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hfo : CRGOrder.FiniteOrder f) (hsol : Solves P f) : ExponentialBound f := by
  classical
  by_cases hnp : ¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z
  · exact finiteOrder_solution_direct_exponentialBound hlead hf hnp hfo hsol
  · obtain ⟨p,hp⟩ := not_not.mp hnp
    have he : f = fun z => p.eval z := funext hp
    rw [he]
    exact bound_poly_comp p bound_id

theorem FiniteOrderFloquetBlock.entire {h : ℂ} (b : FiniteOrderFloquetBlock h) :
    Differentiable ℂ b.eval := by
  apply Differentiable.mul
  · exact Complex.differentiable_exp.comp ((differentiable_const _).mul differentiable_id)
  · apply Differentiable.fun_sum
    intro j hj
    exact (differentiable_id.pow j).mul (b.regular j (Finset.mem_range.mp hj)).1

theorem FiniteOrderFloquetBlock.finiteOrder {h : ℂ} (b : FiniteOrderFloquetBlock h) :
    CRGOrder.FiniteOrder b.eval := by
  apply PowerExponentialBound.finiteOrder
  apply (power_bound_exp b.exponent).mul
  apply power_bound_sum
  intro j hj
  exact (power_bound_id.pow j).mul
    (power_bound_of_finiteOrder (b.regular j (Finset.mem_range.mp hj)).1
      (b.regular j (Finset.mem_range.mp hj)).2.2)

/-- Periodic coefficients inherit the proved growth bound of their actual
solution block, even when the coefficients cancel in the whole sum. -/
theorem direct_floquet_coefficients_exponentialBound {n : ℕ}
    {P : Fin (n+1) → Polynomial ℂ}
    (hlead : (P (Fin.last n)).eval 1 ≠ 0)
    (b : FiniteOrderFloquetBlock exponentialPeriod) (hsol : Solves P b.eval) :
    ∀ j < b.length, ExponentialBound (b.coefficient j) := by
  have hb := finiteOrder_solution_exponentialBound_direct hlead b.entire b.finiteOrder hsol
  have hsum : ExponentialBound
      (fun z => ∑ j ∈ Finset.range b.length, z^j * b.coefficient j z) := by
    have hremove := hb.remove_exponential b.exponent
    have he : (fun z => Complex.exp (-b.exponent*z) * b.eval z) =
        (fun z => ∑ j ∈ Finset.range b.length, z^j * b.coefficient j z) := by
      funext z
      dsimp [FiniteOrderFloquetBlock.eval]
      rw [← mul_assoc, ← Complex.exp_add,
        show -b.exponent*z + b.exponent*z = 0 by ring,
        Complex.exp_zero, one_mul]
    rwa [he] at hremove
  exact periodic_monomial_coefficients_exp_bound_range exponentialPeriod_ne_zero
    b.coefficient (fun j hj => (b.regular j hj).2.1) hsum

theorem direct_floquetBlock_isExponentialSum {n : ℕ}
    {P : Fin (n+1) → Polynomial ℂ}
    (hlead : (P (Fin.last n)).eval 1 ≠ 0)
    (b : FiniteOrderFloquetBlock exponentialPeriod) (hsol : Solves P b.eval) :
    IsExponentialSum b.eval := by
  have hbounds := direct_floquet_coefficients_exponentialBound hlead b hsol
  have hsum : IsExponentialSum
      (fun z => ∑ j ∈ Finset.range b.length, z^j * b.coefficient j z) := by
    apply isExponentialSum_finset_sum
    intro j hj
    have hjlt := Finset.mem_range.mp hj
    have hp := periodic_exponentialBound_isExponentialSum
      (b.regular j hjlt).1 (b.regular j hjlt).2.1 (hbounds j hjlt)
    simpa only [eval_pow, eval_X] using hp.polynomial_mul (X^j)
  exact hsum.exp_mul b.exponent

/-- The representation theorem now follows through the direct growth route. -/
theorem finiteOrder_solution_isExponentialSum_direct {n : ℕ}
    {P : Fin (n+1) → Polynomial ℂ}
    (hlead : (P (Fin.last n)).eval 1 ≠ 0)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hfo : CRGOrder.FiniteOrder f) (hsol : Solves P f) : IsExponentialSum f := by
  obtain ⟨bs,hbsol,hrep⟩ := polynomial_exp_finiteOrder_floquet_blocks hlead hf hfo hsol
  have hb : ∀ b ∈ bs, IsExponentialSum b.eval :=
    fun b hb => direct_floquetBlock_isExponentialSum hlead b (hbsol b hb)
  have he : f = (fun z => (bs.map (fun b => b.eval z)).sum) := funext hrep
  rw [he]
  exact isExponentialSum_list_sum bs FiniteOrderFloquetBlock.eval hb

/-- Theorem 3.5 for every natural leading power, without using the
representation theorem to obtain the growth hypothesis. -/
theorem theorem_3_5_direct {n γ : ℕ}
    {P : Fin (n+1) → Polynomial ℂ} (hlead : P (Fin.last n) = X^γ)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hfo : CRGOrder.FiniteOrder f) (hsol : Solves P f) : IsExponentialSum f :=
  finiteOrder_solution_isExponentialSum_direct (by simp [hlead]) hf hfo hsol

#print axioms finiteOrder_solution_exponentialBound_direct
#print axioms FiniteOrderFloquetBlock.entire
#print axioms FiniteOrderFloquetBlock.finiteOrder
#print axioms direct_floquet_coefficients_exponentialBound
#print axioms direct_floquetBlock_isExponentialSum
#print axioms finiteOrder_solution_isExponentialSum_direct
#print axioms theorem_3_5_direct

end LiWangWen
