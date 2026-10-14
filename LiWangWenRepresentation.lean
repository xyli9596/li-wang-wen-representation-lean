import LiWangWenFloquetCoefficientEquations
import LiWangWenFourierSupport
import LiWangWenLemma51Periodic
import LiWangWenFourierLaurent
import LiWangWenExponentialSumAlgebra

/-!
# Every finite-order entire solution of a nondegenerate equation is an exponential sum

The proof handles arbitrary generalized Floquet blocks. Descending through
their monomial degrees, the higher coefficients give a residual with finite
Fourier support; the scalar recurrence rigidity theorem forces the next
coefficient to have finite Fourier support too. Actual Fourier reconstruction
then produces the explicit exponential sum, including polynomial factors.
-/

noncomputable section
open Polynomial
open scoped BigOperators

namespace LiWangWen

theorem floquetMonomialContribution_entire (a : ℂ) {p : ℂ → ℂ}
    (hp : Differentiable ℂ p) (m d j : ℕ) :
    Differentiable ℂ (floquetMonomialContribution a p m d j) := by
  apply Differentiable.fun_sum
  intro i hi
  exact (differentiable_const _).mul (iterate_shiftedDeriv_entire a hp (d-i))

theorem floquetMonomialContribution_finiteFourier (a : ℂ) {p : ℂ → ℂ}
    (hp : Differentiable ℂ p) (hper : Function.Periodic p exponentialPeriod)
    (hs : HasFiniteFourierSupport p) (m d j : ℕ) :
    HasFiniteFourierSupport (floquetMonomialContribution a p m d j) := by
  apply hasFiniteFourierSupport_sum
  · intro i hi
    exact (continuous_const.mul (iterate_shiftedDeriv_entire a hp (d-i)).continuous)
  · intro i hi
    exact (hs.iterate_shiftedDeriv a hp hper (d-i)).const_mul _

/-- Every periodic coefficient in an actual finite-order Floquet solution
block has finite Fourier support. The proof is a descending induction and
does not assert that the original block is diagonalizable. -/
theorem floquet_block_coefficients_finiteFourier_of_nonzero {n : ℕ}
    (P : Fin (n+1) → Polynomial ℂ) (hne : ∃ d, P d ≠ 0)
    (a : ℂ) (k : ℕ) (p : ℕ → ℂ → ℂ)
    (hp : ∀ j < k, Differentiable ℂ (p j) ∧
      Function.Periodic (p j) exponentialPeriod ∧ CRGOrder.FiniteOrder (p j))
    (hsol : Solves P (fun z => Complex.exp (a*z)*∑ j ∈ Finset.range k, z^j*p j z)) :
    ∀ j < k, HasFiniteFourierSupport (p j) := by
  have H : ∀ t : ℕ, ∀ j < k, k-j = t → HasFiniteFourierSupport (p j) := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
      intro j hj ht
      have higher : ∀ m ∈ (Finset.range k).filter (j < ·), HasFiniteFourierSupport (p m) := by
        intro m hm
        have hmk := Finset.mem_range.mp (Finset.mem_filter.mp hm).1
        have hjm := (Finset.mem_filter.mp hm).2
        exact ih (k-m) (by omega) m hmk rfl
      let F : ℂ → ℂ := fun z => ∑ d : Fin (n+1), (P d).eval (Complex.exp z)*
        ∑ m ∈ (Finset.range k).filter (j < ·), floquetMonomialContribution a (p m) m d.val j z
      have hF : HasFiniteFourierSupport F := by
        apply hasFiniteFourierSupport_sum
        · intro d hd
          apply Continuous.mul
          · exact (P d).continuous.comp Complex.continuous_exp
          · apply continuous_finsetSum
            intro m hm
            exact (floquetMonomialContribution_entire a
              (hp m (Finset.mem_range.mp (Finset.mem_filter.mp hm).1)).1 m d.val j).continuous
        · intro d hd
          apply HasFiniteFourierSupport.polynomial_exp_mul
          · apply hasFiniteFourierSupport_sum
            · intro m hm
              exact (floquetMonomialContribution_entire a
                (hp m (Finset.mem_range.mp (Finset.mem_filter.mp hm).1)).1 m d.val j).continuous
            · intro m hm
              have hmk := Finset.mem_range.mp (Finset.mem_filter.mp hm).1
              exact floquetMonomialContribution_finiteFourier a (hp m hmk).1
                (hp m hmk).2.1 (higher m hm) m d.val j
          · apply continuous_finsetSum
            intro m hm
            exact (floquetMonomialContribution_entire a
              (hp m (Finset.mem_range.mp (Finset.mem_filter.mp hm).1)).1 m d.val j).continuous
      have heq : (fun z => ∑ d : Fin (n+1),
          (P d).eval (Complex.exp z)*((shiftedDeriv a)^[d.val] (p j)) z) = fun z => -F z := by
        funext z
        have hz := floquet_block_triangular_equation a k p
          (fun m hm => ⟨(hp m hm).1, (hp m hm).2.1⟩) hsol hj z
        exact eq_neg_of_add_eq_zero_left hz
      have hres : HasFiniteFourierSupport (fun z => ∑ d : Fin (n+1),
          (P d).eval (Complex.exp z)*((shiftedDeriv a)^[d.val] (p j)) z) := by
        rw [heq]
        exact hF.neg
      exact finite_fourier_support_of_bound (periodic_finiteOrder_fourier_support_of_nonzero_residual
        P a hne (hp j hj).1 (hp j hj).2.1 (hp j hj).2.2 hres.exists_tail)
  exact fun j hj => H (k-j) j hj rfl

/-- Reconstruction of every coefficient turns the complete generalized block
into the paper's explicit exponential sum with polynomial multipliers. -/
theorem finiteOrderFloquetBlock_isExponentialSum_of_nonzero {n : ℕ}
    (P : Fin (n+1) → Polynomial ℂ) (hne : ∃ d, P d ≠ 0)
    (b : FiniteOrderFloquetBlock exponentialPeriod)
    (hsol : Solves P b.eval) : IsExponentialSum b.eval := by
  have hsupport := floquet_block_coefficients_finiteFourier_of_nonzero P hne b.exponent b.length
    b.coefficient b.regular hsol
  have hsum : IsExponentialSum (fun z => ∑ j ∈ Finset.range b.length, z^j*b.coefficient j z) := by
    apply isExponentialSum_finset_sum
    intro j hj
    have hjlt := Finset.mem_range.mp hj
    have hp := finite_fourier_support_isExponentialSum (b.coefficient j)
      (b.regular j hjlt).1 (b.regular j hjlt).2.1 (hsupport j hjlt)
    simpa only [eval_pow, eval_X] using hp.polynomial_mul (X^j)
  exact hsum.exp_mul b.exponent

/-- The representation theorem for any polynomial/exponential equation whose
leading coefficient is nonzero at the origin. -/
theorem finiteOrder_solution_isExponentialSum_of_leading_eval {n : ℕ}
    {P : Fin (n+1) → Polynomial ℂ} (hlead : (P (Fin.last n)).eval 1 ≠ 0)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hfo : CRGOrder.FiniteOrder f)
    (hsol : Solves P f) : IsExponentialSum f := by
  obtain ⟨bs, hbsol, hrep⟩ := polynomial_exp_finiteOrder_floquet_blocks hlead hf hfo hsol
  have hne : ∃ d, P d ≠ 0 := ⟨Fin.last n, fun h => hlead (by rw [h, eval_zero])⟩
  have hb : ∀ b ∈ bs, IsExponentialSum b.eval := fun b hb =>
    finiteOrderFloquetBlock_isExponentialSum_of_nonzero P hne b (hbsol b hb)
  have heq : f = (fun z => (bs.map (fun b => b.eval z)).sum) := funext hrep
  rw [heq]
  exact isExponentialSum_list_sum bs FiniteOrderFloquetBlock.eval hb

/-- In particular every natural leading power allowed in Theorem 3.5 is covered. -/
theorem finiteOrder_solution_isExponentialSum_of_leading_power {n γ : ℕ}
    {P : Fin (n+1) → Polynomial ℂ} (hlead : P (Fin.last n) = X^γ)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hfo : CRGOrder.FiniteOrder f)
    (hsol : Solves P f) : IsExponentialSum f :=
  finiteOrder_solution_isExponentialSum_of_leading_eval (by simp [hlead]) hf hfo hsol

/-- The paper's monic equation is the case of leading power zero. -/
theorem finiteOrder_solution_isExponentialSum {n : ℕ}
    {P : Fin (n+1) → Polynomial ℂ} (hlead : P (Fin.last n) = 1)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hfo : CRGOrder.FiniteOrder f)
    (hsol : Solves P f) : IsExponentialSum f :=
  finiteOrder_solution_isExponentialSum_of_leading_eval (by simp [hlead]) hf hfo hsol

/-- Finite order and the explicit exponential-sum representation are
equivalent for entire solutions of the monic equation. -/
theorem finiteOrder_iff_isExponentialSum {n : ℕ}
    {P : Fin (n+1) → Polynomial ℂ} (hlead : P (Fin.last n) = 1)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hsol : Solves P f) :
    CRGOrder.FiniteOrder f ↔ IsExponentialSum f :=
  ⟨fun hfo => finiteOrder_solution_isExponentialSum hlead hf hfo hsol,
    IsExponentialSum.finiteOrder⟩

/-- Every entire finite-order solution of the nondegenerate equation has an
actual global exponential-type bound. -/
theorem finiteOrder_solution_exponentialBound_of_leading_eval {n : ℕ}
    {P : Fin (n+1) → Polynomial ℂ} (hlead : (P (Fin.last n)).eval 1 ≠ 0)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hfo : CRGOrder.FiniteOrder f)
    (hsol : Solves P f) : ExponentialBound f := by
  obtain ⟨N,p,a,hrep⟩ := finiteOrder_solution_isExponentialSum_of_leading_eval hlead hf hfo hsol
  have heq : f = (fun z => ∑ j : Fin N, (p j).eval z*Complex.exp (a j*z)) := funext hrep
  rw [heq]
  exact bound_sum Finset.univ _ (fun j _ =>
    (bound_poly_comp (p j) bound_id).mul (bound_exp (a j)))

/-- The exponential-type bound missing from the original Lemma 5.1 follows
from the proved representation, excluding intermediate `r log r` growth. -/
theorem finiteOrder_solution_exponentialBound {n : ℕ}
    {P : Fin (n+1) → Polynomial ℂ} (hlead : P (Fin.last n) = 1)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hfo : CRGOrder.FiniteOrder f)
    (hsol : Solves P f) : ExponentialBound f :=
  finiteOrder_solution_exponentialBound_of_leading_eval (by simp [hlead]) hf hfo hsol

/-- Exponential type for every natural leading power. -/
theorem finiteOrder_solution_exponentialBound_of_leading_power {n γ : ℕ}
    {P : Fin (n+1) → Polynomial ℂ} (hlead : P (Fin.last n) = X^γ)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hfo : CRGOrder.FiniteOrder f)
    (hsol : Solves P f) : ExponentialBound f :=
  finiteOrder_solution_exponentialBound_of_leading_eval (by simp [hlead]) hf hfo hsol

#print axioms floquetMonomialContribution_entire
#print axioms floquetMonomialContribution_finiteFourier
#print axioms floquet_block_coefficients_finiteFourier_of_nonzero
#print axioms finiteOrderFloquetBlock_isExponentialSum_of_nonzero
#print axioms finiteOrder_solution_isExponentialSum
#print axioms finiteOrder_solution_isExponentialSum_of_leading_eval
#print axioms finiteOrder_solution_isExponentialSum_of_leading_power
#print axioms finiteOrder_iff_isExponentialSum
#print axioms finiteOrder_solution_exponentialBound
#print axioms finiteOrder_solution_exponentialBound_of_leading_eval
#print axioms finiteOrder_solution_exponentialBound_of_leading_power

end LiWangWen
