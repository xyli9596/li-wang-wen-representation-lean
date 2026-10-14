import LiWangWenBoundedFloquet
import LiWangWenFloquetNormalization

set_option autoImplicit false
noncomputable section
open Polynomial
open scoped BigOperators

namespace LiWangWen

/-- The direct Wiman--Valiron route to Theorem 3.2 with the paper's indicial roots and total logarithmic-degree
 budget. The polynomial factors in the free variable are chosen as `X^p`,
 so their degrees are exactly `p`. No root or degree bound is a hypothesis. -/
theorem theorem_3_2 {n : ℕ} {P : Fin (n+1) → Polynomial ℂ}
    (hlead : P (Fin.last n) = 1) {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hfo : CRGOrder.FiniteOrder f) (hsol : Solves P f) :
    ∃ m : ℕ, ∃ a : Fin m → ℂ, ∃ K : Fin m → ℕ,
      ∃ u : Fin m → ℕ → Polynomial ℂ,
      (∀ j, indicial P (a j) = 0) ∧ (∑ j, K j) ≤ n ∧
      ∀ z, f z = ∑ j : Fin m, Complex.exp (a j*z)*
        ∑ p ∈ Finset.range (K j+1), z^p*(u j p).eval (Complex.exp z) := by
  classical
  let A : Fin (n+1) → ℂ → ℂ := fun j z => (P j).eval (Complex.exp z)
  have hA : ∀ j, Differentiable ℂ (A j) :=
    fun j => (P j).differentiable.comp Complex.differentiable_exp
  have hAl : A (Fin.last n) 0 ≠ 0 := by simp [A,hlead]
  have hAp : ∀ j, Function.Periodic (A j) exponentialPeriod := by
    intro j
    simpa only [A,frequencyPeriod,div_one,one_mul,Function.comp_def] using
      frequency_coefficients_periodic P (ω := 1) one_ne_zero j
  obtain ⟨s,B,hB,hbudget,hrep⟩ := bounded_finiteOrder_floquet_blocks
    hA hAl exponentialPeriod_ne_zero hAp hf hfo hsol
  have hnorm (c : s) : ∃ a : ℂ, ∃ u : ℕ → Polynomial ℂ, indicial P a = 0 ∧
      ∀ z, (B c).eval z = Complex.exp (a*z)*
        ∑ j ∈ Finset.range (B c).length, z^j*(u j).eval (Complex.exp z) :=
    normalized_floquet_solution_block (by simp [hlead]) (B c) (hB c).1 (hB c).2.1
  choose a u hroot hnormrep using hnorm
  let m := Fintype.card s
  let e : Fin m ≃ s := (Fintype.equivFin s).symm
  let K : Fin m → ℕ := fun j => (B (e j)).length-1
  refine ⟨m,a ∘ e,K,u ∘ e,?_,?_,?_⟩
  · intro j
    exact hroot (e j)
  · calc
      (∑ j, K j) ≤ ∑ j : Fin m, (B (e j)).length :=
        Finset.sum_le_sum (fun j hj => Nat.sub_le _ _)
      _ = ∑ c : s, (B c).length := e.sum_comp (fun c => (B c).length)
      _ ≤ n := hbudget
  · intro z
    rw [hrep]
    have he := e.sum_comp (fun c => (B c).eval z)
    rw [← he]
    apply Finset.sum_congr rfl
    intro j hj
    have hlen : K j+1 = (B (e j)).length := by
      dsimp [K]
      have hpos := (hB (e j)).2.2
      omega
    simpa only [Function.comp_apply,hlen] using hnormrep (e j) z

/-- A literal polynomial-factor version of (3.5), with `C_j=1`.
 The degree requirement is retained explicitly, including `p=0`. -/
theorem theorem_3_2_polynomial_factors {n : ℕ} {P : Fin (n+1) → Polynomial ℂ}
    (hlead : P (Fin.last n) = 1) {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hfo : CRGOrder.FiniteOrder f) (hsol : Solves P f) :
    ∃ m : ℕ, ∃ a : Fin m → ℂ, ∃ K : Fin m → ℕ,
      ∃ F u : Fin m → ℕ → Polynomial ℂ,
      (∀ j, indicial P (a j) = 0) ∧ (∑ j, K j) ≤ n ∧
      (∀ j p, (F j p).degree = (p : WithBot ℕ)) ∧
      ∀ z, f z = ∑ j : Fin m, Complex.exp (a j*z)*
        ∑ p ∈ Finset.range (K j+1), (F j p).eval z*(u j p).eval (Complex.exp z) := by
  obtain ⟨m,a,K,u,hroot,hbudget,hrep⟩ := theorem_3_2 hlead hf hfo hsol
  refine ⟨m,a,K,(fun _ p => X^p),u,hroot,hbudget,?_,?_⟩
  · intro j p
    simp
  · simpa only [eval_pow,eval_X] using hrep

/-- The factorial-recurrence route to Theorem 3.2, including the paper's
 indicial roots and total logarithmic-degree budget. The polynomial factors in the free variable are chosen as `X^p`,
 so their degrees are exactly `p`. No root or degree bound is a hypothesis. -/
theorem theorem_3_2_recurrence {n : ℕ} {P : Fin (n+1) → Polynomial ℂ}
    (hlead : P (Fin.last n) = 1) {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hfo : CRGOrder.FiniteOrder f) (hsol : Solves P f) :
    ∃ m : ℕ, ∃ a : Fin m → ℂ, ∃ K : Fin m → ℕ,
      ∃ u : Fin m → ℕ → Polynomial ℂ,
      (∀ j, indicial P (a j) = 0) ∧ (∑ j, K j) ≤ n ∧
      ∀ z, f z = ∑ j : Fin m, Complex.exp (a j*z)*
        ∑ p ∈ Finset.range (K j+1), z^p*(u j p).eval (Complex.exp z) := by
  classical
  let A : Fin (n+1) → ℂ → ℂ := fun j z => (P j).eval (Complex.exp z)
  have hA : ∀ j, Differentiable ℂ (A j) :=
    fun j => (P j).differentiable.comp Complex.differentiable_exp
  have hAl : A (Fin.last n) 0 ≠ 0 := by simp [A,hlead]
  have hAp : ∀ j, Function.Periodic (A j) exponentialPeriod := by
    intro j
    simpa only [A,frequencyPeriod,div_one,one_mul,Function.comp_def] using
      frequency_coefficients_periodic P (ω := 1) one_ne_zero j
  obtain ⟨s,B,hB,hbudget,hrep⟩ := bounded_finiteOrder_floquet_blocks
    hA hAl exponentialPeriod_ne_zero hAp hf hfo hsol
  have hnorm (c : s) : ∃ a : ℂ, ∃ u : ℕ → Polynomial ℂ, indicial P a = 0 ∧
      ∀ z, (B c).eval z = Complex.exp (a*z)*
        ∑ j ∈ Finset.range (B c).length, z^j*(u j).eval (Complex.exp z) :=
    normalized_floquet_solution_block_recurrence (by simp [hlead]) (B c) (hB c).1 (hB c).2.1
  choose a u hroot hnormrep using hnorm
  let m := Fintype.card s
  let e : Fin m ≃ s := (Fintype.equivFin s).symm
  let K : Fin m → ℕ := fun j => (B (e j)).length-1
  refine ⟨m,a ∘ e,K,u ∘ e,?_,?_,?_⟩
  · intro j
    exact hroot (e j)
  · calc
      (∑ j, K j) ≤ ∑ j : Fin m, (B (e j)).length :=
        Finset.sum_le_sum (fun j hj => Nat.sub_le _ _)
      _ = ∑ c : s, (B c).length := e.sum_comp (fun c => (B c).length)
      _ ≤ n := hbudget
  · intro z
    rw [hrep]
    have he := e.sum_comp (fun c => (B c).eval z)
    rw [← he]
    apply Finset.sum_congr rfl
    intro j hj
    have hlen : K j+1 = (B (e j)).length := by
      dsimp [K]
      have hpos := (hB (e j)).2.2
      omega
    simpa only [Function.comp_apply,hlen] using hnormrep (e j) z

/-- The polynomial-factor version of (3.5) through the recurrence route,
 with `C_j=1`.
 The degree requirement is retained explicitly, including `p=0`. -/
theorem theorem_3_2_polynomial_factors_recurrence {n : ℕ} {P : Fin (n+1) → Polynomial ℂ}
    (hlead : P (Fin.last n) = 1) {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hfo : CRGOrder.FiniteOrder f) (hsol : Solves P f) :
    ∃ m : ℕ, ∃ a : Fin m → ℂ, ∃ K : Fin m → ℕ,
      ∃ F u : Fin m → ℕ → Polynomial ℂ,
      (∀ j, indicial P (a j) = 0) ∧ (∑ j, K j) ≤ n ∧
      (∀ j p, (F j p).degree = (p : WithBot ℕ)) ∧
      ∀ z, f z = ∑ j : Fin m, Complex.exp (a j*z)*
        ∑ p ∈ Finset.range (K j+1), (F j p).eval z*(u j p).eval (Complex.exp z) := by
  obtain ⟨m,a,K,u,hroot,hbudget,hrep⟩ := theorem_3_2_recurrence hlead hf hfo hsol
  refine ⟨m,a,K,(fun _ p => X^p),u,hroot,hbudget,?_,?_⟩
  · intro j p
    simp
  · simpa only [eval_pow,eval_X] using hrep

#print axioms theorem_3_2
#print axioms theorem_3_2_polynomial_factors
#print axioms theorem_3_2_recurrence
#print axioms theorem_3_2_polynomial_factors_recurrence
end LiWangWen
