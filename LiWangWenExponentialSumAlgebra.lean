import LiWangWenGrowth
import Mathlib.Data.Fintype.EquivFin

/-! Algebraic closure of the paper's explicit exponential-sum representation. -/

noncomputable section
open Polynomial
open scoped BigOperators

namespace LiWangWen

/-- A representation over any finite index type has the required `Fin N` form. -/
theorem isExponentialSum_of_fintype {ι : Type*} [Fintype ι]
    (p : ι → Polynomial ℂ) (a : ι → ℂ) {f : ℂ → ℂ}
    (hf : ∀ z, f z = ∑ j, (p j).eval z*Complex.exp (a j*z)) : IsExponentialSum f := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  refine ⟨Fintype.card ι, p ∘ e, a ∘ e, fun z => ?_⟩
  rw [hf]
  exact (e.sum_comp (fun j => (p j).eval z*Complex.exp (a j*z))).symm

theorem isExponentialSum_zero : IsExponentialSum (0 : ℂ → ℂ) := by
  exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩

theorem IsExponentialSum.add {f g : ℂ → ℂ}
    (hf : IsExponentialSum f) (hg : IsExponentialSum g) : IsExponentialSum (f+g) := by
  obtain ⟨m, p, a, hp⟩ := hf
  obtain ⟨n, q, b, hq⟩ := hg
  apply isExponentialSum_of_fintype (Sum.elim p q) (Sum.elim a b)
  intro z
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.add_apply, hp, hq]

theorem IsExponentialSum.polynomial_mul {f : ℂ → ℂ}
    (hf : IsExponentialSum f) (q : Polynomial ℂ) :
    IsExponentialSum (fun z => q.eval z*f z) := by
  obtain ⟨n, p, a, hp⟩ := hf
  refine ⟨n, fun j => q*p j, a, fun z => ?_⟩
  dsimp only
  rw [hp, Finset.mul_sum]
  simp only [eval_mul, mul_assoc]

theorem IsExponentialSum.exp_mul {f : ℂ → ℂ}
    (hf : IsExponentialSum f) (b : ℂ) :
    IsExponentialSum (fun z => Complex.exp (b*z)*f z) := by
  obtain ⟨n, p, a, hp⟩ := hf
  refine ⟨n, p, fun j => b+a j, fun z => ?_⟩
  dsimp only
  rw [hp, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [add_mul, Complex.exp_add]
  ring

theorem isExponentialSum_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ)
    (h : ∀ j ∈ s, IsExponentialSum (f j)) : IsExponentialSum (fun z => ∑ j ∈ s, f j z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty, Pi.zero_def] using isExponentialSum_zero
  | @insert j s hj ih =>
    simpa only [Finset.sum_insert hj, Pi.add_def] using
      (h j (Finset.mem_insert_self _ _)).add (ih (fun k hk => h k (Finset.mem_insert_of_mem hk)))

theorem isExponentialSum_list_sum {ι : Type*} (s : List ι) (f : ι → ℂ → ℂ)
    (h : ∀ j ∈ s, IsExponentialSum (f j)) :
    IsExponentialSum (fun z => (s.map (fun j => f j z)).sum) := by
  induction s with
  | nil => simpa only [List.map_nil, List.sum_nil, Pi.zero_def] using isExponentialSum_zero
  | cons j s ih =>
    simpa only [List.map_cons, List.sum_cons, Pi.add_def] using
      (h j List.mem_cons_self).add (ih (fun k hk => h k (List.mem_cons_of_mem j hk)))

#print axioms isExponentialSum_of_fintype
#print axioms isExponentialSum_zero
#print axioms IsExponentialSum.add
#print axioms IsExponentialSum.polynomial_mul
#print axioms IsExponentialSum.exp_mul
#print axioms isExponentialSum_finset_sum
#print axioms isExponentialSum_list_sum

end LiWangWen
