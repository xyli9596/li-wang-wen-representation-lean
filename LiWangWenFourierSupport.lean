import LiWangWenFourierRecurrence
import Mathlib.Algebra.FiniteSupport.Basic

/-!
# Closure of finite Fourier support

These operations use the actual contour-integral coefficients. They support
descending induction through the polynomial factors of a Floquet block.
-/

set_option autoImplicit false
noncomputable section
open Complex Polynomial Finset Set
open scoped Topology

namespace LiWangWen

def HasFiniteFourierSupport (p : ℂ → ℂ) : Prop :=
  (Function.support (verticalFourierCoeff p)).Finite

theorem hasFiniteFourierSupport_zero : HasFiniteFourierSupport (fun _ => 0) := by
  simp [HasFiniteFourierSupport, Function.support, verticalFourierCoeff_zero]

theorem HasFiniteFourierSupport.add {p q : ℂ → ℂ}
    (hs : HasFiniteFourierSupport p) (ht : HasFiniteFourierSupport q)
    (hp : Continuous p) (hq : Continuous q) :
    HasFiniteFourierSupport (fun z => p z + q z) := by
  apply (hs.union ht).subset
  intro m hm
  by_contra h
  have hp0 : verticalFourierCoeff p m = 0 := by
    by_contra hne
    exact h (Or.inl hne)
  have hq0 : verticalFourierCoeff q m = 0 := by
    by_contra hne
    exact h (Or.inr hne)
  exact hm (by rw [verticalFourierCoeff_add hp hq, hp0, hq0, add_zero])

theorem HasFiniteFourierSupport.const_mul {p : ℂ → ℂ}
    (hs : HasFiniteFourierSupport p) (c : ℂ) :
    HasFiniteFourierSupport (fun z => c*p z) := by
  apply hs.subset
  intro m hm hp0
  exact hm (by rw [verticalFourierCoeff_const_mul, hp0, mul_zero])

theorem HasFiniteFourierSupport.neg {p : ℂ → ℂ}
    (hs : HasFiniteFourierSupport p) : HasFiniteFourierSupport (fun z => -p z) := by
  simpa only [neg_one_mul] using hs.const_mul (-1)

theorem HasFiniteFourierSupport.sub {p q : ℂ → ℂ}
    (hs : HasFiniteFourierSupport p) (ht : HasFiniteFourierSupport q)
    (hp : Continuous p) (hq : Continuous q) :
    HasFiniteFourierSupport (fun z => p z - q z) := by
  simpa only [sub_eq_add_neg] using hs.add ht.neg hp hq.neg

theorem hasFiniteFourierSupport_sum {ι : Type*} (s : Finset ι) (p : ι → ℂ → ℂ)
    (hp : ∀ i ∈ s, Continuous (p i))
    (hs : ∀ i ∈ s, HasFiniteFourierSupport (p i)) :
    HasFiniteFourierSupport (fun z => ∑ i ∈ s, p i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasFiniteFourierSupport_zero
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using
      (hs i (Finset.mem_insert_self i s)).add
        (ih (fun j hj => hp j (Finset.mem_insert_of_mem hj))
          (fun j hj => hs j (Finset.mem_insert_of_mem hj)))
        (hp i (Finset.mem_insert_self i s))
        (continuous_finsetSum _ (fun j hj => hp j (Finset.mem_insert_of_mem hj)))

theorem HasFiniteFourierSupport.deriv {p : ℂ → ℂ}
    (hs : HasFiniteFourierSupport p) (hp : Differentiable ℂ p)
    (hper : Function.Periodic p exponentialPeriod) : HasFiniteFourierSupport (deriv p) := by
  apply hs.subset
  intro m hm hp0
  exact hm (by rw [verticalFourierCoeff_deriv hp hper, hp0, mul_zero])

theorem HasFiniteFourierSupport.shiftedDeriv {p : ℂ → ℂ}
    (hs : HasFiniteFourierSupport p) (a : ℂ) (hp : Differentiable ℂ p)
    (hper : Function.Periodic p exponentialPeriod) :
    HasFiniteFourierSupport (shiftedDeriv a p) := by
  apply hs.subset
  intro m hm hp0
  exact hm (by rw [verticalFourierCoeff_shiftedDeriv a hp hper, hp0, mul_zero])

theorem HasFiniteFourierSupport.iterate_shiftedDeriv {p : ℂ → ℂ}
    (hs : HasFiniteFourierSupport p) (a : ℂ) (hp : Differentiable ℂ p)
    (hper : Function.Periodic p exponentialPeriod) (k : ℕ) :
    HasFiniteFourierSupport ((LiWangWen.shiftedDeriv a)^[k] p) := by
  apply hs.subset
  intro m hm hp0
  exact hm (by rw [verticalFourierCoeff_iterate_shiftedDeriv a hp hper, hp0, mul_zero])

theorem HasFiniteFourierSupport.exp_mul {p : ℂ → ℂ}
    (hs : HasFiniteFourierSupport p) (d : ℤ) :
    HasFiniteFourierSupport (fun z => Complex.exp ((d : ℂ)*z)*p z) := by
  apply (hs.image (fun m : ℤ => m+d)).subset
  intro m hm
  refine ⟨m-d,?_,sub_add_cancel m d⟩
  intro hp0
  exact hm (by rw [verticalFourierCoeff_exp_mul, hp0])

theorem HasFiniteFourierSupport.polynomial_exp_mul {p : ℂ → ℂ}
    (hs : HasFiniteFourierSupport p) (P : Polynomial ℂ) (hp : Continuous p) :
    HasFiniteFourierSupport (fun z => P.eval (Complex.exp z)*p z) := by
  have heq : (fun z => P.eval (Complex.exp z)*p z) =
      (fun z => ∑ d ∈ Finset.range (P.natDegree+1),
        P.coeff d * (Complex.exp ((d : ℂ)*z)*p z)) := by
    funext z
    rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d _
    rw [Complex.exp_nat_mul]
    ring
  rw [heq]
  apply hasFiniteFourierSupport_sum
  · intro d _
    fun_prop
  · intro d _
    exact (hs.exp_mul (d : ℤ)).const_mul (P.coeff d)

theorem hasFiniteFourierSupport_of_tail {p : ℂ → ℂ} (N : ℕ)
    (h : ∀ m : ℤ, (N : ℤ) ≤ |m| → verticalFourierCoeff p m = 0) :
    HasFiniteFourierSupport p := by
  apply (Set.finite_Icc (-(N : ℤ)) (N : ℤ)).subset
  intro m hm
  have hlt : |m| < (N : ℤ) := lt_of_not_ge (fun hge => hm (h m hge))
  exact ⟨(abs_lt.mp hlt).1.le, (abs_lt.mp hlt).2.le⟩

theorem HasFiniteFourierSupport.exists_tail {p : ℂ → ℂ}
    (hs : HasFiniteFourierSupport p) :
    ∃ N : ℕ, ∀ m : ℤ, (N : ℤ) ≤ |m| → verticalFourierCoeff p m = 0 := by
  classical
  let s : Finset ℤ := hs.toFinset
  let N : ℕ := (s.sup Int.natAbs)+1
  refine ⟨N,?_⟩
  intro m hm
  by_contra hne
  have hms : m ∈ s := hs.mem_toFinset.mpr hne
  have hmn : m.natAbs < N := Nat.lt_succ_of_le (Finset.le_sup hms)
  have hcast : (m.natAbs : ℤ) < (N : ℤ) := by exact_mod_cast hmn
  rw [Int.natCast_natAbs] at hcast
  exact (not_lt_of_ge hm) hcast

end LiWangWen

#print axioms LiWangWen.hasFiniteFourierSupport_zero
#print axioms LiWangWen.HasFiniteFourierSupport.add
#print axioms LiWangWen.HasFiniteFourierSupport.const_mul
#print axioms LiWangWen.HasFiniteFourierSupport.neg
#print axioms LiWangWen.HasFiniteFourierSupport.sub
#print axioms LiWangWen.hasFiniteFourierSupport_sum
#print axioms LiWangWen.HasFiniteFourierSupport.deriv
#print axioms LiWangWen.HasFiniteFourierSupport.shiftedDeriv
#print axioms LiWangWen.HasFiniteFourierSupport.iterate_shiftedDeriv
#print axioms LiWangWen.HasFiniteFourierSupport.exp_mul
#print axioms LiWangWen.HasFiniteFourierSupport.polynomial_exp_mul
#print axioms LiWangWen.hasFiniteFourierSupport_of_tail
#print axioms LiWangWen.HasFiniteFourierSupport.exists_tail
