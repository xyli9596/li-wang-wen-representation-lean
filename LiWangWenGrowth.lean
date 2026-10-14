import LiWangWenCore

/-! Elementary growth facts for the exact representations. These prove the
finite-order direction from an exponential sum; they do not assert the converse. -/
set_option autoImplicit false
noncomputable section
open Polynomial
open scoped BigOperators
namespace LiWangWen

/-- A global exponential-type upper bound, allowing the zero function. -/
def ExponentialBound (f : ℂ → ℂ) : Prop :=
  ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ z, ‖f z‖ ≤ A * Real.exp (B * ‖z‖)

theorem bound_const (c : ℂ) : ExponentialBound (fun _ => c) := by
  exact ⟨‖c‖, 0, norm_nonneg _, le_rfl, by simp⟩

theorem bound_id : ExponentialBound (fun z : ℂ => z) := by
  refine ⟨1, 1, zero_le_one, zero_le_one, ?_⟩
  intro z
  simpa using (show ‖z‖ ≤ Real.exp ‖z‖ by linarith [Real.add_one_le_exp ‖z‖])

theorem bound_exp (a : ℂ) : ExponentialBound (fun z => Complex.exp (a*z)) := by
  refine ⟨1, ‖a‖, zero_le_one, norm_nonneg _, ?_⟩
  intro z
  simpa [norm_mul] using Complex.norm_exp_le_exp_norm (a*z)

theorem ExponentialBound.add {f g : ℂ → ℂ} (hf : ExponentialBound f)
    (hg : ExponentialBound g) : ExponentialBound (fun z => f z + g z) := by
  obtain ⟨A, B, hA, hB, hf⟩ := hf
  obtain ⟨C, D, hC, hD, hg⟩ := hg
  refine ⟨A+C, B+D, add_nonneg hA hC, add_nonneg hB hD, fun z => ?_⟩
  calc
    ‖f z + g z‖ ≤ ‖f z‖ + ‖g z‖ := norm_add_le _ _
    _ ≤ A * Real.exp (B*‖z‖) + C * Real.exp (D*‖z‖) := add_le_add (hf z) (hg z)
    _ ≤ A * Real.exp ((B+D)*‖z‖) + C * Real.exp ((B+D)*‖z‖) := by
      apply add_le_add <;> apply mul_le_mul_of_nonneg_left _ (by assumption)
      · apply Real.exp_le_exp.mpr
        nlinarith [norm_nonneg z]
      · apply Real.exp_le_exp.mpr
        nlinarith [norm_nonneg z]
    _ = (A+C) * Real.exp ((B+D)*‖z‖) := by ring

theorem ExponentialBound.mul {f g : ℂ → ℂ} (hf : ExponentialBound f)
    (hg : ExponentialBound g) : ExponentialBound (fun z => f z * g z) := by
  obtain ⟨A, B, hA, hB, hf⟩ := hf
  obtain ⟨C, D, hC, hD, hg⟩ := hg
  refine ⟨A*C, B+D, mul_nonneg hA hC, add_nonneg hB hD, fun z => ?_⟩
  calc
    ‖f z * g z‖ = ‖f z‖ * ‖g z‖ := norm_mul _ _
    _ ≤ (A * Real.exp (B*‖z‖)) * (C * Real.exp (D*‖z‖)) :=
      mul_le_mul (hf z) (hg z) (norm_nonneg _) (mul_nonneg hA (Real.exp_pos _).le)
    _ = (A*C) * Real.exp ((B+D)*‖z‖) := by rw [add_mul, Real.exp_add]; ring

theorem ExponentialBound.pow {f : ℂ → ℂ} (hf : ExponentialBound f) (k : ℕ) :
    ExponentialBound (fun z => f z ^ k) := by
  induction k with
  | zero => simpa using bound_const 1
  | succ k ih => simpa only [pow_succ] using ih.mul hf

theorem bound_poly_comp (p : Polynomial ℂ) {f : ℂ → ℂ} (hf : ExponentialBound f) :
    ExponentialBound (fun z => p.eval (f z)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [eval_add] using hp.add hq
  | monomial k c => simpa only [eval_monomial] using (bound_const c).mul (hf.pow k)

theorem bound_lift (a : ℂ) (u : Polynomial ℂ) : ExponentialBound (lift a u) := by
  exact (bound_exp a).mul (bound_poly_comp u (by simpa using bound_exp 1))

theorem ExponentialBound.finiteOrder {f : ℂ → ℂ} (hf : ExponentialBound f) :
    CRGOrder.FiniteOrder f := by
  obtain ⟨A, B, hA, _, hf⟩ := hf
  refine ⟨1, zero_le_one, CRGOrder.upperOrder_of_finiteType (C := A+B) (R := 1) ?_⟩
  intro z hz
  rw [Real.rpow_one]
  calc
    ‖f z‖ ≤ A * Real.exp (B*‖z‖) := hf z
    _ ≤ Real.exp A * Real.exp (B*‖z‖) :=
      mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp A]) (Real.exp_pos _).le
    _ = Real.exp (A+B*‖z‖) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((A+B)*‖z‖) := by apply Real.exp_le_exp.mpr; nlinarith

/-- Corollary 3.4, in a stronger form allowing a zero exponent. The polynomial
identity is the paper's sufficient condition, with the leading coefficient
included as P n. The conclusion includes entirety, nontriviality and finite order. -/
theorem corollary_3_4 {n : ℕ} (P : Fin (n+1) → Polynomial ℂ) (a c : ℂ)
    (hc : c ≠ 0) (h : ∑ j, P j * C (a^j.val) = 0) :
    Solves P (fun z => c * Complex.exp (a*z)) ∧
    Differentiable ℂ (fun z => c * Complex.exp (a*z)) ∧
    CRGOrder.FiniteOrder (fun z => c * Complex.exp (a*z)) ∧
    (fun z => c * Complex.exp (a*z)) ≠ 0 := by
  refine ⟨pure_exponential_solves P a c h, ?_,
    ((bound_const c).mul (bound_exp a)).finiteOrder, ?_⟩
  · have he := lift_entire a (C c)
    have hh : lift a (C c) = (fun z => c * Complex.exp (a*z)) := by
      funext z; simp [lift, mul_comm]
    rwa [hh] at he
  · intro he
    have hz := congrFun he 0
    simp at hz
    exact hc hz

/-- Exponential sums in the terminology of the paper allow polynomial
multipliers in z. The frequencies are linear, not arbitrary polynomials. -/
def IsExponentialSum (f : ℂ → ℂ) : Prop :=
  ∃ N : ℕ, ∃ p : Fin N → Polynomial ℂ, ∃ a : Fin N → ℂ,
    ∀ z, f z = ∑ j, (p j).eval z * Complex.exp (a j * z)

theorem bound_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ)
    (h : ∀ j ∈ s, ExponentialBound (f j)) : ExponentialBound (fun z => ∑ j ∈ s, f j z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using bound_const 0
  | @insert j s hj ih =>
    simpa only [Finset.sum_insert hj] using
      (h j (Finset.mem_insert_self _ _)).add (ih (fun k hk => h k (Finset.mem_insert_of_mem hk)))

theorem IsExponentialSum.finiteOrder {f : ℂ → ℂ} (h : IsExponentialSum f) :
    CRGOrder.FiniteOrder f := by
  obtain ⟨N, p, a, hf⟩ := h
  have he : f = (fun z => ∑ j, (p j).eval z * Complex.exp (a j*z)) := funext hf
  rw [he]
  exact (bound_sum Finset.univ _ (fun j _ =>
    (bound_poly_comp (p j) bound_id).mul (bound_exp (a j)))).finiteOrder

#print axioms bound_const
#print axioms bound_id
#print axioms bound_exp
#print axioms ExponentialBound.add
#print axioms ExponentialBound.mul
#print axioms ExponentialBound.pow
#print axioms bound_poly_comp
#print axioms bound_lift
#print axioms ExponentialBound.finiteOrder
#print axioms corollary_3_4
#print axioms bound_sum
#print axioms IsExponentialSum.finiteOrder
end LiWangWen
