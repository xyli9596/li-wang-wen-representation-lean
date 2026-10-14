import LiWangWenDifferenceGrowth

/-!
# Global power-exponential bounds for finite-order entire functions

These bounds and their closure properties use the actual definition of finite
order. In particular, translation and finite algebraic extraction preserve
finite order without assuming exponential type.
-/

noncomputable section
open Filter Set
open scoped Topology

namespace LiWangWen

/-- A convenient global form of a finite-order upper bound. -/
def PowerExponentialBound (f : ℂ → ℂ) : Prop :=
  ∃ k : ℕ, ∃ A : ℝ, 0 ≤ A ∧ ∀ z, ‖f z‖ ≤ Real.exp (A*(1+‖z‖)^k)

/-- Finite order and continuity on compact disks supply a global bound. -/
theorem power_bound_of_finiteOrder {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hfo : CRGOrder.FiniteOrder f) :
    ∃ k : ℕ, ∃ A : ℝ, 0 ≤ A ∧ ∀ z, ‖f z‖ ≤ Real.exp (A*(1+‖z‖)^k) := by
  obtain ⟨ρ, _, hρ⟩ := hfo
  obtain ⟨R, hR⟩ := hρ 1 zero_lt_one
  obtain ⟨k, hk⟩ := exists_nat_ge (ρ+1)
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) (max R 1)).exists_bound_of_continuousOn
    hf.continuous.continuousOn
  let A := max 1 M
  have hA : 0 ≤ A := zero_le_one.trans (le_max_left _ _)
  refine ⟨k, A, hA, fun z => ?_⟩
  have ht : 1 ≤ 1+‖z‖ := by linarith [norm_nonneg z]
  have hp : 1 ≤ (1+‖z‖)^k := one_le_pow₀ ht
  by_cases hz : max R 1 ≤ ‖z‖
  · calc
      ‖f z‖ ≤ Real.exp (‖z‖^(ρ+1)) := hR z ((le_max_left _ _).trans hz)
      _ ≤ Real.exp (‖z‖^k) := by
        apply Real.exp_le_exp.mpr
        simpa only [Real.rpow_natCast] using
          Real.rpow_le_rpow_of_exponent_le ((le_max_right _ _).trans hz) hk
      _ ≤ Real.exp (A*(1+‖z‖)^k) := by
        apply Real.exp_le_exp.mpr
        have hb : ‖z‖^k ≤ (1+‖z‖)^k := pow_le_pow_left₀ (norm_nonneg z) (by linarith) k
        exact hb.trans (le_mul_of_one_le_left (by positivity) (le_max_left _ _))
  · have hbound : ‖f z‖ ≤ M := hM z (by
      simpa only [Metric.mem_closedBall, dist_zero_right] using (le_of_not_ge hz))
    calc
      ‖f z‖ ≤ M := hbound
      _ ≤ A := le_max_right _ _
      _ ≤ Real.exp A := by linarith [Real.add_one_le_exp A]
      _ ≤ Real.exp (A*(1+‖z‖)^k) := Real.exp_le_exp.mpr
        (le_mul_of_one_le_right hA hp)

/-- Conversely a global power-exponential bound implies finite order. -/
theorem PowerExponentialBound.finiteOrder {f : ℂ → ℂ} (hf : PowerExponentialBound f) :
    CRGOrder.FiniteOrder f := by
  obtain ⟨k, A, hA, hbound⟩ := hf
  refine ⟨k, by positivity, CRGOrder.upperOrder_of_finiteType
    (C := A*2^k) (R := 1) (fun z hz => ?_)⟩
  apply (hbound z).trans
  apply Real.exp_le_exp.mpr
  rw [Real.rpow_natCast]
  have hb : (1+‖z‖)^k ≤ (2*‖z‖)^k :=
    pow_le_pow_left₀ (by positivity) (by linarith) k
  calc
    A*(1+‖z‖)^k ≤ A*(2*‖z‖)^k := mul_le_mul_of_nonneg_left hb hA
    _ = (A*2^k)*‖z‖^k := by rw [mul_pow]; ring

/-- Increasing the integer exponent preserves a global bound. -/
theorem PowerExponentialBound.raise {f : ℂ → ℂ} {k l : ℕ} {A : ℝ}
    (hA : 0 ≤ A) (hkl : k ≤ l)
    (hf : ∀ z, ‖f z‖ ≤ Real.exp (A*(1+‖z‖)^k)) :
    ∀ z, ‖f z‖ ≤ Real.exp (A*(1+‖z‖)^l) := by
  intro z
  apply (hf z).trans
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ (by linarith [norm_nonneg z] : 1 ≤ 1+‖z‖) hkl) hA)

theorem power_bound_const (c : ℂ) : PowerExponentialBound (fun _ => c) := by
  refine ⟨0, ‖c‖, norm_nonneg _, fun z => ?_⟩
  simp only [pow_zero, mul_one]
  linarith [Real.add_one_le_exp ‖c‖]

theorem power_bound_id : PowerExponentialBound (fun z : ℂ => z) := by
  refine ⟨1, 1, zero_le_one, fun z => ?_⟩
  simp only [pow_one, one_mul]
  linarith [Real.add_one_le_exp (1+‖z‖)]

theorem power_bound_exp (a : ℂ) : PowerExponentialBound (fun z => Complex.exp (a*z)) := by
  refine ⟨1, ‖a‖, norm_nonneg _, fun z => ?_⟩
  apply (Complex.norm_exp_le_exp_norm _).trans
  simp only [norm_mul, pow_one]
  apply Real.exp_le_exp.mpr
  nlinarith [norm_nonneg a]

theorem PowerExponentialBound.mul {f g : ℂ → ℂ}
    (hf : PowerExponentialBound f) (hg : PowerExponentialBound g) :
    PowerExponentialBound (fun z => f z*g z) := by
  obtain ⟨k, A, hA, hf⟩ := hf
  obtain ⟨l, B, hB, hg⟩ := hg
  have hf' := PowerExponentialBound.raise hA (Nat.le_max_left k l) hf
  have hg' := PowerExponentialBound.raise hB (Nat.le_max_right k l) hg
  refine ⟨max k l, A+B, add_nonneg hA hB, fun z => ?_⟩
  rw [norm_mul, add_mul, Real.exp_add]
  exact mul_le_mul (hf' z) (hg' z) (norm_nonneg _) (Real.exp_pos _).le

theorem PowerExponentialBound.add {f g : ℂ → ℂ}
    (hf : PowerExponentialBound f) (hg : PowerExponentialBound g) :
    PowerExponentialBound (fun z => f z+g z) := by
  obtain ⟨k, A, hA, hf⟩ := hf
  obtain ⟨l, B, hB, hg⟩ := hg
  have hf' := PowerExponentialBound.raise hA (Nat.le_max_left k l) hf
  have hg' := PowerExponentialBound.raise hB (Nat.le_max_right k l) hg
  refine ⟨max k l, A+B+1, by positivity, fun z => ?_⟩
  let t := (1+‖z‖)^(max k l)
  have ht : 1 ≤ t := one_le_pow₀ (by linarith [norm_nonneg z])
  have htpos : 0 ≤ t := zero_le_one.trans ht
  have hf'' : ‖f z‖ ≤ Real.exp ((A+B)*t) := (hf' z).trans
    (Real.exp_le_exp.mpr (by dsimp only [t]; nlinarith))
  have hg'' : ‖g z‖ ≤ Real.exp ((A+B)*t) := (hg' z).trans
    (Real.exp_le_exp.mpr (by dsimp only [t]; nlinarith))
  calc
    ‖f z+g z‖ ≤ ‖f z‖+‖g z‖ := norm_add_le _ _
    _ ≤ 2*Real.exp ((A+B)*t) := by linarith
    _ ≤ Real.exp t * Real.exp ((A+B)*t) :=
      mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp t]) (Real.exp_pos _).le
    _ = Real.exp ((A+B+1)*t) := by rw [← Real.exp_add]; congr 1; ring

theorem PowerExponentialBound.neg {f : ℂ → ℂ} (hf : PowerExponentialBound f) :
    PowerExponentialBound (fun z => -f z) := by
  obtain ⟨k, A, hA, hf⟩ := hf
  exact ⟨k, A, hA, by simpa only [norm_neg] using hf⟩

theorem PowerExponentialBound.sub {f g : ℂ → ℂ}
    (hf : PowerExponentialBound f) (hg : PowerExponentialBound g) :
    PowerExponentialBound (fun z => f z-g z) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem PowerExponentialBound.translate {f : ℂ → ℂ}
    (hf : PowerExponentialBound f) (h : ℂ) : PowerExponentialBound (fun z => f (z+h)) := by
  obtain ⟨k, A, hA, hf⟩ := hf
  refine ⟨k, A*(1+‖h‖)^k, by positivity, fun z => ?_⟩
  apply (hf (z+h)).trans
  apply Real.exp_le_exp.mpr
  have hz : 1+‖z+h‖ ≤ (1+‖h‖)*(1+‖z‖) := by
    have := norm_add_le z h
    nlinarith [norm_nonneg z, norm_nonneg h]
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1+‖z+h‖) hz k
  calc
    A*(1+‖z+h‖)^k ≤ A*((1+‖h‖)*(1+‖z‖))^k := mul_le_mul_of_nonneg_left hp hA
    _ = _ := by rw [mul_pow]; ring

theorem PowerExponentialBound.const_mul {f : ℂ → ℂ}
    (hf : PowerExponentialBound f) (c : ℂ) : PowerExponentialBound (fun z => c*f z) :=
  (power_bound_const c).mul hf

theorem PowerExponentialBound.pow {f : ℂ → ℂ} (hf : PowerExponentialBound f) (k : ℕ) :
    PowerExponentialBound (fun z => f z^k) := by
  induction k with
  | zero => simpa using power_bound_const 1
  | succ k ih => simpa only [pow_succ] using ih.mul hf

theorem power_bound_poly_comp (p : Polynomial ℂ) {f : ℂ → ℂ}
    (hf : PowerExponentialBound f) : PowerExponentialBound (fun z => p.eval (f z)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval_add] using hp.add hq
  | monomial k c => simpa only [Polynomial.eval_monomial] using
      (power_bound_const c).mul (hf.pow k)

theorem power_bound_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ)
    (h : ∀ j ∈ s, PowerExponentialBound (f j)) :
    PowerExponentialBound (fun z => ∑ j ∈ s, f j z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using power_bound_const 0
  | @insert j s hj ih =>
    simpa only [Finset.sum_insert hj] using
      (h j (Finset.mem_insert_self _ _)).add (ih (fun k hk => h k (Finset.mem_insert_of_mem hk)))

theorem PowerExponentialBound.difference {f : ℂ → ℂ}
    (hf : PowerExponentialBound f) (h : ℂ) : PowerExponentialBound (IncePeriodic.difference h f) :=
  (hf.translate h).sub hf

theorem PowerExponentialBound.remove_exponential {f : ℂ → ℂ}
    (hf : PowerExponentialBound f) (a : ℂ) :
    PowerExponentialBound (fun z => Complex.exp (-a*z)*f z) := (power_bound_exp (-a)).mul hf

#print axioms power_bound_of_finiteOrder
#print axioms PowerExponentialBound.finiteOrder
#print axioms PowerExponentialBound.raise
#print axioms power_bound_const
#print axioms power_bound_id
#print axioms power_bound_exp
#print axioms PowerExponentialBound.mul
#print axioms PowerExponentialBound.add
#print axioms PowerExponentialBound.neg
#print axioms PowerExponentialBound.sub
#print axioms PowerExponentialBound.translate
#print axioms PowerExponentialBound.const_mul
#print axioms PowerExponentialBound.pow
#print axioms power_bound_poly_comp
#print axioms power_bound_sum
#print axioms PowerExponentialBound.difference
#print axioms PowerExponentialBound.remove_exponential

end LiWangWen
