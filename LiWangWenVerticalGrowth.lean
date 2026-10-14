import LiWangWenFiniteOrderFloquet

/-!
# Vertical growth from finite-order periodic Floquet blocks

This estimate uses only the general Floquet decomposition, with entire
periodic coefficients of finite order. It uses neither Fourier support nor
the exponential-sum classification. Imaginary translation into one period
strip makes the periodic factors independent of the height variable.
-/

noncomputable section
open Polynomial
open scoped BigOperators

namespace LiWangWen

/-- A polynomial exponential bound horizontally, and exponential type vertically. -/
def VerticalPowerBound (f : ℂ → ℂ) : Prop :=
  ∃ k : ℕ, ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
    ∀ z, ‖f z‖ ≤ Real.exp (A*(1+|z.re|)^k+B*|z.im|)

/-- Periodicity removes the imaginary coordinate from a finite-order bound. -/
theorem periodic_power_bound_horizontal {p : ℂ → ℂ}
    (hp : PowerExponentialBound p) (hper : Function.Periodic p exponentialPeriod) :
    ∃ k : ℕ, ∃ A : ℝ, 0 ≤ A ∧
      ∀ z, ‖p z‖ ≤ Real.exp (A*(1+|z.re|)^k) := by
  obtain ⟨k,A,hA,hbound⟩ := hp
  let T : ℝ := 2*Real.pi
  have hT : 0 < T := mul_pos (by norm_num) Real.pi_pos
  refine ⟨k,A*(1+T)^k,by positivity,fun z => ?_⟩
  let n : ℤ := ⌊z.im/T⌋
  let w : ℂ := z-(n:ℂ)*exponentialPeriod
  have hwre : w.re = z.re := by simp [w,exponentialPeriod]
  have hwim : w.im = z.im-(n:ℝ)*T := by
    simp [w,exponentialPeriod,T]
  have hlo : (n:ℝ)*T ≤ z.im := by
    have h := Int.floor_le (z.im/T)
    exact (le_div_iff₀ hT).mp h
  have hhi : z.im < ((n:ℝ)+1)*T := by
    have h := Int.lt_floor_add_one (z.im/T)
    exact (div_lt_iff₀ hT).mp h
  have hwi0 : 0 ≤ w.im := by rw [hwim]; linarith
  have hwiT : w.im ≤ T := by rw [hwim]; linarith
  have hwnorm : ‖w‖ ≤ |z.re|+T := by
    apply (Complex.norm_le_abs_re_add_abs_im w).trans
    rw [hwre,abs_of_nonneg hwi0]
    linarith
  have hbase : 1+‖w‖ ≤ (1+T)*(1+|z.re|) := by
    nlinarith [abs_nonneg z.re]
  have hpw : p w = p z := hper.sub_int_mul_eq n
  rw [← hpw]
  apply (hbound w).trans
  apply Real.exp_le_exp.mpr
  calc
    A*(1+‖w‖)^k ≤ A*((1+T)*(1+|z.re|))^k :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbase k) hA
    _ = (A*(1+T)^k)*(1+|z.re|)^k := by rw [mul_pow]; ring

/-- A periodic finite-order entire function has no height dependence in its
horizontal growth bound. -/
theorem periodic_finiteOrder_verticalPowerBound {p : ℂ → ℂ}
    (hp : Differentiable ℂ p) (hfo : CRGOrder.FiniteOrder p)
    (hper : Function.Periodic p exponentialPeriod) : VerticalPowerBound p := by
  obtain ⟨k,A,hA,hbound⟩ := periodic_power_bound_horizontal
    (power_bound_of_finiteOrder hp hfo) hper
  exact ⟨k,A,0,hA,le_rfl,by simpa only [zero_mul,add_zero] using hbound⟩

/-- Exponential-type functions satisfy the separate-coordinate estimate. -/
theorem ExponentialBound.verticalPowerBound {f : ℂ → ℂ} (hf : ExponentialBound f) :
    VerticalPowerBound f := by
  obtain ⟨A,B,hA,hB,hbound⟩ := hf
  refine ⟨1,A+B,B,add_nonneg hA hB,hB,fun z => ?_⟩
  calc
    ‖f z‖ ≤ A*Real.exp (B*‖z‖) := hbound z
    _ ≤ Real.exp A*Real.exp (B*‖z‖) :=
      mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp A]) (Real.exp_pos _).le
    _ = Real.exp (A+B*‖z‖) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((A+B)*(1+|z.re|)^1+B*|z.im|) := by
      apply Real.exp_le_exp.mpr
      have hn := mul_le_mul_of_nonneg_left (Complex.norm_le_abs_re_add_abs_im z) hB
      simp only [pow_one]
      nlinarith [abs_nonneg z.re]

theorem VerticalPowerBound.raise {f : ℂ → ℂ} {k l : ℕ} {A B : ℝ}
    (hA : 0 ≤ A) (hkl : k ≤ l)
    (hf : ∀ z, ‖f z‖ ≤ Real.exp (A*(1+|z.re|)^k+B*|z.im|)) :
    ∀ z, ‖f z‖ ≤ Real.exp (A*(1+|z.re|)^l+B*|z.im|) := by
  intro z
  apply (hf z).trans
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ (by linarith [abs_nonneg z.re] : 1 ≤ 1+|z.re|) hkl) hA
  linarith

theorem VerticalPowerBound.mul {f g : ℂ → ℂ}
    (hf : VerticalPowerBound f) (hg : VerticalPowerBound g) :
    VerticalPowerBound (fun z => f z*g z) := by
  obtain ⟨k,A,B,hA,hB,hf⟩ := hf
  obtain ⟨l,C,D,hC,hD,hg⟩ := hg
  have hf' := VerticalPowerBound.raise hA (Nat.le_max_left k l) hf
  have hg' := VerticalPowerBound.raise hC (Nat.le_max_right k l) hg
  refine ⟨max k l,A+C,B+D,add_nonneg hA hC,add_nonneg hB hD,fun z => ?_⟩
  calc
    ‖f z*g z‖ ≤ Real.exp (A*(1+|z.re|)^(max k l)+B*|z.im|)*
        Real.exp (C*(1+|z.re|)^(max k l)+D*|z.im|) := by
      rw [norm_mul]
      exact mul_le_mul (hf' z) (hg' z) (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem VerticalPowerBound.add {f g : ℂ → ℂ}
    (hf : VerticalPowerBound f) (hg : VerticalPowerBound g) :
    VerticalPowerBound (fun z => f z+g z) := by
  obtain ⟨k,A,B,hA,hB,hf⟩ := hf
  obtain ⟨l,C,D,hC,hD,hg⟩ := hg
  have hf' := VerticalPowerBound.raise hA (Nat.le_max_left k l) hf
  have hg' := VerticalPowerBound.raise hC (Nat.le_max_right k l) hg
  refine ⟨max k l,A+C+1,B+D,by positivity,add_nonneg hB hD,fun z => ?_⟩
  let t := (1+|z.re|)^(max k l)
  let u := |z.im|
  have ht : 1 ≤ t := one_le_pow₀ (by linarith [abs_nonneg z.re])
  have hu : 0 ≤ u := abs_nonneg _
  have hf'' : ‖f z‖ ≤ Real.exp ((A+C)*t+(B+D)*u) := (hf' z).trans
    (Real.exp_le_exp.mpr (by dsimp only [t,u]; nlinarith))
  have hg'' : ‖g z‖ ≤ Real.exp ((A+C)*t+(B+D)*u) := (hg' z).trans
    (Real.exp_le_exp.mpr (by dsimp only [t,u]; nlinarith))
  calc
    ‖f z+g z‖ ≤ ‖f z‖+‖g z‖ := norm_add_le _ _
    _ ≤ 2*Real.exp ((A+C)*t+(B+D)*u) := by linarith
    _ ≤ Real.exp t*Real.exp ((A+C)*t+(B+D)*u) :=
      mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp t]) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; dsimp only [t,u]; ring

theorem verticalPowerBound_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ)
    (h : ∀ i ∈ s, VerticalPowerBound (f i)) : VerticalPowerBound (fun z => ∑ i ∈ s, f i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (bound_const 0).verticalPowerBound
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using
      (h i (Finset.mem_insert_self _ _)).add (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

theorem verticalPowerBound_list_sum {ι : Type*} (s : List ι) (f : ι → ℂ → ℂ)
    (h : ∀ i ∈ s, VerticalPowerBound (f i)) :
    VerticalPowerBound (fun z => (s.map (fun i => f i z)).sum) := by
  induction s with
  | nil => simpa using (bound_const 0).verticalPowerBound
  | cons i s ih =>
    simpa only [List.map_cons,List.sum_cons] using
      (h i List.mem_cons_self).add (ih (fun j hj => h j (List.mem_cons_of_mem i hj)))

/-- Generalized Floquet blocks satisfy the vertical estimate before any
classification of their periodic factors as finite Fourier sums. -/
theorem finiteOrderFloquetBlock_verticalPowerBound
    (b : FiniteOrderFloquetBlock exponentialPeriod) : VerticalPowerBound b.eval := by
  apply VerticalPowerBound.mul (bound_exp b.exponent).verticalPowerBound
  apply verticalPowerBound_finset_sum
  intro j hj
  have hreg := b.regular j (Finset.mem_range.mp hj)
  have hpoly : VerticalPowerBound (fun z : ℂ => z^j) := by
    simpa only [eval_pow,eval_X] using
      (bound_poly_comp (X^j) bound_id).verticalPowerBound
  exact hpoly.mul (periodic_finiteOrder_verticalPowerBound hreg.1 hreg.2.2 hreg.2.1)

/-- Finite-order entire solutions have at most exponential vertical growth,
with a finite power remaining in the horizontal coordinate. This theorem
uses generic periodic Floquet blocks and no exponential-sum classification. -/
theorem finiteOrder_solution_verticalPowerBound {n : ℕ}
    {P : Fin (n+1) → Polynomial ℂ} (hlead : (P (Fin.last n)).eval 1 ≠ 0)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hfo : CRGOrder.FiniteOrder f)
    (hsol : Solves P f) : VerticalPowerBound f := by
  obtain ⟨bs,_,hrep⟩ := polynomial_exp_finiteOrder_floquet_blocks hlead hf hfo hsol
  have heq : f = (fun z => (bs.map (fun b => b.eval z)).sum) := funext hrep
  rw [heq]
  exact verticalPowerBound_list_sum bs FiniteOrderFloquetBlock.eval
    (fun b _ => finiteOrderFloquetBlock_verticalPowerBound b)

/-- Every fixed power of a logarithmic strip width is eventually dominated
by the radius, with an arbitrary fixed nonnegative multiplier. -/
theorem eventually_logarithmic_power_le_radius (k : ℕ) {A C : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) :
    ∀ᶠ r : ℝ in Filter.atTop,
      A*(1+C*(1+Real.log r))^k ≤ r := by
  let L := A*(1+2*C)^k
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hsmall := ((isLittleO_log_rpow_rpow_atTop (k : ℝ) (by norm_num : (0 : ℝ) < 1)).const_mul_left L).bound
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hsmall, Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop 1),
    Filter.eventually_ge_atTop (1 : ℝ)] with r hr hlog hr1
  have hlog0 : 0 ≤ Real.log r := by linarith
  have hlnonneg : 0 ≤ L*(Real.log r)^k := by positivity
  simp only [Real.rpow_natCast,Real.rpow_one,one_mul] at hr
  rw [Real.norm_of_nonneg hlnonneg, Real.norm_of_nonneg (zero_le_one.trans hr1)] at hr
  have hbase : 1+C*(1+Real.log r) ≤ (1+2*C)*Real.log r := by nlinarith
  calc
    A*(1+C*(1+Real.log r))^k ≤ A*((1+2*C)*Real.log r)^k :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbase k) hA
    _ = L*(Real.log r)^k := by rw [mul_pow]; dsimp only [L]; ring
    _ ≤ r := hr

/-- The vertical bound becomes exponential type at every point lying in a
fixed logarithmic strip and a disk of the indicated radius. -/
theorem VerticalPowerBound.logarithmic_strip {f : ℂ → ℂ}
    (hf : VerticalPowerBound f) {C : ℝ} (hC : 0 ≤ C) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ r : ℝ in Filter.atTop, ∀ z : ℂ,
      ‖z‖ ≤ r → |z.re| ≤ C*(1+Real.log r) → ‖f z‖ ≤ Real.exp (D*r) := by
  obtain ⟨k,A,B,hA,hB,hbound⟩ := hf
  refine ⟨1+B,by positivity,?_⟩
  filter_upwards [eventually_logarithmic_power_le_radius k hA hC] with r hr
  intro z hzr hx
  have hpow : A*(1+|z.re|)^k ≤ r := by
    apply le_trans _ hr
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by linarith) k) hA
  have hy : B*|z.im| ≤ B*r :=
    mul_le_mul_of_nonneg_left ((Complex.abs_im_le_norm z).trans hzr) hB
  apply (hbound z).trans
  apply Real.exp_le_exp.mpr
  nlinarith

#print axioms periodic_power_bound_horizontal
#print axioms periodic_finiteOrder_verticalPowerBound
#print axioms ExponentialBound.verticalPowerBound
#print axioms VerticalPowerBound.raise
#print axioms VerticalPowerBound.mul
#print axioms VerticalPowerBound.add
#print axioms verticalPowerBound_finset_sum
#print axioms verticalPowerBound_list_sum
#print axioms finiteOrderFloquetBlock_verticalPowerBound
#print axioms finiteOrder_solution_verticalPowerBound
#print axioms eventually_logarithmic_power_le_radius
#print axioms VerticalPowerBound.logarithmic_strip

end LiWangWen
