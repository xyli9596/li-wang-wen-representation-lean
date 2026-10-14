import WimanValironCircleBounds
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# From centered moments to higher derivative asymptotics

The centered falling-factorial polynomial packages the finite algebraic
change from powers of the centered index to derivatives. No exceptional-set
or moment-concentration assertion is assumed to have been proved here.
-/

set_option autoImplicit false
noncomputable section
open Filter Polynomial
open scoped Topology

namespace WimanValiron

/-- `P_j(t,X) = ∏_{k<j} (X + 1 - k*t)`. -/
def centeredFallingPolynomial (t : ℂ) : ℕ → Polynomial ℂ
  | 0 => 1
  | j + 1 => X * centeredFallingPolynomial t j +
      C (1 - (j : ℂ) * t) * centeredFallingPolynomial t j

theorem centeredFallingPolynomial_coeff_continuous (j k : ℕ) :
    Continuous (fun t => (centeredFallingPolynomial t j).coeff k) := by
  induction j generalizing k with
  | zero => simp only [centeredFallingPolynomial]; exact continuous_const
  | succ j ih =>
    cases k with
    | zero =>
      simp only [centeredFallingPolynomial, coeff_add, coeff_X_mul_zero, coeff_C_mul, zero_add]
      exact (continuous_const.sub (continuous_const.mul continuous_id)).mul (ih 0)
    | succ k =>
      simp only [centeredFallingPolynomial, coeff_add, coeff_X_mul, coeff_C_mul]
      exact (ih k).add ((continuous_const.sub (continuous_const.mul continuous_id)).mul (ih (k+1)))

theorem centeredFallingPolynomial_natDegree_le (t : ℂ) (j : ℕ) :
    (centeredFallingPolynomial t j).natDegree ≤ j := by
  induction j with
  | zero => simp [centeredFallingPolynomial]
  | succ j ih =>
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    cases k with
    | zero => omega
    | succ k =>
      simp only [centeredFallingPolynomial, coeff_add, coeff_X_mul, coeff_C_mul]
      rw [coeff_eq_zero_of_natDegree_lt (by omega : (centeredFallingPolynomial t j).natDegree < k),
        coeff_eq_zero_of_natDegree_lt (by omega : (centeredFallingPolynomial t j).natDegree < k+1)]
      ring

theorem centeredFallingPolynomial_zero_constant (j : ℕ) :
    (centeredFallingPolynomial 0 j).coeff 0 = 1 := by
  induction j with
  | zero => simp [centeredFallingPolynomial]
  | succ j ih => simp [centeredFallingPolynomial, ih]

theorem centeredFallingPolynomial_eval {v : ℂ} (hv : v ≠ 0) (j : ℕ) (x : ℂ) :
    (centeredFallingPolynomial v⁻¹ j).eval x =
      (descPochhammer ℂ j).eval (v * (x + 1)) / v ^ j := by
  induction j with
  | zero => simp [centeredFallingPolynomial]
  | succ j ih =>
    simp only [centeredFallingPolynomial, eval_add, eval_mul, eval_X, eval_C, ih,
      descPochhammer_succ_eval, pow_succ]
    field_simp
    ring

theorem centeredFallingPolynomial_eval_index {v : ℂ} (hv : v ≠ 0) (j n : ℕ) :
    (centeredFallingPolynomial v⁻¹ j).eval (((n : ℂ) - v) / v) =
      (n.descFactorial j : ℂ) / v ^ j := by
  rw [centeredFallingPolynomial_eval hv]
  have heq : v * (((n : ℂ) - v) / v + 1) = n := by field_simp; ring
  rw [heq, descPochhammer_eval_eq_descFactorial]

/-- The signed moment of a weighted sequence about the normalized center `v`. -/
def centeredMoment (w : ℕ → ℂ) (v : ℂ) (k : ℕ) : ℂ :=
  ∑' n : ℕ, (((n : ℂ) - v) / v) ^ k * w n

theorem falling_average_eq_centered_moments {w : ℕ → ℂ} {v : ℂ} (hv : v ≠ 0)
    (j : ℕ) (hs : ∀ k ≤ j, Summable (fun n : ℕ => (((n : ℂ) - v) / v) ^ k * w n)) :
    (∑' n, ((n.descFactorial j : ℂ) / v ^ j) * w n) =
      ∑ k ∈ Finset.range (j + 1), (centeredFallingPolynomial v⁻¹ j).coeff k *
        centeredMoment w v k := by
  have hsum := hasSum_sum (s := Finset.range (j+1)) (fun k hk =>
    ((hs k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))).hasSum.mul_left
      ((centeredFallingPolynomial v⁻¹ j).coeff k)))
  have heval : ∀ n : ℕ,
      (∑ k ∈ Finset.range (j+1), (centeredFallingPolynomial v⁻¹ j).coeff k *
        ((((n : ℂ) - v) / v) ^ k * w n)) =
        ((n.descFactorial j : ℂ) / v ^ j) * w n := by
    intro n
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul,
      ← eval_eq_sum_range' (Nat.lt_succ_of_le (centeredFallingPolynomial_natDegree_le _ _)),
      centeredFallingPolynomial_eval_index hv]
  simpa only [heval, centeredMoment] using hsum.tsum_eq

/-- A coefficient-continuity argument converts centered moment limits to falling-factorial limits. -/
theorem falling_average_tendsto_one_of_centered_moments
    {α : Type*} {l : Filter α} {w : α → ℕ → ℂ} {v : α → ℂ}
    (hv : ∀ᶠ x in l, v x ≠ 0) (hinv : Tendsto (fun x => (v x)⁻¹) l (𝓝 0))
    (hs : ∀ x k, Summable (fun n : ℕ => (((n : ℂ) - v x) / v x) ^ k * w x n))
    (hm0 : Tendsto (fun x => centeredMoment (w x) (v x) 0) l (𝓝 1))
    (hm : ∀ k > 0, Tendsto (fun x => centeredMoment (w x) (v x) k) l (𝓝 0))
    (j : ℕ) :
    Tendsto (fun x => ∑' n, ((n.descFactorial j : ℂ) / v x ^ j) * w x n) l (𝓝 1) := by
  have hlim : ∀ k, Tendsto
      (fun x => (centeredFallingPolynomial (v x)⁻¹ j).coeff k * centeredMoment (w x) (v x) k) l
      (𝓝 (if k = 0 then (centeredFallingPolynomial 0 j).coeff 0 else 0)) := by
    intro k
    have hc := ((centeredFallingPolynomial_coeff_continuous j k).tendsto 0).comp hinv
    by_cases hk : k = 0
    · subst k
      simpa only [Function.comp_apply, ite_true, mul_one] using hc.mul hm0
    · simpa only [Function.comp_apply, hk, ite_false, mul_zero] using hc.mul (hm k (Nat.pos_of_ne_zero hk))
  have hsum := tendsto_finsetSum (Finset.range (j+1)) (fun k _ => hlim k)
  have hsum' : Tendsto (fun x => ∑ k ∈ Finset.range (j+1),
      (centeredFallingPolynomial (v x)⁻¹ j).coeff k * centeredMoment (w x) (v x) k) l (𝓝 1) := by
    simpa only [Finset.sum_ite_eq', Finset.mem_range, Nat.zero_lt_succ, ite_true,
      centeredFallingPolynomial_zero_constant] using hsum
  apply hsum'.congr'
  exact hv.mono fun x hx => (falling_average_eq_centered_moments hx j (fun k _ => hs x k)).symm

theorem summable_nat_pow_taylorCoeff {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hne : f ≠ 0) (z : ℂ) (k : ℕ) :
    Summable (fun n : ℕ => (n : ℂ) ^ k * taylorCoeff f n * z ^ n) := by
  let s : ℝ := ‖z‖ + 1
  have hs : 0 < s := by dsimp [s]; positivity
  have hzs : ‖z‖ < s := by dsimp [s]; linarith
  have hq0 : 0 ≤ ‖z‖ / s := div_nonneg (norm_nonneg _) hs.le
  have hq1 : ‖‖z‖ / s‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]
    exact (div_lt_one hs).mpr hzs
  have hgeom := (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) k hq1).mul_left
    (maximumTerm (taylorCoeff f) s)
  apply hgeom.of_norm_bounded
  intro n
  have hb := norm_powerSeries_term_le_geometric (taylor_admissible hf hne hs) z n
  simp only [norm_mul, norm_pow] at hb
  simp only [norm_mul, norm_pow, Complex.norm_natCast]
  calc
    (n : ℝ) ^ k * ‖taylorCoeff f n‖ * ‖z‖ ^ n
        = (n : ℝ) ^ k * (‖taylorCoeff f n‖ * ‖z‖ ^ n) := by ring
    _ ≤ (n : ℝ) ^ k * (maximumTerm (taylorCoeff f) s * (‖z‖ / s) ^ n) := by
      exact mul_le_mul_of_nonneg_left hb (by positivity)
    _ = maximumTerm (taylorCoeff f) s * ((n : ℝ) ^ k * (‖z‖ / s) ^ n) := by ring

theorem summable_polynomial_taylorCoeff {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hne : f ≠ 0) (z : ℂ) (p : Polynomial ℂ) :
    Summable (fun n : ℕ => p.eval (n : ℂ) * taylorCoeff f n * z ^ n) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [eval_add, add_mul] using hp.add hq
  | monomial k c =>
    simpa only [eval_monomial, mul_assoc] using (summable_nat_pow_taylorCoeff hf hne z k).mul_left c

/-- The actual normalized Taylor weights of `f` at `z`. -/
def taylorWeight (f : ℂ → ℂ) (z : ℂ) (n : ℕ) : ℂ :=
  taylorCoeff f n * z ^ n / f z

theorem summable_centered_taylorWeight {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hne : f ≠ 0) (z v : ℂ) (k : ℕ) :
    Summable (fun n : ℕ => (((n : ℂ) - v) / v) ^ k * taylorWeight f z n) := by
  have hs := (summable_polynomial_taylorCoeff hf hne z
    (((X - C v) * C v⁻¹) ^ k)).mul_right (f z)⁻¹
  simpa only [eval_pow, eval_mul, eval_sub, eval_X, eval_C, taylorWeight,
    div_eq_mul_inv, mul_assoc] using hs

theorem centered_taylorWeight_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {z : ℂ} (hz : f z ≠ 0) (v : ℂ) : centeredMoment (taylorWeight f z) v 0 = 1 := by
  have hs := (hasSum_taylorCoeff hf z).div_const (f z)
  simpa only [centeredMoment, pow_zero, one_mul, taylorWeight, div_self hz] using hs.tsum_eq

theorem falling_taylorWeight_eq_normalized_deriv {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (j : ℕ) (z v : ℂ) :
    (∑' n, ((n.descFactorial j : ℂ) / v ^ j) * taylorWeight f z n) =
      z ^ j * iteratedDeriv j f z / (v ^ j * f z) := by
  have hs := (hasSum_pow_mul_iteratedDeriv hf j z).div_const (v ^ j * f z)
  have heq : (fun n => (n.descFactorial j : ℂ) * taylorCoeff f n * z ^ n / (v ^ j * f z)) =
      (fun n => ((n.descFactorial j : ℂ) / v ^ j) * taylorWeight f z n) := by
    funext n
    simp only [taylorWeight, div_eq_mul_inv, mul_inv_rev]
    ring
  rw [heq] at hs
  exact hs.tsum_eq

/-- Every fixed higher derivative has the Wiman--Valiron normalized limit once
all positive centered signed moments vanish. Summability is derived from entirety. -/
theorem normalized_deriv_tendsto_one_of_centered_moments
    {α : Type*} {l : Filter α} {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hne : f ≠ 0)
    {z v : α → ℂ} (hz : ∀ᶠ x in l, f (z x) ≠ 0) (hv : ∀ᶠ x in l, v x ≠ 0)
    (hinv : Tendsto (fun x => (v x)⁻¹) l (𝓝 0))
    (hm : ∀ k > 0, Tendsto (fun x => centeredMoment (taylorWeight f (z x)) (v x) k) l (𝓝 0))
    (j : ℕ) :
    Tendsto (fun x => z x ^ j * iteratedDeriv j f (z x) / (v x ^ j * f (z x))) l (𝓝 1) := by
  have hm0 : Tendsto (fun x => centeredMoment (taylorWeight f (z x)) (v x) 0) l (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    exact hz.mono fun x hx => (centered_taylorWeight_zero hf hx (v x)).symm
  have h := falling_average_tendsto_one_of_centered_moments hv hinv
    (fun x k => summable_centered_taylorWeight hf hne (z x) (v x) k)
    hm0 hm j
  simpa only [falling_taylorWeight_eq_normalized_deriv hf] using h

theorem inv_natIndex_tendsto_zero {α : Type*} {l : Filter α} {ν : α → ℕ}
    (hν : Tendsto ν l atTop) : Tendsto (fun x => (ν x : ℂ)⁻¹) l (𝓝 0) := by
  have hreal : Tendsto (fun x => (ν x : ℝ)) l atTop :=
    tendsto_natCast_atTop_atTop.comp hν
  have h := (tendsto_inv_atTop_zero.comp hreal).ofReal
  simpa only [Function.comp_apply, Complex.ofReal_inv, Complex.ofReal_natCast, Complex.ofReal_zero] using h

/-- The natural central-index version; indices need only become nonzero eventually. -/
theorem normalized_deriv_tendsto_one_of_nat_centered_moments
    {α : Type*} {l : Filter α} {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hne : f ≠ 0)
    {z : α → ℂ} {ν : α → ℕ} (hz : ∀ᶠ x in l, f (z x) ≠ 0)
    (hν : Tendsto ν l atTop)
    (hm : ∀ k > 0, Tendsto (fun x => centeredMoment (taylorWeight f (z x)) (ν x : ℂ) k)
      l (𝓝 0)) (j : ℕ) :
    Tendsto (fun x => z x ^ j * iteratedDeriv j f (z x) / ((ν x : ℂ) ^ j * f (z x)))
      l (𝓝 1) := by
  have hv : ∀ᶠ x in l, (ν x : ℂ) ≠ 0 := by
    filter_upwards [hν.eventually_ge_atTop 1] with x hx
    exact_mod_cast (Nat.ne_zero_of_lt hx)
  exact normalized_deriv_tendsto_one_of_centered_moments hf hne hz hv
    (inv_natIndex_tendsto_zero hν) hm j

#print axioms centeredFallingPolynomial_coeff_continuous
#print axioms centeredFallingPolynomial_natDegree_le
#print axioms centeredFallingPolynomial_zero_constant
#print axioms centeredFallingPolynomial_eval
#print axioms centeredFallingPolynomial_eval_index
#print axioms falling_average_eq_centered_moments
#print axioms falling_average_tendsto_one_of_centered_moments
#print axioms summable_nat_pow_taylorCoeff
#print axioms summable_polynomial_taylorCoeff
#print axioms summable_centered_taylorWeight
#print axioms centered_taylorWeight_zero
#print axioms falling_taylorWeight_eq_normalized_deriv
#print axioms normalized_deriv_tendsto_one_of_centered_moments
#print axioms inv_natIndex_tendsto_zero
#print axioms normalized_deriv_tendsto_one_of_nat_centered_moments

end WimanValiron
