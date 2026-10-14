import LiWangWenFourier
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Exact Fourier transforms of the differential equation

These identities use the actual contour coefficients, entire functions,
derivatives, and polynomial exponential coefficients.
-/

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory intervalIntegral Polynomial
open scoped Topology

namespace LiWangWen

theorem entire_deriv {p : ℂ → ℂ} (hp : Differentiable ℂ p) :
    Differentiable ℂ (deriv p) := fun z => (hp.analyticAt z).deriv.differentiableAt

theorem verticalFourierCoeff_zero (m : ℤ) : verticalFourierCoeff (fun _ => 0) m = 0 := by
  simp [verticalFourierCoeff, fourierWeight]

theorem verticalFourierCoeff_const_mul (c : ℂ) (p : ℂ → ℂ) (m : ℤ) :
    verticalFourierCoeff (fun z => c * p z) m = c * verticalFourierCoeff p m := by
  simp only [verticalFourierCoeff, fourierWeight]
  simp_rw [show ∀ z : ℂ, Complex.exp (-(m : ℂ)*z) * (c*p z) =
      c * (Complex.exp (-(m : ℂ)*z)*p z) from fun z => by ring]
  rw [intervalIntegral.integral_const_mul]
  ring

theorem fourierWeight_intervalIntegrable {p : ℂ → ℂ} (hp : Continuous p) (m : ℤ) :
    IntervalIntegrable (fun y : ℝ => fourierWeight p m ((y : ℂ)*I))
      volume 0 (2*Real.pi) := by
  apply Continuous.intervalIntegrable
  unfold fourierWeight
  fun_prop

theorem verticalFourierCoeff_add {p q : ℂ → ℂ} (hp : Continuous p) (hq : Continuous q) (m : ℤ) :
    verticalFourierCoeff (fun z => p z + q z) m =
      verticalFourierCoeff p m + verticalFourierCoeff q m := by
  unfold verticalFourierCoeff
  simp only [fourierWeight, mul_add]
  change _ * (∫ y : ℝ in 0..2*Real.pi,
      fourierWeight p m ((y : ℂ)*I) + fourierWeight q m ((y : ℂ)*I)) = _
  rw [intervalIntegral.integral_add (fourierWeight_intervalIntegrable hp m)
    (fourierWeight_intervalIntegrable hq m), mul_add]
  rfl

theorem verticalFourierCoeff_sub {p q : ℂ → ℂ} (hp : Continuous p) (hq : Continuous q) (m : ℤ) :
    verticalFourierCoeff (fun z => p z - q z) m =
      verticalFourierCoeff p m - verticalFourierCoeff q m := by
  have he : (fun z => p z - q z) = (fun z => p z + (-1)*q z) := by funext z; ring
  rw [he, verticalFourierCoeff_add hp (show Continuous (fun z => (-1 : ℂ)*q z) from
    continuous_const.mul hq), verticalFourierCoeff_const_mul]
  ring

theorem verticalFourierCoeff_sum {ι : Type*} (s : Finset ι) (p : ι → ℂ → ℂ)
    (hp : ∀ j ∈ s, Continuous (p j)) (m : ℤ) :
    verticalFourierCoeff (fun z => ∑ j ∈ s, p j z) m =
      ∑ j ∈ s, verticalFourierCoeff (p j) m := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using verticalFourierCoeff_zero m
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [verticalFourierCoeff_add (hp i (Finset.mem_insert_self _ _))
      (continuous_finsetSum _ (fun j hj => hp j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => hp j (Finset.mem_insert_of_mem hj))]

/-- The integral of the complex derivative of an entire periodic function
along one vertical period vanishes. -/
theorem vertical_integral_deriv_eq_zero {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hper : Function.Periodic g exponentialPeriod) :
    (∫ y : ℝ in 0..2*Real.pi, deriv g ((y : ℂ)*I)) = 0 := by
  have hd (y : ℝ) : HasDerivAt (fun t : ℝ => g ((t : ℂ)*I))
      (deriv g ((y : ℂ)*I) * I) y := by
    simpa only [one_mul, Function.comp_def, id_eq] using!
      ((hg ((y : ℂ)*I)).hasDerivAt.comp (y : ℂ)
        ((hasDerivAt_id (y : ℂ)).mul_const I)).comp_ofReal
  have hcont : Continuous (fun y : ℝ => deriv g ((y : ℂ)*I) * I) := by
    have hgd := (entire_deriv hg).continuous
    fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 2*Real.pi) (fun y _ => hd y) (hcont.intervalIntegrable _ _)
  have hp0 : g ((2*Real.pi : ℝ)*I) = g 0 := by
    simpa only [zero_add, exponentialPeriod, ofReal_mul, ofReal_ofNat] using hper 0
  rw [intervalIntegral.integral_mul_const] at h
  simp only [ofReal_zero, zero_mul, hp0, sub_self] at h
  exact (mul_eq_zero.mp h).resolve_right I_ne_zero

/-- Differentiation multiplies the genuine periodic Fourier coefficient by
its integer frequency. -/
theorem verticalFourierCoeff_deriv {p : ℂ → ℂ} (hp : Differentiable ℂ p)
    (hper : Function.Periodic p exponentialPeriod) (m : ℤ) :
    verticalFourierCoeff (deriv p) m = (m : ℂ)*verticalFourierCoeff p m := by
  have hd (z : ℂ) : deriv (fourierWeight p m) z =
      fourierWeight (deriv p) m z - (m : ℂ)*fourierWeight p m z := by
    have he := (Complex.hasDerivAt_exp (-(m : ℂ)*z)).comp z
      ((hasDerivAt_id z).const_mul (-(m : ℂ)))
    have h := (he.mul ((hp z).hasDerivAt)).deriv
    change deriv (fourierWeight p m) z = _ at h
    rw [h]
    simp only [fourierWeight, Function.comp_def]
    ring
  have h := vertical_integral_deriv_eq_zero (fourierWeight_entire hp m)
    (fourierWeight_periodic hper m)
  simp_rw [hd] at h
  rw [intervalIntegral.integral_sub
      (fourierWeight_intervalIntegrable (entire_deriv hp).continuous m)
      ((fourierWeight_intervalIntegrable hp.continuous m).const_mul (m : ℂ)),
    intervalIntegral.integral_const_mul] at h
  unfold verticalFourierCoeff
  rw [sub_eq_zero.mp h]
  ring

theorem verticalFourierCoeff_exp_mul (p : ℂ → ℂ) (d m : ℤ) :
    verticalFourierCoeff (fun z => Complex.exp ((d : ℂ)*z)*p z) m =
      verticalFourierCoeff p (m-d) := by
  unfold verticalFourierCoeff
  congr 1
  apply intervalIntegral.integral_congr
  intro y hy
  simp only [fourierWeight, ← mul_assoc, ← Complex.exp_add, Int.cast_sub]
  congr 2
  ring

theorem periodic_deriv {p : ℂ → ℂ} {h : ℂ} (hper : Function.Periodic p h) :
    Function.Periodic (deriv p) h := by
  have heq : (fun z => p (z+h)) = p := funext hper
  intro z
  have he := congrFun (congrArg deriv heq) z
  simpa only [deriv_comp_add_const] using he

/-- Conjugating differentiation by a common exponential factor. -/
def shiftedDeriv (a : ℂ) (p : ℂ → ℂ) (z : ℂ) : ℂ := deriv p z + a*p z

theorem shiftedDeriv_entire (a : ℂ) {p : ℂ → ℂ} (hp : Differentiable ℂ p) :
    Differentiable ℂ (shiftedDeriv a p) := (entire_deriv hp).add (differentiable_const _ |>.mul hp)

theorem shiftedDeriv_periodic (a : ℂ) {p : ℂ → ℂ} {h : ℂ}
    (hper : Function.Periodic p h) : Function.Periodic (shiftedDeriv a p) h := by
  intro z
  simp only [shiftedDeriv, periodic_deriv hper z, hper z]

theorem iterate_shiftedDeriv_entire (a : ℂ) {p : ℂ → ℂ} (hp : Differentiable ℂ p) (k : ℕ) :
    Differentiable ℂ ((shiftedDeriv a)^[k] p) := by
  induction k with
  | zero => simpa using hp
  | succ k ih => simpa only [Function.iterate_succ_apply'] using shiftedDeriv_entire a ih

theorem iterate_shiftedDeriv_periodic (a : ℂ) {p : ℂ → ℂ} {h : ℂ}
    (hper : Function.Periodic p h) (k : ℕ) :
    Function.Periodic ((shiftedDeriv a)^[k] p) h := by
  induction k with
  | zero => simpa using hper
  | succ k ih => simpa only [Function.iterate_succ_apply'] using shiftedDeriv_periodic a ih

theorem deriv_exp_mul (a : ℂ) {p : ℂ → ℂ} (hp : Differentiable ℂ p) :
    deriv (fun z => Complex.exp (a*z)*p z) =
      fun z => Complex.exp (a*z)*shiftedDeriv a p z := by
  funext z
  have hd := (((Complex.hasDerivAt_exp (a*z)).comp z
    ((hasDerivAt_id z).const_mul a)).mul (hp z).hasDerivAt).deriv
  change deriv (fun z => Complex.exp (a*z)*p z) z = _ at hd
  rw [hd]
  dsimp only [shiftedDeriv, Function.comp_def]
  ring

theorem iteratedDeriv_exp_mul (a : ℂ) {p : ℂ → ℂ} (hp : Differentiable ℂ p) (k : ℕ) :
    iteratedDeriv k (fun z => Complex.exp (a*z)*p z) =
      fun z => Complex.exp (a*z)*((shiftedDeriv a)^[k] p) z := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih, deriv_exp_mul a (iterate_shiftedDeriv_entire a hp k)]
    simp only [Function.iterate_succ_apply']

theorem verticalFourierCoeff_shiftedDeriv (a : ℂ) {p : ℂ → ℂ}
    (hp : Differentiable ℂ p) (hper : Function.Periodic p exponentialPeriod) (m : ℤ) :
    verticalFourierCoeff (shiftedDeriv a p) m =
      ((m : ℂ)+a)*verticalFourierCoeff p m := by
  unfold shiftedDeriv
  rw [verticalFourierCoeff_add (entire_deriv hp).continuous
    (show Continuous (fun z => a*p z) from continuous_const.mul hp.continuous),
    verticalFourierCoeff_deriv hp hper, verticalFourierCoeff_const_mul]
  ring

theorem verticalFourierCoeff_iterate_shiftedDeriv (a : ℂ) {p : ℂ → ℂ}
    (hp : Differentiable ℂ p) (hper : Function.Periodic p exponentialPeriod) (k : ℕ) (m : ℤ) :
    verticalFourierCoeff ((shiftedDeriv a)^[k] p) m =
      ((m : ℂ)+a)^k * verticalFourierCoeff p m := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply',
      verticalFourierCoeff_shiftedDeriv a (iterate_shiftedDeriv_entire a hp k)
        (iterate_shiftedDeriv_periodic a hper k), ih, pow_succ]
    ring

theorem verticalFourierCoeff_polynomial_exp_mul (P : Polynomial ℂ)
    {p : ℂ → ℂ} (hp : Continuous p) (m : ℤ) :
    verticalFourierCoeff (fun z => P.eval (Complex.exp z)*p z) m =
      ∑ d ∈ Finset.range (P.natDegree+1), P.coeff d * verticalFourierCoeff p (m-d) := by
  have heq : (fun z => P.eval (Complex.exp z)*p z) =
      fun z => ∑ d ∈ Finset.range (P.natDegree+1),
        P.coeff d * (Complex.exp ((d : ℂ)*z)*p z) := by
    funext z
    rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Complex.exp_nat_mul]
    ring
  rw [heq, verticalFourierCoeff_sum]
  · apply Finset.sum_congr rfl
    intro d hd
    rw [verticalFourierCoeff_const_mul]
    congr 1
    exact verticalFourierCoeff_exp_mul p (d : ℤ) m
  · intro d hd
    fun_prop

/-- The exact Fourier transform of the conjugated differential residual.
This form also applies to inhomogeneous equations. -/
theorem verticalFourierCoeff_shiftedOperator {n : ℕ} (P : Fin (n+1) → Polynomial ℂ)
    (a : ℂ) {p : ℂ → ℂ} (hp : Differentiable ℂ p)
    (hper : Function.Periodic p exponentialPeriod) (m : ℤ) :
    verticalFourierCoeff (fun z => ∑ j : Fin (n+1),
      (P j).eval (Complex.exp z)*((shiftedDeriv a)^[j.val] p) z) m =
    ∑ j : Fin (n+1), ∑ d ∈ Finset.range ((P j).natDegree+1),
      (P j).coeff d * (((m-d : ℤ) : ℂ)+a)^j.val * verticalFourierCoeff p (m-d) := by
  rw [verticalFourierCoeff_sum]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [verticalFourierCoeff_polynomial_exp_mul _ (iterate_shiftedDeriv_entire a hp _).continuous]
    apply Finset.sum_congr rfl
    intro d hd
    rw [verticalFourierCoeff_iterate_shiftedDeriv a hp hper]
    ring
  · intro j hj
    exact ((P j).continuous.comp Complex.continuous_exp).mul
      (iterate_shiftedDeriv_entire a hp _).continuous

/-- Finite Fourier support of a conjugated inhomogeneous residual gives the
eventual homogeneous Fourier balance needed by recurrence rigidity. -/
theorem verticalFourierCoeff_inhomogeneous_balance {n : ℕ} (P : Fin (n+1) → Polynomial ℂ)
    (a : ℂ) {p F : ℂ → ℂ} (hp : Differentiable ℂ p)
    (hper : Function.Periodic p exponentialPeriod) {M : ℕ}
    (hres : ∀ z, ∑ j : Fin (n+1),
      (P j).eval (Complex.exp z)*((shiftedDeriv a)^[j.val] p) z = F z)
    (hF : ∀ m : ℤ, (M : ℤ) ≤ |m| → verticalFourierCoeff F m = 0) :
    ∀ m : ℤ, (M : ℤ) ≤ |m| →
      (∑ j : Fin (n+1), ∑ d ∈ Finset.range ((P j).natDegree+1),
        (P j).coeff d * (((m-d : ℤ) : ℂ)+a)^j.val * verticalFourierCoeff p (m-d)) = 0 := by
  intro m hm
  rw [← verticalFourierCoeff_shiftedOperator P a hp hper,
    show (fun z => ∑ j : Fin (n+1),
      (P j).eval (Complex.exp z)*((shiftedDeriv a)^[j.val] p) z) = F from funext hres]
  exact hF m hm

/-- The exact Fourier balance of the conjugated ODE, directly from an
actual solution. The derivatives and contour coefficients are not assumed
to be asymptotic or formal symbols. -/
theorem verticalFourierCoeff_ode_balance {n : ℕ} (P : Fin (n+1) → Polynomial ℂ)
    (a : ℂ) {p : ℂ → ℂ} (hp : Differentiable ℂ p)
    (hper : Function.Periodic p exponentialPeriod)
    (hsol : Solves P (fun z => Complex.exp (a*z)*p z)) (m : ℤ) :
    (∑ j : Fin (n+1), ∑ d ∈ Finset.range ((P j).natDegree+1),
      (P j).coeff d * (((m-d : ℤ) : ℂ)+a)^j.val * verticalFourierCoeff p (m-d)) = 0 := by
  have hres : (fun z => ∑ j : Fin (n+1),
      (P j).eval (Complex.exp z)*((shiftedDeriv a)^[j.val] p) z) = fun _ => 0 := by
    funext z
    have hz := hsol z
    simp_rw [iteratedDeriv_exp_mul a hp] at hz
    have heq : (∑ j : Fin (n+1), (P j).eval (Complex.exp z) *
        (Complex.exp (a*z)*((shiftedDeriv a)^[j.val] p) z)) =
        Complex.exp (a*z)*(∑ j : Fin (n+1),
          (P j).eval (Complex.exp z)*((shiftedDeriv a)^[j.val] p) z) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [heq] at hz
    exact (mul_eq_zero.mp hz).resolve_left (Complex.exp_ne_zero _)
  have h := congrArg (fun f => verticalFourierCoeff f m) hres
  rw [verticalFourierCoeff_sum] at h
  · rw [verticalFourierCoeff_zero] at h
    convert h using 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [verticalFourierCoeff_polynomial_exp_mul _ (iterate_shiftedDeriv_entire a hp _).continuous]
    apply Finset.sum_congr rfl
    intro d hd
    rw [verticalFourierCoeff_iterate_shiftedDeriv a hp hper]
    ring
  · intro j hj
    exact ((P j).continuous.comp Complex.continuous_exp).mul
      (iterate_shiftedDeriv_entire a hp _).continuous

end LiWangWen

#print axioms LiWangWen.entire_deriv
#print axioms LiWangWen.verticalFourierCoeff_zero
#print axioms LiWangWen.verticalFourierCoeff_const_mul
#print axioms LiWangWen.fourierWeight_intervalIntegrable
#print axioms LiWangWen.verticalFourierCoeff_add
#print axioms LiWangWen.verticalFourierCoeff_sub
#print axioms LiWangWen.verticalFourierCoeff_sum
#print axioms LiWangWen.vertical_integral_deriv_eq_zero
#print axioms LiWangWen.verticalFourierCoeff_deriv
#print axioms LiWangWen.verticalFourierCoeff_exp_mul
#print axioms LiWangWen.periodic_deriv
#print axioms LiWangWen.shiftedDeriv_entire
#print axioms LiWangWen.shiftedDeriv_periodic
#print axioms LiWangWen.iterate_shiftedDeriv_entire
#print axioms LiWangWen.iterate_shiftedDeriv_periodic
#print axioms LiWangWen.deriv_exp_mul
#print axioms LiWangWen.iteratedDeriv_exp_mul
#print axioms LiWangWen.verticalFourierCoeff_shiftedDeriv
#print axioms LiWangWen.verticalFourierCoeff_iterate_shiftedDeriv
#print axioms LiWangWen.verticalFourierCoeff_polynomial_exp_mul
#print axioms LiWangWen.verticalFourierCoeff_shiftedOperator
#print axioms LiWangWen.verticalFourierCoeff_inhomogeneous_balance
#print axioms LiWangWen.verticalFourierCoeff_ode_balance
