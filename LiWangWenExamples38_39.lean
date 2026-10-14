import LiWangWenCorollary33
import LiWangWenExamples
import LiWangWenMatrix31
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Complete finite-order conclusions of Examples 3.8 and 3.9.
The nonexistence step uses the proved representation theorem, not Frei's theorem. -/
set_option autoImplicit false
noncomputable section
open Polynomial
open scoped BigOperators
namespace LiWangWen

def constantPlusXCoefficients {n : ℕ} (b : Fin (n+1) → ℂ) (c : ℂ)
    (j : Fin (n+1)) : Polynomial ℂ := C (b j) + if j=0 then C c*X else 0

/-- The extra X in the constant term cannot cancel the top coefficient of
any nonzero polynomial solution of the transformed equation. -/
theorem constantPlusX_polynomial_obstruction {n : ℕ} (b : Fin (n+1) → ℂ)
    {c : ℂ} (hc : c ≠ 0) (a : ℂ) {u : Polynomial ℂ}
    (hu : transformedOperator (constantPlusXCoefficients b c) a u = 0) : u=0 := by
  by_contra hun
  have hh : u.coeff (u.natDegree+1)=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have he := congrArg (fun p : Polynomial ℂ => p.coeff (u.natDegree+1)) hu
  have hi (j : Fin n) :
      ((constantPlusXCoefficients b c j.succ)*
        (shiftedEuler a)^[j.succ.val] u).coeff (u.natDegree+1)=0 := by
    change ((C (b j.succ) + if j.succ=0 then C c*X else 0)*
      (shiftedEuler a)^[j.succ.val] u).coeff (u.natDegree+1)=0
    rw [if_neg (Fin.succ_ne_zero j),add_zero,coeff_C_mul,iterate_shiftedEuler_coeff,hh]
    ring
  have hz : ((constantPlusXCoefficients b c 0)*u).coeff (u.natDegree+1) =
      c*u.coeff u.natDegree := by
    simp [constantPlusXCoefficients, add_mul, mul_assoc, coeff_C_mul, coeff_X_mul]
  simp only [transformedOperator, Fin.sum_univ_succ, Fin.val_zero,
    Function.iterate_zero_apply, coeff_add, finsetSum_coeff, coeff_zero] at he
  rw [hz] at he
  simp_rw [hi] at he
  have hc' : c*u.coeff u.natDegree=0 := by simpa using he
  exact (leadingCoeff_ne_zero.mpr hun) (by simpa using (mul_eq_zero.mp hc').resolve_left hc)

/-- Any entire finite-order solution of this coefficient pattern is zero. -/
theorem constantPlusX_finiteOrder_solution_zero {n : ℕ} (b : Fin (n+1) → ℂ)
    {c : ℂ} (hc : c ≠ 0)
    (hlead : (constantPlusXCoefficients b c (Fin.last n)).eval 1 ≠ 0)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hfo : CRGOrder.FiniteOrder f)
    (hs : Solves (constantPlusXCoefficients b c) f) : f=0 := by
  by_contra hne
  obtain ⟨a,u,hu0,hu,_⟩ :=
    finiteOrder_solution_has_normalized_polynomial_solution hlead hf hfo hs hne
  have hz := constantPlusX_polynomial_obstruction b hc a hu
  simp [hz] at hu0

/-- Cauchy's estimate preserves a global exponential upper bound under any
fixed number of derivatives of an entire function. -/
theorem ExponentialBound.iterated_derivative {f : ℂ → ℂ} (hf : ExponentialBound f)
    (he : Differentiable ℂ f) (j : ℕ) : ExponentialBound (iteratedDeriv j f) := by
  obtain ⟨A,B,hA,hB,hbound⟩ := hf
  refine ⟨j.factorial*A*Real.exp B,B,mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hA)
    (Real.exp_pos _).le,hB,fun z => ?_⟩
  have hc : ∀ w ∈ Metric.sphere z 1, ‖f w‖ ≤ A*Real.exp (B*(‖z‖+1)) := by
    intro w hw
    have hd : ‖w-z‖=1 := by simpa [Metric.mem_sphere,dist_eq_norm] using hw
    have hn : ‖w‖ ≤ ‖z‖+1 := by
      calc
        ‖w‖ = ‖z+(w-z)‖ := by congr 1; ring
        _ ≤ ‖z‖+‖w-z‖ := norm_add_le _ _
        _ = ‖z‖+1 := by rw [hd]
    exact (hbound w).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hn hB)) hA)
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    j zero_lt_one he.diffContOnCl hc
  calc
    ‖iteratedDeriv j f z‖ ≤ j.factorial*(A*Real.exp (B*(‖z‖+1))) := by simpa using h
    _ = (j.factorial*A*Real.exp B)*Real.exp (B*‖z‖) := by rw [mul_add, mul_one,Real.exp_add]; ring

def example39Coefficients : Fin 3 → Polynomial ℂ := ![X,1,1]

/-- Example 3.9: no nonzero entire finite-order solution of f''+f'+exp(z)f=0. -/
theorem example39_no_nonzero_finiteOrder_solution {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hfo : CRGOrder.FiniteOrder f)
    (hs : Solves example39Coefficients f) : f=0 := by
  have he : example39Coefficients = constantPlusXCoefficients ![0,1,1] 1 := by
    funext j; fin_cases j <;> simp [example39Coefficients,constantPlusXCoefficients]
  rw [he] at hs
  exact constantPlusX_finiteOrder_solution_zero ![0,1,1] one_ne_zero
    (by norm_num [constantPlusXCoefficients,Fin.last]) hf hfo hs


def example38Coefficients : Fin 4 → Polynomial ℂ := ![-(1+X),3+2*X,-(3+X),1]
def example38Aux (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  iteratedDeriv 2 f z-2*deriv f z+f z

theorem example38_aux_equation {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hs : Solves example38Coefficients f) :
    Differentiable ℂ (example38Aux f) ∧
      Solves (constantPlusXCoefficients ![-1,1] (-1)) (example38Aux f) := by
  have haux : Differentiable ℂ (example38Aux f) :=
    ((IncePeriodic.entire_iteratedDeriv hf 2).sub (hf.deriv.const_mul 2)).add hf
  refine ⟨haux,fun z => ?_⟩
  have hd : deriv (example38Aux f) z = iteratedDeriv 3 f z-2*iteratedDeriv 2 f z+deriv f z := by
    have h := ((((IncePeriodic.entire_iteratedDeriv hf 2) z).hasDerivAt).sub
      (((hf.deriv z).hasDerivAt).const_mul 2)).add ((hf z).hasDerivAt)
    have heq : ((iteratedDeriv 2 f-(fun y => 2*deriv f y))+f)=example38Aux f := by
      funext w; rfl
    rw [heq] at h
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using h.deriv
  have hz := hs z
  norm_num [example38Coefficients,Fin.sum_univ_succ] at hz
  norm_num [constantPlusXCoefficients,Fin.sum_univ_succ,Fin.last,iteratedDeriv_one]
  rw [hd]
  dsimp only [example38Aux]
  convert hz using 1; ring

theorem affine_of_second_derivative_zero {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (h2 : ∀ z, deriv (deriv g) z=0) : ∃ A B : ℂ, ∀ z, g z=A+B*z := by
  have hd (z : ℂ) : deriv g z=deriv g 0 := is_const_of_deriv_eq_zero hg.deriv h2 z 0
  let H : ℂ → ℂ := fun z => g z-g 0-deriv g 0*z
  have hH : Differentiable ℂ H := (hg.sub (differentiable_const _)).sub
    (differentiable_id.const_mul _)
  have hHd (z : ℂ) : deriv H z=0 := by
    have h := (((hg z).hasDerivAt).sub (hasDerivAt_const z (g 0))).sub
      ((hasDerivAt_id z).const_mul (deriv g 0))
    have heq : ((g-(fun _ => g 0))-(fun y => deriv g 0*id y))=H := by funext w; rfl
    rw [heq] at h
    simpa only [sub_zero,mul_one,hd z,sub_self] using h.deriv
  refine ⟨g 0,deriv g 0,fun z => ?_⟩
  have h := is_const_of_deriv_eq_zero hH hHd z 0
  dsimp [H] at h
  linear_combination h

/-- Example 3.8: every entire finite-order solution has exactly the stated
linear span, including the zero solution. -/
theorem example38_classification {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hfo : CRGOrder.FiniteOrder f) (hs : Solves example38Coefficients f) :
    ∃ A B : ℂ, ∀ z, f z=Complex.exp z*(A+B*z) := by
  have hb := finiteOrder_solution_exponentialBound_direct
    (P:=example38Coefficients) (by norm_num [example38Coefficients,Fin.last]) hf hfo hs
  obtain ⟨haux,hauxsol⟩ := example38_aux_equation hf hs
  have hb1 : ExponentialBound (deriv f) := by simpa using hb.iterated_derivative hf 1
  have hauxb : ExponentialBound (example38Aux f) :=
    ((hb.iterated_derivative hf 2).sub (hb1.const_mul 2)).add hb
  have hzero : example38Aux f=0 := constantPlusX_finiteOrder_solution_zero ![-1,1]
    (by norm_num) (by norm_num [constantPlusXCoefficients,Fin.last])
    haux hauxb.finiteOrder hauxsol
  let g : ℂ → ℂ := fun z => Complex.exp (-z)*f z
  have heg : Differentiable ℂ (fun z : ℂ => Complex.exp (-z)) :=
    Complex.differentiable_exp.comp differentiable_id.neg
  have hg : Differentiable ℂ g := heg.mul hf
  have he (z : ℂ) : HasDerivAt (fun w : ℂ => Complex.exp (-w)) (-Complex.exp (-z)) z := by
    simpa only [Function.comp_def, mul_neg, mul_one] using
      (Complex.hasDerivAt_exp (-z)).comp z (hasDerivAt_id z).neg
  have hdg (z : ℂ) : deriv g z=Complex.exp (-z)*(deriv f z-f z) := by
    have h := (he z).mul ((hf z).hasDerivAt)
    change deriv g z= _
    rw [show deriv g z=(-Complex.exp (-z))*f z+Complex.exp (-z)*deriv f z from h.deriv]
    ring
  have hdgfun : deriv g=(fun z => Complex.exp (-z)*(deriv f z-f z)) := funext hdg
  have h2 (z : ℂ) : deriv (deriv g) z=0 := by
    rw [hdgfun]
    have h := (he z).mul (((hf.deriv z).hasDerivAt).sub ((hf z).hasDerivAt))
    change HasDerivAt (fun w : ℂ => Complex.exp (-w)*(deriv f w-f w))
      (-Complex.exp (-z)*(deriv f z-f z)+Complex.exp (-z)*(deriv (deriv f) z-deriv f z)) z at h
    rw [h.deriv]
    have hz : example38Aux f z=0 := congrFun hzero z
    dsimp [example38Aux] at hz
    simp only [iteratedDeriv_succ,iteratedDeriv_zero] at hz
    linear_combination Complex.exp (-z)*hz
  obtain ⟨A,B,hAB⟩ := affine_of_second_derivative_zero hg h2
  refine ⟨A,B,fun z => ?_⟩
  calc
    f z=Complex.exp z*g z := by
      dsimp [g]
      rw [←mul_assoc,←Complex.exp_add]
      simp
    _=Complex.exp z*(A+B*z) := by rw [hAB z]


def example38Family (A B z : ℂ) : ℂ := Complex.exp z*(A+B*z)

theorem example38_family_deriv (A B : ℂ) :
    deriv (example38Family A B)=example38Family (A+B) B := by
  funext z
  have h := (Complex.hasDerivAt_exp z).mul
    ((hasDerivAt_const z A).add ((hasDerivAt_id z).const_mul B))
  have heq : (Complex.exp*((fun _ => A)+(fun w => B*id w)))=example38Family A B := by funext w; rfl
  rw [heq] at h
  rw [h.deriv]
  dsimp [example38Family]
  ring

theorem example38_family_iteratedDeriv (j : ℕ) (A B : ℂ) :
    iteratedDeriv j (example38Family A B)=example38Family (A+j*B) B := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ,ih,example38_family_deriv]
    congr 1
    push_cast
    ring

theorem example38_family_solution (A B : ℂ) :
    Differentiable ℂ (example38Family A B) ∧
      CRGOrder.FiniteOrder (example38Family A B) ∧
      Solves example38Coefficients (example38Family A B) := by
  refine ⟨?_,?_,fun z => ?_⟩
  · change Differentiable ℂ (fun z => Complex.exp z*(A+B*z))
    fun_prop
  · have hb := (bound_exp 1).mul ((bound_const A).add (bound_id.const_mul B))
    have hb' : ExponentialBound (example38Family A B) := by
      change ExponentialBound (fun z => Complex.exp z*(A+B*z))
      simpa only [one_mul] using hb
    exact hb'.finiteOrder
  · rw [Fin.sum_univ_four]
    change (example38Coefficients 0).eval (Complex.exp z)*iteratedDeriv 0 (example38Family A B) z+
      (example38Coefficients 1).eval (Complex.exp z)*iteratedDeriv 1 (example38Family A B) z+
      (example38Coefficients 2).eval (Complex.exp z)*iteratedDeriv 2 (example38Family A B) z+
      (example38Coefficients 3).eval (Complex.exp z)*iteratedDeriv 3 (example38Family A B) z=0
    rw [example38_family_iteratedDeriv 0,example38_family_iteratedDeriv 1,
      example38_family_iteratedDeriv 2,example38_family_iteratedDeriv 3,
      show example38Coefficients 0= -(1+X) from rfl,
      show example38Coefficients 1=3+2*X from rfl,
      show example38Coefficients 2= -(3+X) from rfl,
      show example38Coefficients 3=1 from rfl]
    norm_num [example38Family]
    ring

/-- The two displayed solutions in Example 3.8 are linearly independent. -/
theorem example38_linearIndependent :
    LinearIndependent ℂ ![(fun z : ℂ => Complex.exp z),(fun z : ℂ => z*Complex.exp z)] := by
  rw [linearIndependent_fin2]
  constructor
  · intro h
    have hz := congrFun h 1
    apply Complex.exp_ne_zero 1
    simpa only [Matrix.cons_val_one,Matrix.cons_val_zero,one_mul,Pi.zero_apply] using hz
  · intro a h
    have hz := congrFun h 0
    norm_num at hz

/-- Complete two-sided statement of Example 3.8, without any assumed basis
or dimension bound. -/
theorem example38_finiteOrder_iff (f : ℂ → ℂ) :
    (Differentiable ℂ f ∧ CRGOrder.FiniteOrder f ∧ Solves example38Coefficients f) ↔
      ∃ A B : ℂ, ∀ z, f z=Complex.exp z*(A+B*z) := by
  constructor
  · rintro ⟨hf,hfo,hs⟩
    exact example38_classification hf hfo hs
  · rintro ⟨A,B,h⟩
    have he : f=example38Family A B := funext h
    rw [he]
    exact example38_family_solution A B

/-- Example 3.9: every nonzero entire solution has infinite order. -/
theorem example39_nonzero_solution_not_finiteOrder {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hs : Solves example39Coefficients f) (hne : f ≠ 0) :
    ¬CRGOrder.FiniteOrder f := fun hfo => hne (example39_no_nonzero_finiteOrder_solution hf hfo hs)

#print axioms constantPlusX_polynomial_obstruction
#print axioms constantPlusX_finiteOrder_solution_zero
#print axioms ExponentialBound.iterated_derivative
#print axioms example39_no_nonzero_finiteOrder_solution
#print axioms example38_aux_equation
#print axioms affine_of_second_derivative_zero
#print axioms example38_classification
#print axioms example38_family_deriv
#print axioms example38_family_iteratedDeriv
#print axioms example38_family_solution
#print axioms example38_linearIndependent
#print axioms example38_finiteOrder_iff
#print axioms example39_nonzero_solution_not_finiteOrder
end LiWangWen
