import LiWangWenFiniteOrderBounds
import LiWangWenFloquet
import LiWangWenCoefficientExtraction

/-!
# Finite-order Floquet blocks with finite-order periodic coefficients

The finite-order solutions form a translation-invariant finite-dimensional
subspace. Spectral decomposition takes place inside that subspace, so every
block retains finite order and solves the original equation. Lagrange
extraction then gives finite order of each entire periodic coefficient,
including in the presence of cancellation.
-/

noncomputable section
open Polynomial
open scoped BigOperators

namespace LiWangWen

/-- Periodic coefficients of a finite monomial expansion inherit the actual
exponential bound of the whole sum, allowing cancellation between terms. -/
theorem periodic_monomial_coefficients_power_bound {k : ℕ} {h : ℂ}
    (hh : h ≠ 0) (p : Fin k → ℂ → ℂ)
    (hp : ∀ j, Function.Periodic (p j) h)
    (hg : PowerExponentialBound (fun z => ∑ j : Fin k, z^j.val * p j z)) :
    ∀ j, PowerExponentialBound (p j) := by
  classical
  let g : ℂ → ℂ := fun z => ∑ j : Fin k, z^j.val * p j z
  let P : ℂ → Polynomial ℂ := fun z => ∑ j : Fin k, C (p j z) * X^j.val
  let v : Fin k → ℂ := fun i => (i.val : ℂ)*h
  let L : Fin k → Polynomial ℂ := Lagrange.basis Finset.univ v
  have hv : Set.InjOn v (Finset.univ : Finset (Fin k)) := by
    intro i hi j hj hij
    apply Fin.ext
    have hc : (i.val : ℂ) = (j.val : ℂ) := mul_right_cancel₀ hh hij
    exact_mod_cast hc
  have hinterp (z : ℂ) :
      taylor z (P z) = Lagrange.interpolate Finset.univ v (fun i => g (z+v i)) := by
    apply Lagrange.eq_interpolate_of_eval_eq _ hv
    · simp only [degree_taylor, Finset.card_univ, Fintype.card_fin]
      exact degree_sum_fin_lt (fun j => p j z)
    · intro i hi
      rw [taylor_eval]
      dsimp [P, g]
      simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
      apply Finset.sum_congr rfl
      intro j hj
      rw [show p j (z+v i) = p j z from (hp j).nat_mul i.val z]
      ring
  have hcoeff (z : ℂ) (j : Fin k) : (P z).coeff j.val = p j z := by
    simp [P, Fin.val_inj]
  have hrecover (z : ℂ) (j : Fin k) :
      p j z = ∑ i : Fin k, g (z+v i) * (hasseDeriv j.val (L i)).eval (-z) := by
    have he := congrArg (fun Q : Polynomial ℂ => (taylor (-z) Q).coeff j.val) (hinterp z)
    simpa only [taylor_taylor, neg_add_cancel, taylor_zero, hcoeff,
      Lagrange.interpolate_apply, map_sum, taylor_mul, taylor_C,
      finsetSum_coeff, coeff_C_mul, taylor_coeff, L] using he
  intro j
  have hb : PowerExponentialBound (fun z =>
      ∑ i : Fin k, g (z+v i) * (hasseDeriv j.val (L i)).eval (-z)) := by
    apply power_bound_sum
    intro i hi
    exact (hg.translate (v i)).mul (power_bound_poly_comp _ power_bound_id.neg)
  have he : p j = (fun z =>
      ∑ i : Fin k, g (z+v i) * (hasseDeriv j.val (L i)).eval (-z)) :=
    funext (fun z => hrecover z j)
  rw [he]
  exact hb

/-- The same extraction theorem in the natural-number range notation used
by the finite-difference representation theorem. -/
theorem periodic_monomial_coefficients_power_bound_range {k : ℕ} {h : ℂ}
    (hh : h ≠ 0) (p : ℕ → ℂ → ℂ)
    (hp : ∀ j < k, Function.Periodic (p j) h)
    (hg : PowerExponentialBound (fun z => ∑ j ∈ Finset.range k, z^j * p j z)) :
    ∀ j < k, PowerExponentialBound (p j) := by
  have hf : PowerExponentialBound (fun z => ∑ j : Fin k, z^j.val * p j.val z) := by
    have he : (fun z => ∑ j : Fin k, z^j.val * p j.val z) =
        (fun z => ∑ j ∈ Finset.range k, z^j * p j z) := by
      funext z
      exact Fin.sum_univ_eq_sum_range (fun j => z^j * p j z) k
    rw [he]
    exact hg
  have hb := periodic_monomial_coefficients_power_bound hh
    (fun j : Fin k => p j.val) (fun j => hp j.val j.isLt) hf
  exact fun j hj => hb ⟨j, hj⟩


/-- All functions with global power-exponential bounds form a linear space. -/
def powerBoundSpace : Submodule ℂ (ℂ → ℂ) where
  carrier := {f | PowerExponentialBound f}
  zero_mem' := power_bound_const 0
  add_mem' := fun hf hg => hf.add hg
  smul_mem' := fun c _f hf => hf.const_mul c

/-- Finite-order entire solutions with the convenient global bound retained. -/
def powerBoundSolutionSpace {n : ℕ} (a : Fin (n+1) → ℂ → ℂ) :
    Submodule ℂ (ℂ → ℂ) := IncePeriodic.solutionSpace a ⊓ powerBoundSpace

theorem powerBoundSolutionSpace_finiteDimensional {n : ℕ}
    {a : Fin (n+1) → ℂ → ℂ} (ha : ∀ j, Differentiable ℂ (a j))
    (hlead : a (Fin.last n) 0 ≠ 0) :
    FiniteDimensional ℂ (powerBoundSolutionSpace a) := by
  let := IncePeriodic.solutionSpace_finiteDimensional ha hlead
  exact FiniteDimensional.of_injective
    (Submodule.inclusion (show powerBoundSolutionSpace a ≤ IncePeriodic.solutionSpace a from inf_le_left))
    (Submodule.inclusion_injective _)

/-- Translation preserves the finite-order solution subspace in both directions. -/
def powerBoundTranslateEquiv {n : ℕ} (a : Fin (n+1) → ℂ → ℂ) (h : ℂ)
    (hp : ∀ j, Function.Periodic (a j) h) :
    powerBoundSolutionSpace a ≃ₗ[ℂ] powerBoundSolutionSpace a where
  toFun f := ⟨fun z => (f : ℂ → ℂ) (z+h),
    ⟨f.property.1.1.comp (differentiable_id.add_const h),
      IncePeriodic.solves_translate hp f.property.1.2⟩,
    f.property.2.translate h⟩
  invFun f := ⟨fun z => (f : ℂ → ℂ) (z+(-h)),
    ⟨f.property.1.1.comp (differentiable_id.add_const (-h)),
      IncePeriodic.solves_translate (fun j => (hp j).neg) f.property.1.2⟩,
    f.property.2.translate (-h)⟩
  left_inv f := by apply Subtype.ext; funext z; simp
  right_inv f := by apply Subtype.ext; funext z; simp
  map_add' f g := rfl
  map_smul' c f := rfl

/-- A generalized Floquet block, keeping the polynomial in `z` together. -/
structure FiniteOrderFloquetBlock (h : ℂ) where
  exponent : ℂ
  length : ℕ
  coefficient : ℕ → ℂ → ℂ
  regular : ∀ j < length, Differentiable ℂ (coefficient j) ∧
    Function.Periodic (coefficient j) h ∧ CRGOrder.FiniteOrder (coefficient j)

def FiniteOrderFloquetBlock.eval {h : ℂ} (b : FiniteOrderFloquetBlock h) (z : ℂ) : ℂ :=
  Complex.exp (b.exponent*z) * ∑ j ∈ Finset.range b.length, z^j*b.coefficient j z

/-- Each block in the decomposition solves the same original equation. -/
def HasFiniteOrderFloquetBlocks {n : ℕ} (h : ℂ)
    (a : Fin (n+1) → ℂ → ℂ) (f : ℂ → ℂ) : Prop :=
  ∃ bs : List (FiniteOrderFloquetBlock h),
    (∀ b ∈ bs, IncePeriodic.Solves a b.eval) ∧
    ∀ z, f z = (bs.map (fun b => b.eval z)).sum

theorem hasFiniteOrderFloquetBlocks_zero {n : ℕ} (h : ℂ)
    (a : Fin (n+1) → ℂ → ℂ) : HasFiniteOrderFloquetBlocks h a (0 : ℂ → ℂ) := by
  exact ⟨[], by simp, by simp⟩

theorem HasFiniteOrderFloquetBlocks.add {n : ℕ} {h : ℂ}
    {a : Fin (n+1) → ℂ → ℂ} {f g : ℂ → ℂ}
    (hf : HasFiniteOrderFloquetBlocks h a f) (hg : HasFiniteOrderFloquetBlocks h a g) :
    HasFiniteOrderFloquetBlocks h a (f+g) := by
  obtain ⟨bs, hbs, hf⟩ := hf
  obtain ⟨cs, hcs, hg⟩ := hg
  refine ⟨bs++cs, ?_, ?_⟩
  · intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact hbs b hb
    · exact hcs b hb
  · intro z
    simp only [List.map_append, List.sum_append, Pi.add_apply, hf, hg]

/-- The full generalized-eigenspace argument inside the finite-order subspace.
No diagonalizability or bound on the generalized block size is assumed. -/
theorem finiteOrder_floquet_blocks {n : ℕ} {a : Fin (n+1) → ℂ → ℂ}
    (ha : ∀ j, Differentiable ℂ (a j)) (hlead : a (Fin.last n) 0 ≠ 0)
    {h : ℂ} (hh : h ≠ 0) (hp : ∀ j, Function.Periodic (a j) h)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hfo : CRGOrder.FiniteOrder f)
    (hsol : IncePeriodic.Solves a f) : HasFiniteOrderFloquetBlocks h a f := by
  let V := powerBoundSolutionSpace a
  let T := powerBoundTranslateEquiv a h hp
  let := powerBoundSolutionSpace_finiteDimensional ha hlead
  have hT : ∀ (v : V) z, (T v : ℂ → ℂ) z = (v : ℂ → ℂ) (z+h) := fun _ _ => rfl
  let v : V := ⟨f, ⟨hf, hsol⟩, power_bound_of_finiteOrder hf hfo⟩
  have hv : v ∈ ⨆ c : ℂ, Module.End.maxGenEigenspace T.toLinearMap c := by
    rw [Module.End.iSup_maxGenEigenspace_eq_top]
    trivial
  refine Submodule.iSup_induction
    (motive := fun w : V => HasFiniteOrderFloquetBlocks h a (w : ℂ → ℂ))
    (fun c : ℂ => Module.End.maxGenEigenspace T.toLinearMap c) hv ?_ ?_ ?_
  · intro c w hw
    obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace T.toLinearMap c w).mp hw
    by_cases hc : c = 0
    · subst c
      have hz := IncePeriodic.zero_multiplier_kernel T k hk
      subst w
      exact hasFiniteOrderFloquetBlocks_zero h a
    · have hkernel := IncePeriodic.difference_pow_eq_zero_of_generalizedEigenvector
        T (IncePeriodic.difference h) hT (fun _ _ => rfl) hh hc k w hk
      let b := Complex.log c/h
      let g := IncePeriodic.exponentialRemoval V b w
      have he : Differentiable ℂ g :=
        IncePeriodic.exponentialRemoval_entire b w.property.1.1
      obtain ⟨p, hpreg, hrep⟩ := IncePeriodic.finite_difference_representation hh he hkernel
      have hgbound : PowerExponentialBound g := w.property.2.remove_exponential b
      have hsum : PowerExponentialBound
          (fun z => ∑ j ∈ Finset.range k, z^j*p j z) := by
        have heq : g = (fun z => ∑ j ∈ Finset.range k, z^j*p j z) := funext hrep
        rwa [← heq]
      have hpb := periodic_monomial_coefficients_power_bound_range hh p
        (fun j hj => (hpreg j hj).2) hsum
      let B : FiniteOrderFloquetBlock h := ⟨b, k, p,
        fun j hj => ⟨(hpreg j hj).1, (hpreg j hj).2, (hpb j hj).finiteOrder⟩⟩
      have hweq : (w : ℂ → ℂ) = B.eval := by
        funext z
        calc
          (w : ℂ → ℂ) z = Complex.exp (b*z)*g z :=
            IncePeriodic.reconstruct_factor (w : ℂ → ℂ) b z
          _ = B.eval z := by rw [hrep]; rfl
      refine ⟨[B], ?_, ?_⟩
      · intro Q hQ
        have hQB : Q = B := List.mem_singleton.mp hQ
        subst Q
        rw [← hweq]
        exact w.property.1.2
      · intro z
        simpa only [List.map_singleton, List.sum_singleton] using congrFun hweq z
  · exact hasFiniteOrderFloquetBlocks_zero h a
  · intro u w hu hw
    exact hu.add hw

/-- Actual polynomial/exponential coefficients with leading coefficient
nonzero at `exp 0 = 1` admit finite-order solution blocks. -/
theorem polynomial_exp_finiteOrder_floquet_blocks {n : ℕ}
    {P : Fin (n+1) → Polynomial ℂ} (hlead : (P (Fin.last n)).eval 1 ≠ 0)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hfo : CRGOrder.FiniteOrder f)
    (hsol : Solves P f) : HasFiniteOrderFloquetBlocks exponentialPeriod
      (fun j z => (P j).eval (Complex.exp z)) f := by
  apply finiteOrder_floquet_blocks
    (fun j => (P j).differentiable.comp Complex.differentiable_exp)
    (by simpa using hlead) exponentialPeriod_ne_zero
    (fun j => by
      simpa only [frequencyPeriod, div_one, one_mul, Function.comp_def] using
        frequency_coefficients_periodic P (ω := 1) one_ne_zero j)
    hf hfo hsol

/-- Actual frequency-one polynomial/exponential coefficients satisfy all
periodicity and entire-coefficient assumptions of the block theorem. -/
theorem paper_finiteOrder_floquet_blocks {n γ : ℕ}
    {P : Fin (n+1) → Polynomial ℂ} (hlead : P (Fin.last n) = X^γ)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hfo : CRGOrder.FiniteOrder f)
    (hsol : Solves P f) : HasFiniteOrderFloquetBlocks exponentialPeriod
      (fun j z => (P j).eval (Complex.exp z)) f := by
  exact polynomial_exp_finiteOrder_floquet_blocks (by simp [hlead]) hf hfo hsol

#print axioms periodic_monomial_coefficients_power_bound
#print axioms periodic_monomial_coefficients_power_bound_range
#print axioms powerBoundSolutionSpace_finiteDimensional
#print axioms hasFiniteOrderFloquetBlocks_zero
#print axioms HasFiniteOrderFloquetBlocks.add
#print axioms finiteOrder_floquet_blocks
#print axioms polynomial_exp_finiteOrder_floquet_blocks
#print axioms paper_finiteOrder_floquet_blocks

end LiWangWen
