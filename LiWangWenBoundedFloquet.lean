import LiWangWenSpectralBudget

set_option autoImplicit false
noncomputable section
open Polynomial
open scoped BigOperators

namespace LiWangWen

theorem generalized_solution_floquet_block {n : ℕ}
    {a : Fin (n+1) → ℂ → ℂ} {h : ℂ} (hh : h ≠ 0)
    (hp : ∀ j, Function.Periodic (a j) h)
    (c : ℂ) (hc : c ≠ 0) (k : ℕ) (w : powerBoundSolutionSpace a)
    (hk : (((powerBoundTranslateEquiv a h hp).toLinearMap-c • 1)^k) w = 0) :
    ∃ B : FiniteOrderFloquetBlock h,
      B.length = k ∧ (w : ℂ → ℂ) = B.eval ∧ IncePeriodic.Solves a B.eval := by
  let V := powerBoundSolutionSpace a
  let T := powerBoundTranslateEquiv a h hp
  have hT : ∀ (v : V) z, (T v : ℂ → ℂ) z = (v : ℂ → ℂ) (z+h) := fun _ _ => rfl
  have hkernel := IncePeriodic.difference_pow_eq_zero_of_generalizedEigenvector
    T (IncePeriodic.difference h) hT (fun _ _ => rfl) hh hc k w hk
  let b := Complex.log c/h
  let g := IncePeriodic.exponentialRemoval V b w
  have he : Differentiable ℂ g :=
    IncePeriodic.exponentialRemoval_entire b w.property.1.1
  obtain ⟨p,hpreg,hrep⟩ := IncePeriodic.finite_difference_representation hh he hkernel
  have hgb : PowerExponentialBound g := w.property.2.remove_exponential b
  have hsum : PowerExponentialBound (fun z => ∑ j ∈ Finset.range k, z^j*p j z) := by
    have heq : g = (fun z => ∑ j ∈ Finset.range k, z^j*p j z) := funext hrep
    rwa [← heq]
  have hpb := periodic_monomial_coefficients_power_bound_range hh p
    (fun j hj => (hpreg j hj).2) hsum
  let B : FiniteOrderFloquetBlock h := ⟨b,k,p,
    fun j hj => ⟨(hpreg j hj).1,(hpreg j hj).2,(hpb j hj).finiteOrder⟩⟩
  have hw : (w : ℂ → ℂ) = B.eval := by
    funext z
    calc
      (w : ℂ → ℂ) z = Complex.exp (b*z)*g z :=
        IncePeriodic.reconstruct_factor (w : ℂ → ℂ) b z
      _ = B.eval z := by rw [hrep]; rfl
  exact ⟨B,rfl,hw,hw ▸ w.property.1.2⟩

/-- One block for each participating translation eigenvalue, retaining the
 total Jordan-length budget from the finite-dimensional solution space. -/
theorem bounded_finiteOrder_floquet_blocks {n : ℕ}
    {a : Fin (n+1) → ℂ → ℂ} (ha : ∀ j, Differentiable ℂ (a j))
    (hlead : a (Fin.last n) 0 ≠ 0) {h : ℂ} (hh : h ≠ 0)
    (hp : ∀ j, Function.Periodic (a j) h) {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hfo : CRGOrder.FiniteOrder f)
    (hsol : IncePeriodic.Solves a f) :
    ∃ s : Finset ℂ, ∃ B : s → FiniteOrderFloquetBlock h,
      (∀ c, IncePeriodic.Solves a (B c).eval ∧ (B c).eval ≠ 0 ∧ 0 < (B c).length) ∧
      (∑ c, (B c).length) ≤ n ∧ ∀ z, f z = ∑ c, (B c).eval z := by
  classical
  let V := powerBoundSolutionSpace a
  let T := powerBoundTranslateEquiv a h hp
  let := powerBoundSolutionSpace_finiteDimensional ha hlead
  let := IncePeriodic.solutionSpace_finiteDimensional ha hlead
  let v : V := ⟨f,⟨hf,hsol⟩,power_bound_of_finiteOrder hf hfo⟩
  have hv : v ∈ ⨆ c : ℂ, Module.End.maxGenEigenspace T.toLinearMap c := by
    rw [Module.End.iSup_maxGenEigenspace_eq_top]
    trivial
  obtain ⟨q,hq,hqsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ v).mp hv
  let s := q.support
  have block (c : s) : ∃ B : FiniteOrderFloquetBlock h,
      B.length = Module.finrank ℂ (Module.End.maxGenEigenspace T.toLinearMap c.val) ∧
      (q c.val : ℂ → ℂ) = B.eval ∧ IncePeriodic.Solves a B.eval := by
    have hcq : q c.val ≠ 0 := Finsupp.mem_support_iff.mp c.property
    have hc : c.val ≠ 0 := by
      intro hc
      obtain ⟨k,hk⟩ := (Module.End.mem_maxGenEigenspace T.toLinearMap c.val _).mp (hq c.val)
      rw [hc] at hk
      have hz := IncePeriodic.zero_multiplier_kernel T k hk
      apply hcq
      simpa only [hc] using hz
    exact generalized_solution_floquet_block hh hp c.val hc _ (q c.val)
      (generalizedEigenvector_dimension_power T.toLinearMap c.val (hq c.val))
  choose B hlen hrep hBsol using block
  refine ⟨s,B,?_,?_,?_⟩
  · intro c
    have hqne : q c.val ≠ 0 := Finsupp.mem_support_iff.mp c.property
    have hBne : (B c).eval ≠ 0 := by
      intro h
      exact hqne (Subtype.ext (by simpa only [ZeroMemClass.coe_zero] using (hrep c).trans h))
    refine ⟨hBsol c,hBne,?_⟩
    by_contra h
    have hz : (B c).length = 0 := Nat.eq_zero_of_not_pos h
    apply hBne
    funext z
    simp [FiniteOrderFloquetBlock.eval,hz]
  · have hdim : Module.finrank ℂ V ≤ n :=
      (Submodule.finrank_mono (show V ≤ IncePeriodic.solutionSpace a from inf_le_left)).trans
        (IncePeriodic.finrank_solutionSpace_le ha hlead)
    have he : (∑ c : s, (B c).length) =
        ∑ c ∈ s, Module.finrank ℂ (Module.End.maxGenEigenspace T.toLinearMap c) := by
      simp only [hlen]
      exact Finset.sum_coe_sort s (fun c => Module.finrank ℂ (Module.End.maxGenEigenspace T.toLinearMap c))
    rw [he]
    exact (generalizedEigenspace_finrank_sum_le T.toLinearMap s).trans hdim
  · intro z
    have he := congrFun (congrArg Subtype.val hqsum) z
    simp only [Finsupp.sum,Submodule.coe_sum,Finset.sum_apply] at he
    change (∑ c ∈ s, (q c : ℂ → ℂ) z) = f z at he
    rw [← he,← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro c hc
    exact congrFun (hrep c) z

#print axioms generalized_solution_floquet_block
#print axioms bounded_finiteOrder_floquet_blocks
end LiWangWen
