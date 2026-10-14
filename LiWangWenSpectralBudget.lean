import LiWangWenFiniteOrderFloquet
import Mathlib.LinearAlgebra.Dimension.Constructions

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace LiWangWen

/-- The exponent needed to kill a generalized eigenspace is at most the
 dimension of that eigenspace, rather than the dimension of the ambient space. -/
theorem generalizedEigenvector_dimension_power {V : Type*}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (T : Module.End ℂ V) (c : ℂ) {v : V}
    (hv : v ∈ T.maxGenEigenspace c) :
    ((T-c • 1)^Module.finrank ℂ (T.maxGenEigenspace c)) v = 0 := by
  let E := T.maxGenEigenspace c
  let N := T-c • 1
  have hN : ∀ x ∈ E, N x ∈ E :=
    T.mapsTo_maxGenEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes T c) c
  let R : Module.End ℂ E := N.restrict hN
  have hpow (k : ℕ) (x : E) : ((R^k) x : V) = (N^k) (x : V) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply]
      change N ((R^k) x : V) = N ((N^k) (x : V))
      rw [ih]
  let w : E := ⟨v,hv⟩
  obtain ⟨k,hk⟩ := (Module.End.mem_maxGenEigenspace T c v).mp hv
  have hr : w ∈ LinearMap.ker (R^k) := by
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    simpa only [hpow, ZeroMemClass.coe_zero] using hk
  have hd := Module.End.ker_pow_le_ker_pow_finrank R k hr
  have hz := congrArg Subtype.val (LinearMap.mem_ker.mp hd)
  simpa only [hpow, ZeroMemClass.coe_zero] using hz

/-- Distinct generalized eigenspaces consume a total dimension bounded by
 the dimension of the actual finite-order solution space. -/
theorem generalizedEigenspace_finrank_sum_le {V : Type*}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (T : Module.End ℂ V) (s : Finset ℂ) :
    ∑ c ∈ s, Module.finrank ℂ (T.maxGenEigenspace c) ≤ Module.finrank ℂ V := by
  classical
  let E : s → Submodule ℂ V := fun c => T.maxGenEigenspace c.val
  have hind : iSupIndep E := T.independent_maxGenEigenspace.comp Subtype.coe_injective
  have hle := LinearMap.finrank_le_finrank_of_injective hind.dfinsupp_lsum_injective
  rw [DFinsupp.linearEquivFunOnFintype.finrank_eq, Module.finrank_pi_fintype] at hle
  calc
    _ = ∑ c : s, Module.finrank ℂ (T.maxGenEigenspace c.val) :=
      (Finset.sum_coe_sort s (fun c => Module.finrank ℂ (T.maxGenEigenspace c))).symm
    _ ≤ _ := hle

#print axioms generalizedEigenvector_dimension_power
#print axioms generalizedEigenspace_finrank_sum_le
end LiWangWen
