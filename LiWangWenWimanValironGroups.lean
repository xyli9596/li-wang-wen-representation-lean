import LiWangWenWimanValironStrip

/-!
# Grouping the actual exponential-polynomial Wiman--Valiron equation

The group set and its extreme derivative powers are extracted from the
coefficients of the given polynomials. The resulting strip conclusions use
the exact substituted equation and the proved derivative-ratio limits.
-/

set_option autoImplicit false
noncomputable section
open Filter Finset Polynomial
open scoped Topology

namespace LiWangWen

def exponentialDegreeSupport {ι : Type*} [Fintype ι]
    (P : ι → Polynomial ℂ) : Finset ℕ :=
  Finset.univ.biUnion (fun j => (P j).support)

theorem mem_exponentialDegreeSupport {ι : Type*} [Fintype ι]
    (P : ι → Polynomial ℂ) (d : ℕ) :
    d ∈ exponentialDegreeSupport P ↔ ∃ j, (P j).coeff d ≠ 0 := by
  simp [exponentialDegreeSupport, Polynomial.mem_support_iff]

theorem exponentialDegreeSupport_nonempty {ι : Type*} [Fintype ι]
    (P : ι → Polynomial ℂ) (hP : ∃ j, P j ≠ 0) : (exponentialDegreeSupport P).Nonempty := by
  obtain ⟨j,hj⟩ := hP
  obtain ⟨d,hd⟩ := Polynomial.support_nonempty.mpr hj
  exact ⟨d,(mem_exponentialDegreeSupport P d).mpr ⟨j,Polynomial.mem_support_iff.mp hd⟩⟩

theorem eval_eq_sum_exponentialDegreeSupport {ι : Type*} [Fintype ι]
    (P : ι → Polynomial ℂ) (j : ι) (z : ℂ) :
    (P j).eval z = ∑ d ∈ exponentialDegreeSupport P, (P j).coeff d * z^d := by
  classical
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  apply Finset.sum_subset
  · intro d hd
    exact (mem_exponentialDegreeSupport P d).mpr ⟨j,Polynomial.mem_support_iff.mp hd⟩
  · intro d _ hd
    have hzero : (P j).coeff d = 0 := by simpa only [Polynomial.mem_support_iff, not_not] using hd
    rw [hzero,zero_mul]

/-- This is an exact regrouping, before any approximation or dominance
argument. Each exponential degree appears exactly once. -/
theorem polynomial_exponential_grouping {ι : Type*} [Fintype ι]
    (P : ι → Polynomial ℂ) (index : ι → ℕ) (b : ι → ℂ) (z w : ℂ) :
    (∑ j, (P j).eval (Complex.exp z)*b j*w^(index j)) =
      ∑ d ∈ exponentialDegreeSupport P,
        (∑ j, (P j).coeff d*b j*w^(index j))*Complex.exp ((d : ℂ)*z) := by
  simp_rw [eval_eq_sum_exponentialDegreeSupport P, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro j _
  rw [Complex.exp_nat_mul]
  ring

theorem exists_group_max_index {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : ι → Polynomial ℂ) (index : ι → ℕ) {d : ℕ}
    (hd : d ∈ exponentialDegreeSupport P) :
    ∃ j : ι, (P j).coeff d ≠ 0 ∧ ∀ k : ι, (P k).coeff d ≠ 0 → index k ≤ index j := by
  obtain ⟨j,hj⟩ := (mem_exponentialDegreeSupport P d).mp hd
  let s : Finset ι := Finset.univ.filter (fun j => (P j).coeff d ≠ 0)
  have hs : s.Nonempty := ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ j,hj⟩⟩
  obtain ⟨k,hk,hmax⟩ := Finset.exists_max_image s index hs
  refine ⟨k,(Finset.mem_filter.mp hk).2,?_⟩
  intro j hj
  exact hmax j (Finset.mem_filter.mpr ⟨Finset.mem_univ j,hj⟩)

theorem exists_group_min_index {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : ι → Polynomial ℂ) (index : ι → ℕ) {d : ℕ}
    (hd : d ∈ exponentialDegreeSupport P) :
    ∃ j : ι, (P j).coeff d ≠ 0 ∧ ∀ k : ι, (P k).coeff d ≠ 0 → index j ≤ index k := by
  obtain ⟨j,hj⟩ := (mem_exponentialDegreeSupport P d).mp hd
  let s : Finset ι := Finset.univ.filter (fun j => (P j).coeff d ≠ 0)
  have hs : s.Nonempty := ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ j,hj⟩⟩
  obtain ⟨k,hk,hmin⟩ := Finset.exists_min_image s index hs
  refine ⟨k,(Finset.mem_filter.mp hk).2,?_⟩
  intro j hj
  exact hmin j (Finset.mem_filter.mpr ⟨Finset.mem_univ j,hj⟩)

/-- If the actual logarithmic derivative tends to infinity, the original
substituted equation forces its evaluation points into a logarithmic strip. -/
theorem exponential_ode_large_w_strip {α ι : Type*} [Fintype ι] [DecidableEq ι]
    {l : Filter α} (P : ι → Polynomial ℂ) (hP : ∃ j, P j ≠ 0)
    (index : ι → ℕ) (hinj : Function.Injective index)
    {b : α → ι → ℂ} {z w : α → ℂ}
    (hb : ∀ j, Tendsto (fun x => b x j) l (𝓝 1))
    (hw : Tendsto (fun x => ‖w x‖) l atTop)
    (hbalance : ∀ᶠ x in l, ∑ j, (P j).eval (Complex.exp (z x))*b x j*(w x)^(index j) = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x in l, |(z x).re| ≤ C*(1+|Real.log ‖w x‖|) := by
  classical
  let s : Finset ℕ := exponentialDegreeSupport P
  have hs : s.Nonempty := exponentialDegreeSupport_nonempty P hP
  have : Nonempty s := ⟨⟨hs.choose,hs.choose_spec⟩⟩
  have hchoose : ∀ d : s, ∃ j : ι, (P j).coeff d ≠ 0 ∧
      ∀ k : ι, (P k).coeff d ≠ 0 → index k ≤ index j := by
    intro d
    exact exists_group_max_index P index d.property
  choose k hk hmax using hchoose
  let A : α → s → ℂ := fun x d => ∑ j, (P j).coeff d*b x j*(w x)^(index j)
  have hAnorm : ∀ d : s, Tendsto (fun x => A x d/(w x)^(index (k d))) l
      (𝓝 ((P (k d)).coeff d)) := by
    intro d
    exact perturbed_polynomial_max_normalized index hinj (fun j => (P j).coeff d)
      (k d) (hmax d) hb hw
  have hwne : ∀ᶠ x in l, w x ≠ 0 := by
    filter_upwards [hw.eventually (eventually_gt_atTop (0 : ℝ))] with x hx
    exact norm_pos_iff.mp hx
  have hbal : ∀ᶠ x in l, ∑ d : s, A x d*Complex.exp ((d : ℂ)*z x) = 0 := by
    filter_upwards [hbalance] with x hx
    rw [polynomial_exponential_grouping P index (b x) (z x) (w x)] at hx
    exact (Finset.sum_coe_sort s (fun d =>
      (∑ j, (P j).coeff d*b x j*(w x)^(index j))*Complex.exp ((d : ℂ)*z x))).trans hx
  exact eventually_logarithmic_strip_of_normalized_groups
    (fun d : s => d.val) (fun d => index (k d)) Subtype.val_injective hk hAnorm hwne hbal

/-- The same direct conclusion for a logarithmic derivative tending to
zero, using the smallest nonzero derivative index in every group. -/
theorem exponential_ode_small_w_strip {α ι : Type*} [Fintype ι] [DecidableEq ι]
    {l : Filter α} (P : ι → Polynomial ℂ) (hP : ∃ j, P j ≠ 0)
    (index : ι → ℕ) (hinj : Function.Injective index)
    {b : α → ι → ℂ} {z w : α → ℂ}
    (hb : ∀ j, Tendsto (fun x => b x j) l (𝓝 1))
    (hw : Tendsto w l (𝓝 0)) (hwne : ∀ᶠ x in l, w x ≠ 0)
    (hbalance : ∀ᶠ x in l, ∑ j, (P j).eval (Complex.exp (z x))*b x j*(w x)^(index j) = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x in l, |(z x).re| ≤ C*(1+|Real.log ‖w x‖|) := by
  classical
  let s : Finset ℕ := exponentialDegreeSupport P
  have hs : s.Nonempty := exponentialDegreeSupport_nonempty P hP
  have : Nonempty s := ⟨⟨hs.choose,hs.choose_spec⟩⟩
  have hchoose : ∀ d : s, ∃ j : ι, (P j).coeff d ≠ 0 ∧
      ∀ k : ι, (P k).coeff d ≠ 0 → index j ≤ index k := by
    intro d
    exact exists_group_min_index P index d.property
  choose k hk hmin using hchoose
  let A : α → s → ℂ := fun x d => ∑ j, (P j).coeff d*b x j*(w x)^(index j)
  have hAnorm : ∀ d : s, Tendsto (fun x => A x d/(w x)^(index (k d))) l
      (𝓝 ((P (k d)).coeff d)) := by
    intro d
    exact perturbed_polynomial_min_normalized index hinj (fun j => (P j).coeff d)
      (k d) (hmin d) hb hw hwne
  have hbal : ∀ᶠ x in l, ∑ d : s, A x d*Complex.exp ((d : ℂ)*z x) = 0 := by
    filter_upwards [hbalance] with x hx
    rw [polynomial_exponential_grouping P index (b x) (z x) (w x)] at hx
    exact (Finset.sum_coe_sort s (fun d =>
      (∑ j, (P j).coeff d*b x j*(w x)^(index j))*Complex.exp ((d : ℂ)*z x))).trans hx
  exact eventually_logarithmic_strip_of_normalized_groups
    (fun d : s => d.val) (fun d => index (k d)) Subtype.val_injective hk hAnorm hwne hbal

/-- The large-variable result is uniform above one fixed threshold. No
assumption that the logarithmic derivative actually diverges is required. -/
theorem exponential_ode_large_w_strip_threshold {α ι : Type*} [Fintype ι] [DecidableEq ι]
    {l : Filter α} (P : ι → Polynomial ℂ) (hP : ∃ j, P j ≠ 0)
    (index : ι → ℕ) (hinj : Function.Injective index)
    {b : α → ι → ℂ} {z w : α → ℂ}
    (hb : ∀ j, Tendsto (fun x => b x j) l (𝓝 1))
    (hbalance : ∀ᶠ x in l, ∑ j, (P j).eval (Complex.exp (z x))*b x j*(w x)^(index j) = 0) :
    ∃ Q : ℝ, 1 ≤ Q ∧ ∃ C : ℝ, 0 < C ∧ ∀ᶠ x in l,
      Q ≤ ‖w x‖ → |(z x).re| ≤ C*(1+Real.log ‖w x‖) := by
  let l' : Filter α := l ⊓ Filter.comap (fun x => ‖w x‖) atTop
  have hw : Tendsto (fun x => ‖w x‖) l' atTop := tendsto_comap.mono_left inf_le_right
  obtain ⟨C,hC,hstrip⟩ := exponential_ode_large_w_strip P hP index hinj
    (fun j => (hb j).mono_left (show l' ≤ l from inf_le_left)) hw
    (hbalance.filter_mono (show l' ≤ l from inf_le_left))
  obtain ⟨s,hs,t,ht,hst⟩ := Filter.eventually_inf.mp hstrip
  obtain ⟨Q,hQ⟩ := Filter.eventually_atTop.mp (Filter.eventually_comap.mp ht)
  refine ⟨max 1 Q,le_max_left _ _,C,hC,?_⟩
  filter_upwards [hs] with x hx hxw
  have hx1 : 1 ≤ ‖w x‖ := (le_max_left 1 Q).trans hxw
  have hxt : x ∈ t := hQ ‖w x‖ ((le_max_right 1 Q).trans hxw) x rfl
  simpa only [abs_of_nonneg (Real.log_nonneg hx1)] using hst x ⟨hx,hxt⟩

end LiWangWen

#print axioms LiWangWen.mem_exponentialDegreeSupport
#print axioms LiWangWen.exponentialDegreeSupport_nonempty
#print axioms LiWangWen.eval_eq_sum_exponentialDegreeSupport
#print axioms LiWangWen.polynomial_exponential_grouping
#print axioms LiWangWen.exists_group_max_index
#print axioms LiWangWen.exists_group_min_index
#print axioms LiWangWen.exponential_ode_large_w_strip
#print axioms LiWangWen.exponential_ode_small_w_strip
#print axioms LiWangWen.exponential_ode_large_w_strip_threshold
