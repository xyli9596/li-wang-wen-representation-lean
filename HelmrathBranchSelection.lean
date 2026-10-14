import HelmrathExceptionalSet
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Prod.Lex

/-!
# Selection of one asymptotic power branch

The selection argument uses monotonicity, finite separated candidate bands,
and good radii in each fixed relative interval. It does not assume continuity
of the central index, nor an already selected asymptotic branch.
-/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section

namespace HelmrathBranchSelection

/-- A monotone sequence taking values in a finite linear order stabilizes. -/
theorem finite_monotone_stabilizes {ι : Type*} [Fintype ι] [LinearOrder ι]
    (f : ℕ → ι) (hf : Monotone f) : ∃ N, ∀ n ≥ N, f n = f N := by
  let : Nonempty (Set.range f) := ⟨⟨f 0, Set.mem_range_self 0⟩⟩
  obtain ⟨i, hmax⟩ := Finite.exists_max (Subtype.val : Set.range f → ι)
  obtain ⟨N, hN⟩ := i.property
  refine ⟨N, fun n hn => le_antisymm ?_ (hf hn)⟩
  simpa only [hN] using hmax ⟨f n, Set.mem_range_self n⟩

/-- Arbitrarily large good radii can be chosen with uniformly bounded successive
ratios. The construction also records the geometric brackets explicitly. -/
theorem exists_geometric_good_radii {E : Set ℝ}
    (hE : LevinDensity.ZeroRadialDensity E) {a : ℝ} (ha : 1 < a) (R : ℝ) :
    ∃ B : ℝ, 0 < B ∧ R ≤ B ∧ ∃ s : ℕ → ℝ,
      (∀ n, B * a^n ≤ s n ∧ s n ≤ B * a^(n+1) ∧ s n ∉ E) ∧
      Monotone s ∧ Tendsto s atTop atTop := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (HelmrathExceptionalSet.exists_good_radius hE (by norm_num : (0 : ℝ) ≤ 1) ha)
  let B := max 1 (max R T)
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hBR : R ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hBT : T ≤ B := (le_max_right _ _).trans (le_max_right _ _)
  have hpower : ∀ n : ℕ, B ≤ B * a^n := fun n =>
    le_mul_of_one_le_right hBpos.le (one_le_pow₀ ha.le)
  have hex : ∀ n : ℕ, ∃ x : ℝ,
      B * a^n ≤ x ∧ x ≤ B * a^(n+1) ∧ x ∉ E := by
    intro n
    obtain ⟨x, hx, hxE⟩ := hT (B * a^n) (hBT.trans (hpower n))
    refine ⟨x, by simpa using hx.1, ?_, hxE⟩
    simpa only [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hx.2
  choose s hs using hex
  have hmono : Monotone s := monotone_nat_of_le_succ fun n =>
    (hs n).2.1.trans (hs (n+1)).1
  have hlim : Tendsto (fun n : ℕ => B * a^n) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt ha).const_mul_atTop hBpos
  exact ⟨B, hBpos, hBR, s, hs, hmono, tendsto_atTop_mono (fun n => (hs n).1) hlim⟩

/-- Two sufficiently close good radii cannot select decreasing branches when
the candidate bands are separated at the allowed radius ratio. -/
theorem branch_le_of_close_radii {ι : Type*} [LinearOrder ι]
    {ν : ℝ → ℝ} {lo hi : ι → ℝ → ℝ} {R a r s : ℝ} {i j : ι}
    (hν : MonotoneOn ν (Ioi 0))
    (hhi : ∀ k, MonotoneOn (hi k) (Ioi 0))
    (hsep : ∀ t ≥ R, ∀ k l, k < l → hi k (a*t) < lo l t)
    (hr : 0 < r) (hR : R ≤ r) (hrs : r ≤ s) (hs : s ≤ a*r)
    (hlo : lo i r ≤ ν r) (hup : ν s ≤ hi j s) : i ≤ j := by
  by_contra h
  have hji : j < i := lt_of_not_ge h
  have hspos : 0 < s := hr.trans_le hrs
  have harpos : 0 < a*r := hspos.trans_le hs
  have hu := hhi j hspos harpos hs
  have hv := hν hr hspos hrs
  have hgap := hsep r hR j i hji
  linarith

/-- Finite separated bands force eventual selection of one band outside a
zero-density set. The upper band functions may be discontinuous; only their
monotonicity is used. -/
theorem eventually_one_band {ι : Type*} [Fintype ι] [LinearOrder ι]
    {E : Set ℝ} {ν : ℝ → ℝ} {lo hi : ι → ℝ → ℝ} {R a : ℝ}
    (hE : LevinDensity.ZeroRadialDensity E) (ha : 1 < a)
    (hν : MonotoneOn ν (Ioi 0))
    (hhi : ∀ k, MonotoneOn (hi k) (Ioi 0))
    (hsep : ∀ r ≥ R, ∀ i j, i < j → hi i ((a*a)*r) < lo j r)
    (hband : ∀ r ≥ R, r ∉ E → ∃ i, lo i r ≤ ν r ∧ ν r ≤ hi i r) :
    ∃ i, ∀ᶠ r : ℝ in atTop, r ∉ E → lo i r ≤ ν r ∧ ν r ≤ hi i r := by
  obtain ⟨B, hBpos, hBR, s, hs, hmono, hlim⟩ :=
    exists_geometric_good_radii hE ha R
  have hBs : ∀ n, B ≤ s n := by
    intro n
    exact (le_mul_of_one_le_right hBpos.le (one_le_pow₀ ha.le)).trans (hs n).1
  have hspos : ∀ n, 0 < s n := fun n => hBpos.trans_le (hBs n)
  have hRs : ∀ n, R ≤ s n := fun n => hBR.trans (hBs n)
  have hstep : ∀ n, s (n+1) ≤ (a*a)*s n := by
    intro n
    calc
      s (n+1) ≤ B*a^(n+1+1) := (hs (n+1)).2.1
      _ = (a*a)*(B*a^n) := by ring
      _ ≤ (a*a)*s n := mul_le_mul_of_nonneg_left (hs n).1 (mul_self_nonneg a)
  choose k hk using fun n => hband (s n) (hRs n) (hs n).2.2
  have hkmono : Monotone k := monotone_nat_of_le_succ fun n =>
    branch_le_of_close_radii hν hhi hsep (hspos n) (hRs n)
      (hmono (Nat.le_succ n)) (hstep n) (hk n).1 (hk (n+1)).2
  obtain ⟨N, hN⟩ := finite_monotone_stabilizes k hkmono
  refine ⟨k N, ?_⟩
  filter_upwards [eventually_ge_atTop (s N)] with r hr hrE
  have hrpos : 0 < r := (hspos N).trans_le hr
  have hRr : R ≤ r := (hRs N).trans hr
  obtain ⟨j, hj⟩ := hband r hRr hrE
  have hex : ∃ m : ℕ, r < s m :=
    ((hlim.eventually (eventually_gt_atTop r)).exists)
  let m := Nat.find hex
  have hm : r < s m := Nat.find_spec hex
  have hmpos : 0 < m := by
    by_contra hm0
    have hmzero : m = 0 := Nat.eq_zero_of_not_pos hm0
    have h0N := hmono (Nat.zero_le N)
    rw [hmzero] at hm
    linarith
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hmpos)
  have hnle : s n ≤ r := by
    have hnm : n < Nat.find hex := by simpa only [m, hn] using Nat.lt_succ_self n
    exact le_of_not_gt (Nat.find_min hex hnm)
  have hNn : N ≤ n := by
    by_contra h
    have hmN : m ≤ N := by omega
    have := hmono hmN
    linarith
  have hmn : s m ≤ (a*a)*s n := by simpa only [hn] using hstep n
  have hjlow : k n ≤ j := branch_le_of_close_radii hν hhi hsep
    (hspos n) (hRs n) hnle (hm.le.trans hmn) (hk n).1 hj.2
  have hjhigh : j ≤ k m := branch_le_of_close_radii hν hhi hsep
    hrpos hRr hm.le (hmn.trans (mul_le_mul_of_nonneg_left hnle (mul_self_nonneg a)))
    hj.1 (hk m).2
  have hNm : N ≤ m := hNn.trans (by omega)
  rw [hN n hNn] at hjlow
  rw [hN m hNm] at hjhigh
  have hjeq : j = k N := le_antisymm hjhigh hjlow
  simpa only [hjeq] using hj


/-- Different real powers, with positive leading constants, are eventually
strictly ordered according to their exponents. -/
theorem eventually_power_lt_of_exponent_lt {p q C D : ℝ}
    (hpq : p < q) (hD : 0 < D) :
    ∀ᶠ r : ℝ in atTop, C * r^p < D * r^q := by
  have hlim := tendsto_rpow_atTop (sub_pos.mpr hpq)
  filter_upwards [hlim.eventually (eventually_gt_atTop (C / D)),
    eventually_gt_atTop (0 : ℝ)] with r hr hrpos
  rw [Real.rpow_sub hrpos] at hr
  have hpow : 0 < r^p := Real.rpow_pos_of_pos hrpos _
  have h := (div_lt_div_iff₀ hD hpow).mp hr
  nlinarith

/-- A finite lexicographically ordered collection of positive power branches
admits disjoint bands even after a small fixed enlargement of the radius.
The margin and radius enlargement are constructed, not assumed. -/
theorem exists_separated_power_bands {ι : Type*} [Fintype ι] [LinearOrder ι]
    (ρ c : ι → ℝ) (hc : ∀ i, 0 < c i)
    (horder : ∀ i j, i < j → ρ i < ρ j ∨ (ρ i = ρ j ∧ c i < c j)) :
    ∃ δ a : ℝ, 0 < δ ∧ 1 < a ∧ (∀ i, δ < c i) ∧
      ∀ᶠ r : ℝ in atTop, ∀ i j, i < j →
        (c i + δ) * ((a*a)*r)^(ρ i) < (c j - δ)*r^(ρ j) := by
  have hcoef : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, t < c i := by
    apply Filter.eventually_all.mpr
    intro i
    exact eventually_lt_nhds (hc i)
  have hequal : ∀ᶠ t : ℝ in 𝓝 0, ∀ i j, i < j → ρ i = ρ j →
      (c i+t)*((1+t)*(1+t))^(ρ i) < c j-t := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    by_cases hij : i < j
    · by_cases heq : ρ i = ρ j
      · have hcij : c i < c j := by
          rcases horder i j hij with h | h
          · exact False.elim ((ne_of_lt h) heq)
          · exact h.2
        have hcont : ContinuousAt (fun t : ℝ =>
            (c i+t)*((1+t)*(1+t))^(ρ i)) 0 := by
          apply ContinuousAt.mul
          · fun_prop
          · apply ContinuousAt.rpow_const
            · fun_prop
            · left
              norm_num
        have hcont2 : ContinuousAt (fun t : ℝ => c j-t) 0 := by fun_prop
        have hstrict := hcont.eventually_lt hcont2 (by simpa using hcij)
        filter_upwards [hstrict] with t ht _ _ using ht
      · exact Eventually.of_forall (fun _ _ h => (heq h).elim)
    · exact Eventually.of_forall (fun _ h _ => (hij h).elim)
  have hsmall := (hcoef.and hequal).filter_mono
    (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  obtain ⟨δ, hδpos, hδcoef, hδequal⟩ := (hpos.and hsmall).exists
  refine ⟨δ, 1+δ, hδpos, by linarith, hδcoef, ?_⟩
  apply Filter.eventually_all.mpr
  intro i
  apply Filter.eventually_all.mpr
  intro j
  by_cases hij : i < j
  · rcases horder i j hij with hlt | ⟨heq, _⟩
    · have hD : 0 < c j-δ := sub_pos.mpr (hδcoef j)
      have hh := eventually_power_lt_of_exponent_lt
        (C := (c i+δ)*((1+δ)*(1+δ))^(ρ i)) hlt hD
      filter_upwards [hh, eventually_gt_atTop (0 : ℝ)] with r hr hrpos _
      rw [Real.mul_rpow (mul_self_nonneg _) hrpos.le]
      simpa only [mul_assoc] using hr
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hrpos _
      have hh := mul_lt_mul_of_pos_right (hδequal i j hij heq)
        (Real.rpow_pos_of_pos hrpos (ρ i))
      rw [Real.mul_rpow (mul_self_nonneg _) hrpos.le]
      simpa only [heq, mul_assoc] using hh
  · exact Eventually.of_forall (fun _ h => (hij h).elim)

/-- Finite positive power approximations on good radii select a single branch.
Indices are ordered by exponent and then coefficient; this ordering concerns
only the fixed finite candidate list. -/
theorem exists_single_power_branch_zero_density
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    {E : Set ℝ} {ν : ℝ → ℝ} (ρ c : ι → ℝ)
    (hE : LevinDensity.ZeroRadialDensity E)
    (hν : MonotoneOn ν (Ioi 0)) (hρ : ∀ i, 0 ≤ ρ i) (hc : ∀ i, 0 < c i)
    (horder : ∀ i j, i < j → ρ i < ρ j ∨ (ρ i = ρ j ∧ c i < c j))
    (happrox : ∀ ε > 0, ∀ᶠ r : ℝ in atTop, r ∉ E →
      ∃ i, |ν r / r^(ρ i) - c i| < ε) :
    ∃ i, Tendsto (fun r : ℝ => ν r / r^(ρ i)) atTop (𝓝 (c i)) := by
  obtain ⟨δ, a, hδ, ha, hδc, hsep⟩ := exists_separated_power_bands ρ c hc horder
  obtain ⟨R, hR⟩ := eventually_atTop.mp
    ((hsep.and (happrox δ hδ)).and (eventually_gt_atTop (0 : ℝ)))
  let lo : ι → ℝ → ℝ := fun i r => (c i-δ)*r^(ρ i)
  let hi : ι → ℝ → ℝ := fun i r => (c i+δ)*r^(ρ i)
  have hhi : ∀ i, MonotoneOn (hi i) (Ioi 0) := by
    intro i r hr s hs hrs
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hr.le hrs (hρ i))
      (by linarith [hc i])
  have hseparation : ∀ r ≥ R, ∀ i j, i < j → hi i ((a*a)*r) < lo j r :=
    fun r hr => (hR r hr).1.1
  have hband : ∀ r ≥ R, r ∉ E → ∃ i, lo i r ≤ ν r ∧ ν r ≤ hi i r := by
    intro r hr hrE
    obtain ⟨i, hi⟩ := (hR r hr).1.2 hrE
    have hp := Real.rpow_pos_of_pos (hR r hr).2 (ρ i)
    have habs := abs_lt.mp hi
    refine ⟨i, ?_, ?_⟩
    · exact ((lt_div_iff₀ hp).mp (by linarith : c i-δ < ν r/r^(ρ i))).le
    · exact ((div_lt_iff₀ hp).mp (by linarith : ν r/r^(ρ i) < c i+δ)).le
  obtain ⟨i, hselected⟩ := eventually_one_band hE ha hν hhi hseparation hband
  have hgood : Tendsto (fun r : ℝ => ν r/r^(ρ i))
      (atTop ⊓ 𝓟 Eᶜ) (𝓝 (c i)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    rw [Filter.eventually_inf_principal]
    filter_upwards [hselected, happrox (min ε δ) (lt_min hε hδ),
      eventually_ge_atTop R] with r hir happ hr hrE
    obtain ⟨j, hj⟩ := happ hrE
    have hrpos := (hR r hr).2
    have hp := Real.rpow_pos_of_pos hrpos (ρ j)
    have hjδ := hj.trans_le (min_le_right ε δ)
    have habs := abs_lt.mp hjδ
    have hjband : lo j r ≤ ν r ∧ ν r ≤ hi j r := by
      constructor
      · exact ((lt_div_iff₀ hp).mp (by linarith : c j-δ < ν r/r^(ρ j))).le
      · exact ((div_lt_iff₀ hp).mp (by linarith : ν r/r^(ρ j) < c j+δ)).le
    have haa : r ≤ (a*a)*r := by nlinarith [sq_nonneg (a-1)]
    have hij : i ≤ j := branch_le_of_close_radii hν hhi hseparation
      hrpos hr le_rfl haa (hir hrE).1 hjband.2
    have hji : j ≤ i := branch_le_of_close_radii hν hhi hseparation
      hrpos hr le_rfl haa hjband.1 (hir hrE).2
    have heq : j = i := le_antisymm hji hij
    rw [heq] at hj
    simpa only [Real.dist_eq] using hj.trans_le (min_le_left ε δ)
  exact ⟨i, HelmrathExceptionalSet.remove_zero_density_exception hE hν (hρ i) (hc i) hgood⟩

/-- The finite-logarithmic-measure form used by the central-index argument. -/
theorem exists_single_power_branch
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    {E : Set ℝ} {ν : ℝ → ℝ} (ρ c : ι → ℝ)
    (hEm : MeasurableSet E) (hE : HelmrathExceptionalSet.FiniteLogarithmicMeasure E)
    (hν : MonotoneOn ν (Ioi 0)) (hρ : ∀ i, 0 ≤ ρ i) (hc : ∀ i, 0 < c i)
    (horder : ∀ i j, i < j → ρ i < ρ j ∨ (ρ i = ρ j ∧ c i < c j))
    (happrox : ∀ ε > 0, ∀ᶠ r : ℝ in atTop, r ∉ E →
      ∃ i, |ν r / r^(ρ i) - c i| < ε) :
    ∃ i, Tendsto (fun r : ℝ => ν r / r^(ρ i)) atTop (𝓝 (c i)) :=
  exists_single_power_branch_zero_density ρ c
    (HelmrathExceptionalSet.zero_density_of_finite_logarithmic_measure hEm hE)
    hν hρ hc horder happrox

/-- Unordered finite Newton-root candidates, with rational exponents, select one
actual global asymptotic. A lexicographic order is constructed internally. -/
theorem exists_single_power_branch_finset
    {E : Set ℝ} {ν : ℝ → ℝ} (C : Finset (ℚ × ℝ))
    (hEm : MeasurableSet E) (hE : HelmrathExceptionalSet.FiniteLogarithmicMeasure E)
    (hν : MonotoneOn ν (Ioi 0))
    (hC : ∀ p ∈ C, 0 < p.1 ∧ 0 < p.2)
    (happrox : ∀ ε > 0, ∀ᶠ r : ℝ in atTop ⊓ 𝓟 Eᶜ,
      ∃ p ∈ C, |ν r / r^(p.1 : ℝ) - p.2| < ε) :
    ∃ p ∈ C, Tendsto (fun r : ℝ => ν r / r^(p.1 : ℝ)) atTop (𝓝 p.2) := by
  classical
  let I := Lex {p // p ∈ C}
  let : Fintype I := Fintype.ofEquiv {p // p ∈ C} toLex
  let : LinearOrder I := LinearOrder.lift'
    (fun p : I => toLex (ofLex p).val)
    (toLex.injective.comp (Subtype.val_injective.comp ofLex.injective))
  let ρ : I → ℝ := fun p => (ofLex p).val.1
  let c : I → ℝ := fun p => (ofLex p).val.2
  have hρ : ∀ i, 0 ≤ ρ i := by
    intro i
    dsimp only [ρ]
    exact_mod_cast (hC (ofLex i).val (ofLex i).property).1.le
  have hc : ∀ i, 0 < c i := fun i => (hC (ofLex i).val (ofLex i).property).2
  have horder : ∀ i j : I, i < j →
      ρ i < ρ j ∨ (ρ i = ρ j ∧ c i < c j) := by
    intro i j hij
    change toLex (ofLex i).val < toLex (ofLex j).val at hij
    rcases Prod.Lex.toLex_lt_toLex.mp hij with h | ⟨h, hcij⟩
    · left
      dsimp only [ρ]
      exact_mod_cast h
    · exact Or.inr ⟨by dsimp only [ρ]; rw [h], hcij⟩
  have happ : ∀ ε > 0, ∀ᶠ r : ℝ in atTop, r ∉ E →
      ∃ i, |ν r / r^(ρ i) - c i| < ε := by
    intro ε hε
    have hh := Filter.eventually_inf_principal.mp (happrox ε hε)
    filter_upwards [hh] with r hr hrE
    obtain ⟨p, hp, hclose⟩ := hr hrE
    exact ⟨toLex ⟨p, hp⟩, hclose⟩
  obtain ⟨i, hi⟩ := exists_single_power_branch ρ c hEm hE hν hρ hc horder happ
  exact ⟨(ofLex i).val, (ofLex i).property, hi⟩

#print axioms finite_monotone_stabilizes
#print axioms exists_geometric_good_radii
#print axioms branch_le_of_close_radii
#print axioms eventually_one_band
#print axioms eventually_power_lt_of_exponent_lt
#print axioms exists_separated_power_bands
#print axioms exists_single_power_branch_zero_density
#print axioms exists_single_power_branch
#print axioms exists_single_power_branch_finset

end HelmrathBranchSelection
