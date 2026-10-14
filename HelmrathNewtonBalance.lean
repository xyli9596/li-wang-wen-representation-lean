import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Tactic

/-!
# Newton balance for the central-index method

This is the dominant-term step used in the elementary Newton-diagram argument
of Helmrath and Nikolaus (1984), pp. 389--393. It does not assert the
Wiman--Valiron derivative estimate or the existence of a power asymptotic for
the central index. Those analytic steps remain separate obligations.

A finite vanishing sum of terms with nonzero power asymptotics cannot have a
unique largest exponent. For weights `degree(j) + j * (rho - 1)`, this forces
a rational candidate slope. Constant degrees force the candidate slope one.
-/

noncomputable section
open Filter Finset
open scoped Topology

namespace HelmrathNewtonBalance

/-- Raising the normalization exponent strictly makes the limit zero. -/
theorem tendsto_div_rpow_of_lt {u : ℝ → ℂ} {a b : ℝ} {c : ℂ}
    (hu : Tendsto (fun r => u r / (r ^ a : ℝ)) atTop (𝓝 c)) (hab : a < b) :
    Tendsto (fun r => u r / (r ^ b : ℝ)) atTop (𝓝 0) := by
  have hp : Tendsto (fun r : ℝ => (r ^ (a-b) : ℝ)) atTop (𝓝 0) := by
    simpa only [neg_sub] using tendsto_rpow_neg_atTop (sub_pos.mpr hab)
  have hpc : Tendsto (fun r : ℝ => ((r ^ (a-b) : ℝ) : ℂ)) atTop (𝓝 0) := by
    exact_mod_cast Complex.continuous_ofReal.continuousAt.tendsto.comp hp
  have h := hu.mul hpc
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  rw [Real.rpow_sub hr, Complex.ofReal_div]
  have ha : ((r ^ a : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos hr a).ne'
  field_simp

/-- A finite sum with a unique largest power has the corresponding nonzero
normalized limit; in particular it cannot vanish eventually. -/
theorem unique_max_not_eventually_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : ι → ℝ → ℂ) (w : ι → ℝ) (c : ι → ℂ) (i : ι)
    (hc : c i ≠ 0)
    (hu : ∀ j, Tendsto (fun r => u j r / (r ^ w j : ℝ)) atTop (𝓝 (c j)))
    (hw : ∀ j, j ≠ i → w j < w i) :
    ¬ (∀ᶠ r : ℝ in atTop, ∑ j, u j r = 0) := by
  intro hz
  have hlim : ∀ j, Tendsto (fun r => u j r / (r ^ w i : ℝ)) atTop
      (𝓝 (if j = i then c i else 0)) := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa using hu i
    · simpa [hji] using tendsto_div_rpow_of_lt (hu j) (hw j hji)
  have hsum := tendsto_finsetSum univ (fun j _ => hlim j)
  simp only [sum_ite_eq', mem_univ, if_true] at hsum
  have hzero : Tendsto (fun r => ∑ j, u j r / (r ^ w i : ℝ)) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hz] with r hr
    rw [← sum_div, hr, zero_div]
  exact hc (tendsto_nhds_unique hsum hzero)

/-- Every maximizing term in a vanishing sum has another term of the same weight. -/
theorem exists_other_max {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : ι → ℝ → ℂ) (w : ι → ℝ) (c : ι → ℂ) (i : ι)
    (hc : c i ≠ 0)
    (hu : ∀ j, Tendsto (fun r => u j r / (r ^ w j : ℝ)) atTop (𝓝 (c j)))
    (hw : ∀ j, w j ≤ w i)
    (hz : ∀ᶠ r : ℝ in atTop, ∑ j, u j r = 0) :
    ∃ j, j ≠ i ∧ w j = w i := by
  by_contra h
  apply unique_max_not_eventually_zero u w c i hc hu ?_ hz
  intro j hji
  exact lt_of_le_of_ne (hw j) (fun he => h ⟨j, hji, he⟩)

/-- The Newton weights relevant to an ODE after division by the solution. -/
def weight (degree : ℕ → ℤ) (ρ : ℝ) (j : ℕ) : ℝ :=
  degree j + (j : ℝ) * (ρ-1)

/-- Equal weights of two distinct derivative orders determine a rational slope. -/
theorem rational_of_equal_weights (degree : ℕ → ℤ) {ρ : ℝ} {i j : ℕ}
    (hij : i ≠ j) (h : weight degree ρ i = weight degree ρ j) :
    ∃ q : ℚ, ρ = q := by
  have hd : (i : ℝ) - (j : ℝ) ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hij)
  refine ⟨1 + ((degree j - degree i : ℤ) : ℚ) / ((i : ℚ) - (j : ℚ)), ?_⟩
  push_cast
  dsimp [weight] at h
  field_simp [hd]
  nlinarith

/-- If all participating coefficient degrees coincide, the only possible
balanced power is one. -/
theorem order_one_of_equal_degrees {degree : ℕ → ℤ} {ρ : ℝ} {i j : ℕ}
    (hij : i ≠ j) (hd : degree i = degree j)
    (h : weight degree ρ i = weight degree ρ j) : ρ = 1 := by
  have hn : (i : ℝ) ≠ (j : ℝ) := by exact_mod_cast hij
  dsimp [weight] at h
  rw [hd] at h
  have hm : ((i : ℝ) - j) * (ρ-1) = 0 := by nlinarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr hn))

/-- Rationality of a power exponent once a finite asymptotic balance has been
established. This does not assume rationality or a Newton slope as an input. -/
theorem rational_of_vanishing_sum {ι : Type*} [Fintype ι] [Nonempty ι]
    [DecidableEq ι] (u : ι → ℝ → ℂ) (index : ι → ℕ)
    (hi : Function.Injective index) (degree : ℕ → ℤ) (ρ : ℝ) (c : ι → ℂ)
    (hc : ∀ j, c j ≠ 0)
    (hu : ∀ j, Tendsto (fun r => u j r / (r ^ weight degree ρ (index j) : ℝ))
      atTop (𝓝 (c j)))
    (hz : ∀ᶠ r : ℝ in atTop, ∑ j, u j r = 0) : ∃ q : ℚ, ρ = q := by
  obtain ⟨i, _, hmax⟩ := exists_max_image univ (fun j => weight degree ρ (index j))
    univ_nonempty
  obtain ⟨j, hji, hw⟩ := exists_other_max u (fun j => weight degree ρ (index j)) c i
    (hc i) hu (fun j => hmax j (mem_univ j)) hz
  exact rational_of_equal_weights degree (fun hij => hji (hi hij).symm) hw.symm

/-- Constant polynomial degrees force exponent one in a genuine vanishing
asymptotic balance. Producing that balance from the ODE is a separate step. -/
theorem order_one_of_vanishing_sum {ι : Type*} [Fintype ι] [Nonempty ι]
    [DecidableEq ι] (u : ι → ℝ → ℂ) (index : ι → ℕ)
    (hi : Function.Injective index) (degree : ℕ → ℤ) (ρ : ℝ) (c : ι → ℂ)
    (hd : ∀ i j, degree (index i) = degree (index j))
    (hc : ∀ j, c j ≠ 0)
    (hu : ∀ j, Tendsto (fun r => u j r / (r ^ weight degree ρ (index j) : ℝ))
      atTop (𝓝 (c j)))
    (hz : ∀ᶠ r : ℝ in atTop, ∑ j, u j r = 0) : ρ = 1 := by
  obtain ⟨i, _, hmax⟩ := exists_max_image univ (fun j => weight degree ρ (index j))
    univ_nonempty
  obtain ⟨j, hji, hw⟩ := exists_other_max u (fun j => weight degree ρ (index j)) c i
    (hc i) hu (fun j => hmax j (mem_univ j)) hz
  exact order_one_of_equal_degrees (fun hij => hji (hi hij).symm) (hd i j) hw.symm

/-- Exact substitution of derivative comparison identities in a linear ODE.
This is formula (3) before replacing polynomial coefficients by their leading
terms. The derivative comparison itself is explicit input, not proved here. -/
theorem scaled_ode_identity {n : ℕ} {f : ℂ → ℂ} {z v : ℂ}
    (a ε : Fin (n+1) → ℂ) (hz : z ≠ 0) (hf : f z ≠ 0)
    (heq : ∑ j, a j * iteratedDeriv j.val f z = 0)
    (hjet : ∀ j : Fin (n+1), iteratedDeriv j.val f z =
      (v/z)^j.val * f z * (1+ε j)) :
    ∑ j : Fin (n+1), a j * z^(n-j.val) * v^j.val * (1+ε j) = 0 := by
  have term (j : Fin (n+1)) :
      a j * iteratedDeriv j.val f z * (z^n / f z) =
      a j * z^(n-j.val) * v^j.val * (1+ε j) := by
    rw [hjet j, div_pow]
    have hp : z^n = z^(n-j.val)*z^j.val := by
      rw [← pow_add, Nat.sub_add_cancel (Nat.le_of_lt_succ j.isLt)]
    rw [hp]
    field_simp
  calc
    ∑ j : Fin (n+1), a j * z^(n-j.val) * v^j.val * (1+ε j)
        = ∑ j : Fin (n+1), a j * iteratedDeriv j.val f z * (z^n / f z) := by
            apply sum_congr rfl
            intro j _
            exact (term j).symm
    _ = (∑ j : Fin (n+1), a j * iteratedDeriv j.val f z) * (z^n / f z) :=
      (sum_mul ..).symm
    _ = 0 := by rw [heq, zero_mul]

#print axioms tendsto_div_rpow_of_lt
#print axioms unique_max_not_eventually_zero
#print axioms exists_other_max
#print axioms rational_of_equal_weights
#print axioms order_one_of_equal_degrees
#print axioms rational_of_vanishing_sum
#print axioms order_one_of_vanishing_sum
#print axioms scaled_ode_identity

end HelmrathNewtonBalance
