import WimanValironComparisonSequence
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Weighted coefficient moments from quadratic exponential decay

The numerical estimates in this file convert genuine exponential decay to
summable power majorants. The constants depend on the fixed exponents, not on
the radius or the central index. No derivative or weighted-moment asymptotic
is assumed in these numerical estimates.

The final theorems use the actual normal-radius coefficient bounds to prove
summability and a uniform estimate for every fixed normalized moment.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Topology

namespace WimanValiron

/-- For positive `s`, the maximum of `x^s * exp (-x)` on the positive real axis. -/
def exponentialPowerConstant (s : ℝ) : ℝ := Real.exp (s * Real.log s - s)

theorem exponentialPowerConstant_pos (s : ℝ) : 0 < exponentialPowerConstant s :=
  Real.exp_pos _

/-- An exponential is bounded by every prescribed negative real power. -/
theorem exp_neg_le_power {s x : ℝ} (hs : 0 < s) (hx : 0 < x) :
    Real.exp (-x) ≤ exponentialPowerConstant s * x ^ (-s) := by
  have hlog := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hx hs)) hs.le
  rw [Real.log_div hx.ne' hs.ne'] at hlog
  have hdiv : s * (x/s - 1) = x-s := by field_simp
  rw [hdiv] at hlog
  calc
    Real.exp (-x) ≤ Real.exp (s*Real.log s-s + Real.log x*(-s)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    _ = exponentialPowerConstant s * x ^ (-s) := by
      rw [Real.exp_add, Real.rpow_def_of_pos hx]
      rfl

/-- A power times a stretched exponential has an explicit power majorant. -/
theorem weighted_stretched_exp_le_power (l : ℕ) {s c γ x : ℝ}
    (hs : 0 < s) (hc : 0 < c) (hx : 0 < x) :
    x ^ l * Real.exp (-(c * x ^ γ)) ≤
      (exponentialPowerConstant s * c ^ (-s)) * x ^ ((l : ℝ) - γ*s) := by
  calc
    x ^ l * Real.exp (-(c * x ^ γ)) ≤
        x ^ l * (exponentialPowerConstant s * (c * x ^ γ) ^ (-s)) :=
      mul_le_mul_of_nonneg_left (exp_neg_le_power hs (by positivity)) (by positivity)
    _ = (exponentialPowerConstant s * c ^ (-s)) * x ^ ((l : ℝ) - γ*s) := by
      rw [Real.mul_rpow hc.le (Real.rpow_nonneg hx.le _), ← Real.rpow_mul hx.le]
      rw [← Real.rpow_natCast]
      calc
        _ = (exponentialPowerConstant s * c ^ (-s)) *
            (x ^ (l : ℝ) * x ^ (γ * (-s))) := by ring
        _ = _ := by rw [← Real.rpow_add hx]; congr 2; ring

/-- Polynomially weighted stretched-exponential sequences are summable for
every positive stretch exponent, including exponents below one. -/
theorem summable_weighted_stretched_exp (l : ℕ) {c γ : ℝ}
    (hc : 0 < c) (hγ : 0 < γ) :
    Summable (fun k : ℕ => ((k+1 : ℕ) : ℝ)^l *
      Real.exp (-(c * ((k+1 : ℕ) : ℝ)^γ))) := by
  let s : ℝ := ((l : ℝ) + 2) / γ
  have hs : 0 < s := by dsimp [s]; positivity
  have he : (l : ℝ) - γ*s = -2 := by dsimp [s]; field_simp; ring
  have hp : Summable (fun k : ℕ => ((k+1 : ℕ) : ℝ)^(-2 : ℝ)) :=
    (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by norm_num))
  apply (hp.mul_left (exponentialPowerConstant s * c^(-s))).of_nonneg_of_le
    (fun _ => by positivity)
  intro k
  simpa only [he] using weighted_stretched_exp_le_power l (γ := γ) hs hc
    (show (0 : ℝ) < ((k+1 : ℕ) : ℝ) by positivity)

/-- A scaled Gaussian has a power majorant whose scale dependence is explicit. -/
theorem weighted_gaussian_le_power (l : ℕ) {s c α R x : ℝ}
    (hs : 0 < s) (hc : 0 < c) (hR : 0 < R) (hx : 0 < x) :
    x ^ l * Real.exp (-(c * x^2 * R^(-α))) ≤
      (exponentialPowerConstant s * c^(-s)) * R^(α*s) * x^((l : ℝ)-2*s) := by
  have h := weighted_stretched_exp_le_power l (γ := 2) hs
    (mul_pos hc (Real.rpow_pos_of_pos hR (-α))) hx
  calc
    _ = x ^ l * Real.exp (-((c * R^(-α)) * x^(2 : ℝ))) := by
      rw [Real.rpow_two]
      congr 2
      ring
    _ ≤ _ := h
    _ = _ := by
      rw [Real.mul_rpow hc.le (Real.rpow_nonneg hR.le _), ← Real.rpow_mul hR.le]
      rw [show (-α)*(-s) = α*s by ring]
      ring

/-- Exponential decay with denominator `(R+x)^α` splits into a Gaussian near
the center and a stretched exponential beyond it. -/
theorem right_kernel_power_majorant (l : ℕ) {α s : ℝ}
    (hα : 0 ≤ α) (hαtwo : α < 2) (hs : 0 < s) :
    ∃ C : ℝ, 0 < C ∧ ∀ R x : ℝ, 0 < R → 0 < x →
      x^l * Real.exp (-(x^2/2 * (R+x)^(-α))) ≤
        C * (R^(α*s) * x^((l : ℝ)-2*s) + x^(-2 : ℝ)) := by
  let c : ℝ := (2 : ℝ)^(-α)/2
  let t : ℝ := ((l : ℝ)+2)/(2-α)
  let A : ℝ := exponentialPowerConstant s * c^(-s)
  let B : ℝ := exponentialPowerConstant t * c^(-t)
  have hc : 0 < c := by dsimp [c]; positivity
  have ht : 0 < t := by dsimp [t]; positivity
  have hA : 0 < A := mul_pos (exponentialPowerConstant_pos _) (by positivity)
  have hB : 0 < B := mul_pos (exponentialPowerConstant_pos _) (by positivity)
  refine ⟨max A B, lt_of_lt_of_le hA (le_max_left _ _), ?_⟩
  intro R x hR hx
  by_cases hxR : x ≤ R
  · have hp : (2*R)^(-α) ≤ (R+x)^(-α) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hR.le] at hp
    have he : c*x^2*R^(-α) ≤ x^2/2*(R+x)^(-α) := by
      have := mul_le_mul_of_nonneg_left hp (show 0 ≤ x^2/2 by positivity)
      dsimp [c]
      nlinarith
    calc
      _ ≤ x^l * Real.exp (-(c*x^2*R^(-α))) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg he)) (by positivity)
      _ ≤ A * R^(α*s) * x^((l : ℝ)-2*s) :=
        weighted_gaussian_le_power l hs hc hR hx
      _ ≤ max A B * (R^(α*s) * x^((l : ℝ)-2*s) + x^(-2 : ℝ)) := by
        have hn : 0 ≤ R^(α*s) * x^((l : ℝ)-2*s) := by positivity
        have h := mul_le_mul_of_nonneg_right (le_max_left A B) hn
        have hz : 0 ≤ max A B * x^(-2 : ℝ) := by positivity
        nlinarith
  · have hp : (2*x)^(-α) ≤ (R+x)^(-α) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hx.le] at hp
    have hpow : x^(2-α) = x^2 * x^(-α) := by
      rw [sub_eq_add_neg, Real.rpow_add hx, Real.rpow_two]
    have he : c*x^(2-α) ≤ x^2/2*(R+x)^(-α) := by
      have := mul_le_mul_of_nonneg_left hp (show 0 ≤ x^2/2 by positivity)
      rw [hpow]
      dsimp [c]
      nlinarith
    have hexp : (l : ℝ) - (2-α)*t = -2 := by
      dsimp [t]
      field_simp [ne_of_gt (sub_pos.mpr hαtwo)]
      ring
    calc
      _ ≤ x^l * Real.exp (-(c*x^(2-α))) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg he)) (by positivity)
      _ ≤ B * x^(-2 : ℝ) := by
        simpa only [hexp] using weighted_stretched_exp_le_power l (γ := 2-α) ht hc hx
      _ ≤ max A B * (R^(α*s) * x^((l : ℝ)-2*s) + x^(-2 : ℝ)) := by
        have h := mul_le_mul_of_nonneg_right (le_max_right A B)
          (show 0 ≤ x^(-2 : ℝ) by positivity)
        have hz : 0 ≤ max A B * (R^(α*s) * x^((l : ℝ)-2*s)) := by positivity
        nlinarith

/-- A left Gaussian loses only a fixed factor when `k(k-1)` is replaced by
`k²/2`; this includes the adjacent coefficient. -/
theorem left_kernel_power_majorant (l : ℕ) {α s : ℝ}
    (hα : 0 ≤ α) (hs : 0 < s) :
    ∃ C : ℝ, 0 < C ∧ ∀ R x : ℝ, 1 ≤ R → 0 < x →
      x^l * Real.exp (-(x*(x-1)/2 * R^(-α))) ≤
        C * R^(α*s) * x^((l : ℝ)-2*s) := by
  refine ⟨Real.exp 1 * (exponentialPowerConstant s * (1/4 : ℝ)^(-s)),
    mul_pos (Real.exp_pos _) (mul_pos (exponentialPowerConstant_pos _) (by positivity)), ?_⟩
  intro R x hR hx
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hp : R^(-α) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hR (by linarith)
  have hbase : x^2/4-x*(x-1)/2 ≤ 1 := by nlinarith [sq_nonneg (x-1)]
  have hm := mul_le_mul_of_nonneg_right hbase (Real.rpow_nonneg hRp.le (-α))
  have he : -(x*(x-1)/2*R^(-α)) ≤ 1 - (1/4)*x^2*R^(-α) := by nlinarith
  calc
    _ ≤ x^l * Real.exp (1-(1/4)*x^2*R^(-α)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by positivity)
    _ = Real.exp 1 * (x^l * Real.exp (-((1/4)*x^2*R^(-α)))) := by
      rw [sub_eq_add_neg, Real.exp_add]
      ring
    _ ≤ Real.exp 1 * ((exponentialPowerConstant s * (1/4 : ℝ)^(-s)) *
        R^(α*s) * x^((l : ℝ)-2*s)) :=
      mul_le_mul_of_nonneg_left (weighted_gaussian_le_power l hs (by norm_num) hRp hx)
        (Real.exp_pos _).le
    _ = _ := by ring

/-- A summable majorant for the two tails, with value one at the center. -/
def momentPowerKernel (l : ℕ) (s : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 1 else (k : ℝ)^((l : ℝ)-2*s) + (k : ℝ)^(-2 : ℝ)

theorem momentPowerKernel_nonneg (l : ℕ) (s : ℝ) (k : ℕ) :
    0 ≤ momentPowerKernel l s k := by
  unfold momentPowerKernel
  split_ifs <;> positivity

theorem summable_momentPowerKernel (l : ℕ) {s : ℝ} (hs : (l : ℝ)+1 < 2*s) :
    Summable (momentPowerKernel l s) := by
  have hp : Summable (fun k : ℕ => (k : ℝ)^((l : ℝ)-2*s)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hq : Summable (fun k : ℕ => (k : ℝ)^(-2 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  apply (summable_nat_add_iff 1).mp
  simpa [momentPowerKernel] using (summable_nat_add_iff 1).mpr (hp.add hq)

/-- Combining a summable majorant on the two sides of an integer center costs
at most a factor two. No reindexing multiplicity is silently discarded. -/
theorem tsum_le_twice_of_two_sided {v w : ℕ → ℝ} (N : ℕ)
    (hv0 : ∀ n, 0 ≤ v n) (hw0 : ∀ n, 0 ≤ w n) (hw : Summable w)
    (hright : ∀ k, v (N+k) ≤ w k)
    (hleft : ∀ k ≤ N, v (N-k) ≤ w k) :
    Summable v ∧ (∑' n, v n) ≤ 2 * ∑' k, w k := by
  have htail : Summable (fun k => v (k+N)) :=
    hw.of_nonneg_of_le (fun k => hv0 _) (fun k => by simpa [add_comm] using hright k)
  have hv : Summable v := (summable_nat_add_iff N).mp htail
  refine ⟨hv, ?_⟩
  have hprefix : (∑ n ∈ Finset.range N, v n) ≤ ∑' k, w k := by
    calc
      _ ≤ ∑ n ∈ Finset.range (N+1), v n := by
        rw [Finset.sum_range_succ]
        exact le_add_of_nonneg_right (hv0 _)
      _ = ∑ k ∈ Finset.range (N+1), v (N-k) := by
        simpa using (Finset.sum_range_reflect v (N+1)).symm
      _ ≤ ∑ k ∈ Finset.range (N+1), w k := by
        apply Finset.sum_le_sum
        intro k hk
        exact hleft k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
      _ ≤ ∑' k, w k := hw.sum_le_tsum _ (fun k _ => hw0 k)
  have htailbound : (∑' k, v (k+N)) ≤ ∑' k, w k :=
    htail.tsum_le_tsum (fun k => by simpa [add_comm] using hright k) hw
  rw [← hv.sum_add_tsum_nat_add N]
  linarith

/-- Absolute coefficient moments at a normal radius, before dividing by the
central index. The exponent may be any `α*s` with `2*s > l+1`. -/
theorem normal_absolute_moment_bound (l : ℕ) {α s : ℝ}
    (hα : 0 ≤ α) (hαtwo : α < 2) (hs : 0 < s) (hcount : (l : ℝ)+1 < 2*s) :
    ∃ D : ℝ, 0 < D ∧ ∀ {a : ℕ → ℂ} {r : ℝ} {N : ℕ}, 1 ≤ N →
      NormalRadiusAt a (comparisonSequence α) r N → a N ≠ 0 →
      Summable (fun n : ℕ => |(n : ℝ)-(N : ℝ)|^l * term a r n) ∧
        (∑' n : ℕ, |(n : ℝ)-(N : ℝ)|^l * term a r n) ≤
          D * term a r N * (N : ℝ)^(α*s) := by
  obtain ⟨A, hA, hright⟩ := right_kernel_power_majorant l hα hαtwo hs
  obtain ⟨B, hB, hleft⟩ := left_kernel_power_majorant l hα hs
  let C : ℝ := max (max A B) 1
  have hC1 : 1 ≤ C := le_max_right _ _
  have hC : 0 < C := zero_lt_one.trans_le hC1
  have hAC : A ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hBC : B ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  have hkernel := summable_momentPowerKernel l hcount
  have hsumpos : 0 < ∑' k, momentPowerKernel l s k := by
    have hle := hkernel.sum_le_tsum ({0} : Finset ℕ)
      (fun k _ => momentPowerKernel_nonneg l s k)
    have : 1 ≤ ∑' k, momentPowerKernel l s k := by simpa [momentPowerKernel] using hle
    exact zero_lt_one.trans_le this
  refine ⟨2*C*(∑' k, momentPowerKernel l s k), by positivity, ?_⟩
  intro a r N hN1 hN haN
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNp : (0 : ℝ) < N := zero_lt_one.trans_le hNR
  have hterm : 0 < term a r N := term_pos hN.1 haN
  have hscale : 1 ≤ (N : ℝ)^(α*s) := Real.one_le_rpow hNR (mul_nonneg hα hs.le)
  let M : ℝ := C * term a r N * (N : ℝ)^(α*s)
  have hM : 0 < M := by dsimp [M]; positivity
  have hcenter : |(N : ℝ)-(N : ℝ)|^l * term a r N ≤
      M * momentPowerKernel l s 0 := by
    have hz : (0 : ℝ)^l ≤ 1 := by cases l <;> simp
    have hCt : term a r N ≤ C * term a r N := by nlinarith
    have hCM : C * term a r N ≤ M := by
      dsimp [M]
      nlinarith [mul_pos hC hterm]
    simpa [momentPowerKernel] using (mul_le_mul_of_nonneg_right hz hterm.le).trans
      (by simpa using hCt.trans hCM)
  have hright' : ∀ k, |((N+k : ℕ) : ℝ)-(N : ℝ)|^l * term a r (N+k) ≤
      M * momentPowerKernel l s k := by
    intro k
    by_cases hk : k = 0
    · simpa [hk] using hcenter
    have hkp : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
    have hratio := normal_right_gaussian hα hN haN k
    have hc := (div_le_iff₀ hterm).mp hratio
    have hexp : Real.exp (-((k : ℝ)*(k+1)/2)*((N+k : ℕ) : ℝ)^(-α)) ≤
        Real.exp (-((k : ℝ)^2/2*((N : ℝ)+k)^(-α))) := by
      apply Real.exp_le_exp.mpr
      push_cast
      have hp : 0 ≤ ((N : ℝ)+k)^(-α) := by positivity
      nlinarith
    have hnum := hright (N : ℝ) (k : ℝ) hNp hkp
    have hraw : (k : ℝ)^l * term a r (N+k) ≤
        term a r N * (A * ((N : ℝ)^(α*s) * (k : ℝ)^((l : ℝ)-2*s) +
          (k : ℝ)^(-2 : ℝ))) := by
      calc
        _ ≤ (k : ℝ)^l * (Real.exp (-((k : ℝ)^2/2*((N : ℝ)+k)^(-α))) *
            term a r N) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact hc.trans (mul_le_mul_of_nonneg_right hexp hterm.le)
        _ = term a r N * ((k : ℝ)^l *
            Real.exp (-((k : ℝ)^2/2*((N : ℝ)+k)^(-α)))) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hnum hterm.le
    have hmajor : A * ((N : ℝ)^(α*s) * (k : ℝ)^((l : ℝ)-2*s) + (k : ℝ)^(-2 : ℝ)) ≤
        C * (N : ℝ)^(α*s) * ((k : ℝ)^((l : ℝ)-2*s) + (k : ℝ)^(-2 : ℝ)) := by
      calc
        _ ≤ C * ((N : ℝ)^(α*s) * (k : ℝ)^((l : ℝ)-2*s) + (k : ℝ)^(-2 : ℝ)) :=
          mul_le_mul_of_nonneg_right hAC (by positivity)
        _ ≤ _ := by
          have hq := mul_le_mul_of_nonneg_right hscale
            (show 0 ≤ (k : ℝ)^(-2 : ℝ) by positivity)
          nlinarith
    have hfinal := hraw.trans (mul_le_mul_of_nonneg_left hmajor hterm.le)
    simpa [M, momentPowerKernel, hk, Nat.cast_add, abs_of_nonneg hkp.le,
      mul_assoc, mul_left_comm, mul_comm] using hfinal
  have hleft' : ∀ k ≤ N, |((N-k : ℕ) : ℝ)-(N : ℝ)|^l * term a r (N-k) ≤
      M * momentPowerKernel l s k := by
    intro k hkN
    by_cases hk : k = 0
    · simpa [hk] using hcenter
    have hkp : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
    have hNk : N-k+k = N := Nat.sub_add_cancel hkN
    have hratio := normal_left_gaussian (n := N-k) (k := k) hα
      (hNk.symm ▸ hN) (hNk.symm ▸ haN)
    rw [hNk] at hratio
    have hc := (div_le_iff₀ hterm).mp hratio
    have hnum := hleft (N : ℝ) (k : ℝ) hNR hkp
    have hraw : (k : ℝ)^l * term a r (N-k) ≤
        term a r N * (B * (N : ℝ)^(α*s) * (k : ℝ)^((l : ℝ)-2*s)) := by
      calc
        _ ≤ (k : ℝ)^l * (Real.exp (-((k : ℝ)*(k-1)/2)*((N : ℝ))^(-α)) *
            term a r N) := mul_le_mul_of_nonneg_left hc (by positivity)
        _ = term a r N * ((k : ℝ)^l * Real.exp (-((k : ℝ)*(k-1)/2*(N : ℝ)^(-α)))) := by
          simp only [neg_mul]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hnum hterm.le
    have hmajor : B * (N : ℝ)^(α*s) * (k : ℝ)^((l : ℝ)-2*s) ≤
        C * (N : ℝ)^(α*s) * ((k : ℝ)^((l : ℝ)-2*s)+(k : ℝ)^(-2 : ℝ)) := by
      have h := mul_le_mul_of_nonneg_right hBC
        (show 0 ≤ (N : ℝ)^(α*s) * (k : ℝ)^((l : ℝ)-2*s) by positivity)
      have hz : 0 ≤ C * (N : ℝ)^(α*s) * (k : ℝ)^(-2 : ℝ) := by positivity
      nlinarith
    have hfinal := hraw.trans (mul_le_mul_of_nonneg_left hmajor hterm.le)
    rw [Nat.cast_sub hkN]
    have heq : (N : ℝ)-(k : ℝ)-(N : ℝ) = -(k : ℝ) := by ring
    rw [heq, abs_neg, abs_of_nonneg hkp.le]
    simpa [M, momentPowerKernel, hk, mul_assoc, mul_left_comm, mul_comm] using hfinal
  have hboth := tsum_le_twice_of_two_sided N
    (v := fun n : ℕ => |(n : ℝ)-(N : ℝ)|^l * term a r n)
    (w := fun k => M * momentPowerKernel l s k)
    (fun n => mul_nonneg (pow_nonneg (abs_nonneg _) _) (term_nonneg a hN.1.le n))
    (fun k => mul_nonneg hM.le (momentPowerKernel_nonneg l s k))
    (hkernel.mul_left M) hright' hleft'
  refine ⟨hboth.1, ?_⟩
  calc
    _ ≤ 2 * ∑' k, M * momentPowerKernel l s k := hboth.2
    _ = (2*C*(∑' k, momentPowerKernel l s k)) * term a r N * (N : ℝ)^(α*s) := by
      rw [tsum_mul_left]
      dsimp [M]
      ring

/-- Every fixed normalized coefficient moment has the required power saving
at normal radii. The strict inequality `α/2 < β` absorbs the summation loss. -/
theorem normal_normalized_moment_bound (l : ℕ) {α β : ℝ}
    (hα : 0 < α) (hαtwo : α < 2) (hβ : α/2 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ {a : ℕ → ℂ} {r : ℝ} {N : ℕ}, 1 ≤ N →
      NormalRadiusAt a (comparisonSequence α) r N → a N ≠ 0 →
      Summable (fun n : ℕ => |(n : ℝ)/(N : ℝ)-1|^l * term a r n) ∧
        (∑' n : ℕ, |(n : ℝ)/(N : ℝ)-1|^l * term a r n) ≤
          C * term a r N * (N : ℝ)^(β*((l : ℝ)+1)-(l : ℝ)) := by
  let s : ℝ := β*((l : ℝ)+1)/α
  have hβpos : 0 < β := (by linarith : (0 : ℝ) < α/2).trans hβ
  have hs : 0 < s := by dsimp [s]; positivity
  have hscale : α*s = β*((l : ℝ)+1) := by dsimp [s]; field_simp
  have hcount : (l : ℝ)+1 < 2*s := by
    have hm := mul_lt_mul_of_pos_right hβ (show 0 < (l : ℝ)+1 by positivity)
    nlinarith
  obtain ⟨C, hC, hbound⟩ := normal_absolute_moment_bound l hα.le hαtwo hs hcount
  refine ⟨C, hC, ?_⟩
  intro a r N hN1 hN haN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨hraw, hrawbound⟩ := hbound hN1 hN haN
  have heq : (fun n : ℕ => |(n : ℝ)/(N : ℝ)-1|^l * term a r n) =
      (fun n : ℕ => (|(n : ℝ)-(N : ℝ)|^l * term a r n)/(N : ℝ)^l) := by
    funext n
    have hd : (n : ℝ)/(N : ℝ)-1 = ((n : ℝ)-(N : ℝ))/(N : ℝ) := by
      field_simp
    rw [hd, abs_div, abs_of_pos hNp, div_pow]
    ring
  rw [heq]
  refine ⟨hraw.div_const _, ?_⟩
  rw [tsum_div_const]
  calc
    _ ≤ (C * term a r N * (N : ℝ)^(α*s))/(N : ℝ)^l :=
      div_le_div_of_nonneg_right hrawbound (pow_nonneg hNp.le _)
    _ = C * term a r N * (N : ℝ)^(α*s-(l : ℝ)) := by
      rw [Real.rpow_sub hNp, Real.rpow_natCast]
      ring
    _ = _ := by rw [hscale]

end WimanValiron

#print axioms WimanValiron.exponentialPowerConstant_pos
#print axioms WimanValiron.exp_neg_le_power
#print axioms WimanValiron.weighted_stretched_exp_le_power
#print axioms WimanValiron.summable_weighted_stretched_exp
#print axioms WimanValiron.weighted_gaussian_le_power
#print axioms WimanValiron.right_kernel_power_majorant
#print axioms WimanValiron.left_kernel_power_majorant
#print axioms WimanValiron.momentPowerKernel_nonneg
#print axioms WimanValiron.summable_momentPowerKernel
#print axioms WimanValiron.tsum_le_twice_of_two_sided
#print axioms WimanValiron.normal_absolute_moment_bound
#print axioms WimanValiron.normal_normalized_moment_bound
