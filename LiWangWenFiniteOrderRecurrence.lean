import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic
import HelmrathODECoefficients

/-!
# Rapidly decreasing sequences and polynomial recurrences

A sequence satisfying a finite recurrence whose coefficients grow at most
polynomially cannot have a nonzero tail decreasing faster than every power of
a factorial. This is the discrete rigidity step in a possible independent
proof of the representation theorem. The connection with Fourier coefficients
of the actual differential equation is not asserted in this module.
-/

set_option autoImplicit false
noncomputable section
open Filter Finset
open scoped Topology

namespace LiWangWen

/-- A sequence converging to zero cannot increase strictly to a later index
whenever its current value is positive. -/
theorem vanishing_tail_of_strict_future_increase {b : ℕ → ℝ} {M : ℕ}
    (hb : ∀ n, 0 ≤ b n) (hlim : Tendsto b atTop (𝓝 0))
    (hinc : ∀ n, M ≤ n → 0 < b n → ∃ m, n < m ∧ b n < b m) :
    ∀ n, M ≤ n → b n = 0 := by
  intro n hn
  by_contra hne
  have hnpos : 0 < b n := lt_of_le_of_ne (hb n) (Ne.symm hne)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually_lt_const hnpos)
  let S := Finset.Icc M (max n N)
  have hnS : n ∈ S := Finset.mem_Icc.mpr ⟨hn, le_max_left _ _⟩
  obtain ⟨k, hkS, hkmax⟩ := Finset.exists_max_image S b ⟨n, hnS⟩
  have hnk : b n ≤ b k := hkmax n hnS
  obtain ⟨m, hkm, hkmv⟩ := hinc k (Finset.mem_Icc.mp hkS).1 (hnpos.trans_le hnk)
  by_cases hmN : m ≤ max n N
  · have hmS : m ∈ S := Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hkS).1.trans hkm.le, hmN⟩
    exact (not_lt_of_ge (hkmax m hmS)) hkmv
  · have hNm : N ≤ m := (le_max_right n N).trans (le_of_not_ge hmN)
    exact (not_lt_of_ge (hnk.trans hkmv.le)) (hN m hNm)

/-- The factorial weight at any strictly later integer dominates the next
factorial weight. -/
theorem factorial_weight_future {n m K : ℕ} (hnm : n < m) :
    ((n : ℝ) + 1)^(K+1) * (n.factorial : ℝ)^(K+1) ≤
      (m.factorial : ℝ)^(K+1) := by
  rw [← mul_pow, ← Nat.cast_add_one, ← Nat.cast_mul, ← Nat.factorial_succ]
  exact pow_le_pow_left₀ (by positivity)
    (by exact_mod_cast Nat.factorial_le hnm) _

/-- A finite recurrence with polynomially bounded coefficients has no
nonzero tail whose corresponding factorial weight converges to zero.

The bound can be obtained by solving a polynomial recurrence for its first
coefficient. It permits any finite width, including zero. -/
theorem factorial_rapid_recurrence_eventually_zero
    {c : ℕ → ℂ} {K D M : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hrec : ∀ n, M ≤ n → ‖c n‖ ≤ C * ((n : ℝ)+1)^K *
      ∑ j ∈ Finset.range D, ‖c (n+j+1)‖)
    (hrapid : Tendsto (fun n => (n.factorial : ℝ)^(K+1) * ‖c n‖)
      atTop (𝓝 0)) :
    ∀ᶠ n in atTop, c n = 0 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (C * D)
  let b : ℕ → ℝ := fun n => (n.factorial : ℝ)^(K+1) * ‖c n‖
  have hb : ∀ n, 0 ≤ b n := by intro n; dsimp [b]; positivity
  have hzero := vanishing_tail_of_strict_future_increase (M := max M N) hb hrapid
    (fun n hn hnpos => ?_)
  · filter_upwards [eventually_ge_atTop (max M N)] with n hn
    have hz := hzero n hn
    dsimp [b] at hz
    have hfac : (n.factorial : ℝ)^(K+1) ≠ 0 := by positivity
    exact norm_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hfac)
  · by_contra h
    push Not at h
    have hnM : M ≤ n := (le_max_left _ _).trans hn
    have hnN : N ≤ n := (le_max_right _ _).trans hn
    have hcoeff : C * D < (n : ℝ)+1 := by
      have hnN' : (N : ℝ) ≤ n := by exact_mod_cast hnN
      linarith
    have hn1 : 0 < (n : ℝ)+1 := by positivity
    have hfac : 0 < (n.factorial : ℝ)^(K+1) := by positivity
    have hcn : 0 < ‖c n‖ := (mul_pos_iff_of_pos_left hfac).mp hnpos
    have hfuture (j : ℕ) : ((n : ℝ)+1)^(K+1) * ‖c (n+j+1)‖ ≤ ‖c n‖ := by
      have hnm : n < n+j+1 := by omega
      have hw := factorial_weight_future (K := K) hnm
      have hbnd := h (n+j+1) hnm
      dsimp [b] at hbnd
      have hmul := (mul_le_mul_of_nonneg_right hw (norm_nonneg _)).trans hbnd
      apply le_of_mul_le_mul_left _ hfac
      calc
        (n.factorial : ℝ)^(K+1) * (((n : ℝ)+1)^(K+1) * ‖c (n+j+1)‖) =
            (((n : ℝ)+1)^(K+1) * (n.factorial : ℝ)^(K+1)) * ‖c (n+j+1)‖ := by ring
        _ ≤ _ := hmul
    have hsum : ((n : ℝ)+1)^(K+1) *
        (∑ j ∈ Finset.range D, ‖c (n+j+1)‖) ≤ (D : ℝ) * ‖c n‖ := by
      rw [Finset.mul_sum]
      simpa using Finset.sum_le_sum (s := Finset.range D)
        (fun j _ => hfuture j)
    have hupper := mul_le_mul_of_nonneg_left (hrec n hnM)
      (pow_nonneg hn1.le (K+1))
    have hbound := mul_le_mul_of_nonneg_left hsum
      (mul_nonneg hC (pow_nonneg hn1.le K))
    have hpow : 0 < ((n : ℝ)+1)^K := pow_pos hn1 K
    have hcancel : ((n : ℝ)+1)^(K+1) * ‖c n‖ ≤
        C * ((n : ℝ)+1)^K * ((D : ℝ)*‖c n‖) := by
      calc
        _ ≤ _ := hupper
        _ = C * ((n : ℝ)+1)^K * (((n : ℝ)+1)^(K+1) *
            ∑ j ∈ Finset.range D, ‖c (n+j+1)‖) := by ring
        _ ≤ _ := hbound
    rw [pow_succ] at hcancel
    have hcancel' : ((n : ℝ)+1) * ‖c n‖ ≤ (C * D)*‖c n‖ := by
      apply le_of_mul_le_mul_left _ hpow
      nlinarith [hcancel]
    exact (not_le_of_gt (mul_lt_mul_of_pos_right hcoeff hcn)) hcancel'

/-- Every complex polynomial has a uniform coefficient-sum bound on the
nonnegative integer axis. -/
theorem polynomial_nat_norm_bound (p : Polynomial ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      ‖p.eval (n : ℂ)‖ ≤ C * ((n : ℝ)+1)^p.natDegree := by
  classical
  let C : ℝ := ∑ j ∈ Finset.range (p.natDegree+1), ‖p.coeff j‖
  refine ⟨C, Finset.sum_nonneg (fun j _ => norm_nonneg _), fun n => ?_⟩
  rw [Polynomial.eval_eq_sum_range]
  calc
    ‖∑ j ∈ Finset.range (p.natDegree+1), p.coeff j * (n : ℂ)^j‖ ≤
        ∑ j ∈ Finset.range (p.natDegree+1), ‖p.coeff j * (n : ℂ)^j‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range (p.natDegree+1), ‖p.coeff j‖ * ((n : ℝ)+1)^p.natDegree := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul, norm_pow, Complex.norm_natCast]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      calc
        (n : ℝ)^j ≤ ((n : ℝ)+1)^j := pow_le_pow_left₀ (by positivity) (by linarith) _
        _ ≤ ((n : ℝ)+1)^p.natDegree := pow_le_pow_right₀ (by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith)
          (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj)
    _ = C * ((n : ℝ)+1)^p.natDegree := (Finset.sum_mul _ _ _).symm

/-- A nonzero polynomial is bounded away from zero on a sufficiently late
part of the nonnegative integer axis. -/
theorem polynomial_nat_eventually_norm_lower {p : Polynomial ℂ} (hp : p ≠ 0) :
    ∃ a : ℝ, 0 < a ∧ ∀ᶠ n : ℕ in atTop, a ≤ ‖p.eval (n : ℂ)‖ := by
  have hlim := HelmrathODE.polynomial_normalized_tendsto p hp
    (z := fun n : ℕ => (n : ℂ))
    (by simpa only [Complex.norm_natCast] using
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))
  have hlc : 0 < ‖p.leadingCoeff‖ :=
    norm_pos_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hp)
  let a := ‖p.leadingCoeff‖ / 2
  have ha : 0 < a := by dsimp [a]; positivity
  refine ⟨a, ha, ?_⟩
  filter_upwards [hlim.norm.eventually_const_lt (show a < ‖p.leadingCoeff‖ by dsimp [a]; linarith),
    eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hnorm : ‖p.eval (n : ℂ)‖ / (n : ℝ)^p.natDegree > a := by
    simpa only [norm_div, norm_pow, Complex.norm_natCast] using hn
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hpw : 1 ≤ (n : ℝ)^p.natDegree := one_le_pow₀ hnreal
  have hprod := (lt_div_iff₀ (zero_lt_one.trans_le hpw)).mp hnorm
  exact (le_mul_of_one_le_right ha.le hpw).trans hprod.le

/-- Polynomial recurrences force the forward norm inequality used by the
factorial maximum principle. -/
theorem polynomial_recurrence_norm_bound {c : ℕ → ℂ} {D M : ℕ}
    (p : Polynomial ℂ) (q : Fin D → Polynomial ℂ) (hp : p ≠ 0)
    (hrec : ∀ n, M ≤ n → p.eval (n : ℂ) * c n +
      ∑ j : Fin D, (q j).eval (n : ℂ) * c (n+j.val+1) = 0) :
    ∃ K : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      ‖c n‖ ≤ C * ((n : ℝ)+1)^K *
        ∑ j ∈ Finset.range D, ‖c (n+j+1)‖ := by
  classical
  choose A hA hbound using fun j => polynomial_nat_norm_bound (q j)
  let K := Finset.univ.sup (fun j : Fin D => (q j).natDegree)
  let B := ∑ j : Fin D, A j
  have hB : 0 ≤ B := Finset.sum_nonneg (fun j _ => hA j)
  have hAj (j : Fin D) : A j ≤ B := Finset.single_le_sum
    (fun k _ => hA k) (Finset.mem_univ j)
  obtain ⟨a, ha, hlow⟩ := polynomial_nat_eventually_norm_lower hp
  obtain ⟨N, hN⟩ := eventually_atTop.mp hlow
  refine ⟨K, B/a, div_nonneg hB ha.le, max M N, fun n hn => ?_⟩
  have hbound' (j : Fin D) : ‖(q j).eval (n : ℂ)‖ ≤ B * ((n : ℝ)+1)^K := by
    calc
      _ ≤ A j * ((n : ℝ)+1)^(q j).natDegree := hbound j n
      _ ≤ B * ((n : ℝ)+1)^K := by
        apply mul_le_mul (hAj j)
        · exact pow_le_pow_right₀ (by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith)
            (Finset.le_sup (f := fun j : Fin D => (q j).natDegree) (Finset.mem_univ j))
        · positivity
        · exact hB
  have heq : p.eval (n : ℂ) * c n =
      -(∑ j : Fin D, (q j).eval (n : ℂ) * c (n+j.val+1)) := by
    linear_combination hrec n ((le_max_left _ _).trans hn)
  have hsum : a * ‖c n‖ ≤ B * ((n : ℝ)+1)^K *
      ∑ j ∈ Finset.range D, ‖c (n+j+1)‖ := by
    calc
      _ ≤ ‖p.eval (n : ℂ)‖ * ‖c n‖ :=
        mul_le_mul_of_nonneg_right (hN n ((le_max_right _ _).trans hn)) (norm_nonneg _)
      _ = ‖∑ j : Fin D, (q j).eval (n : ℂ) * c (n+j.val+1)‖ := by
        rw [← norm_mul, heq, norm_neg]
      _ ≤ ∑ j : Fin D, ‖(q j).eval (n : ℂ) * c (n+j.val+1)‖ := norm_sum_le _ _
      _ ≤ ∑ j : Fin D, (B * ((n : ℝ)+1)^K) * ‖c (n+j.val+1)‖ := by
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hbound' j) (norm_nonneg _)
      _ = _ := by
        rw [← Finset.mul_sum]
        congr 1
        exact Fin.sum_univ_eq_sum_range (fun j => ‖c (n+j+1)‖) D
  apply le_of_mul_le_mul_left _ ha
  calc
    a * ‖c n‖ ≤ B * ((n : ℝ)+1)^K *
        ∑ j ∈ Finset.range D, ‖c (n+j+1)‖ := hsum
    _ = a * (B/a * ((n : ℝ)+1)^K *
        ∑ j ∈ Finset.range D, ‖c (n+j+1)‖) := by field_simp

/-- A superfactorially decreasing solution of an eventual polynomial
recurrence has finite support. No order or limiting-ratio assumption is used. -/
theorem polynomial_recurrence_eventually_zero {c : ℕ → ℂ} {D M : ℕ}
    (p : Polynomial ℂ) (q : Fin D → Polynomial ℂ) (hp : p ≠ 0)
    (hrec : ∀ n, M ≤ n → p.eval (n : ℂ) * c n +
      ∑ j : Fin D, (q j).eval (n : ℂ) * c (n+j.val+1) = 0)
    (hrapid : ∀ K : ℕ, Tendsto (fun n => (n.factorial : ℝ)^K * ‖c n‖)
      atTop (𝓝 0)) :
    ∀ᶠ n in atTop, c n = 0 := by
  obtain ⟨K, C, hC, N, hN⟩ := polynomial_recurrence_norm_bound p q hp hrec
  exact factorial_rapid_recurrence_eventually_zero hC hN (hrapid (K+1))

/-- Reflecting a finite polynomial recurrence turns its rightmost
coefficient into the first coefficient of a forward recurrence. -/
theorem integer_polynomial_recurrence_positive_tail {c : ℤ → ℂ} {D M : ℕ}
    (Q : ℕ → Polynomial ℂ) (hQ : Q D ≠ 0)
    (hrec : ∀ m : ℤ, (M : ℤ) ≤ |m| → ∑ d ∈ Finset.range (D+1),
      (Q d).eval ((m-d : ℤ) : ℂ) * c (m-d) = 0)
    (hrapid : ∀ K : ℕ, Tendsto (fun n : ℕ => (n.factorial : ℝ)^K * ‖c n‖)
      atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop, c n = 0 := by
  let q : Fin D → Polynomial ℂ := fun j =>
    (Q (D-(j.val+1))).comp (Polynomial.X + Polynomial.C ((j.val+1 : ℕ) : ℂ))
  apply polynomial_recurrence_eventually_zero (c := fun n => c n)
    (M := M) (Q D) q hQ _ hrapid
  intro n hn
  have h := hrec ((n+D : ℕ) : ℤ) (by
    rw [abs_of_nonneg (by positivity)]
    exact_mod_cast (show M ≤ n+D by omega))
  rw [← Finset.sum_range_reflect _ (D+1)] at h
  have heq : (∑ j ∈ Finset.range (D+1),
      (Q (D+1-1-j)).eval (((((n+D : ℕ) : ℤ) - ((D+1-1-j : ℕ) : ℤ)) : ℤ) : ℂ) *
        c (((n+D : ℕ) : ℤ) - ((D+1-1-j : ℕ) : ℤ))) =
      ∑ j ∈ Finset.range (D+1), (Q (D-j)).eval ((n+j : ℕ) : ℂ)*c ((n+j : ℕ) : ℤ) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjD : j ≤ D := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
    have he : (((n+D : ℕ) : ℤ) - ((D+1-1-j : ℕ) : ℤ)) = ((n+j : ℕ) : ℤ) := by omega
    rw [he]
    simp only [Nat.add_sub_cancel, Int.cast_natCast]
  rw [heq, Finset.sum_range_succ'] at h
  simp only [Nat.sub_zero, Nat.add_zero] at h
  have heq' : (∑ j : Fin D, (q j).eval (n : ℂ) * c ((n+j.val+1 : ℕ) : ℤ)) =
      ∑ j ∈ Finset.range D, (Q (D-(j+1))).eval ((n+(j+1) : ℕ) : ℂ)*c ((n+(j+1) : ℕ) : ℤ) := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [q, Polynomial.eval_comp, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_C, Nat.cast_add, Nat.cast_one, add_assoc]
  rw [heq']
  linear_combination h

/-- Reversing the integer axis turns the leftmost coefficient of a
polynomial recurrence into a forward recurrence. -/
theorem integer_polynomial_recurrence_negative_tail {c : ℤ → ℂ} {D M : ℕ}
    (Q : ℕ → Polynomial ℂ) (hQ : Q 0 ≠ 0)
    (hrec : ∀ m : ℤ, (M : ℤ) ≤ |m| → ∑ d ∈ Finset.range (D+1),
      (Q d).eval ((m-d : ℤ) : ℂ) * c (m-d) = 0)
    (hrapid : ∀ K : ℕ, Tendsto (fun n : ℕ => (n.factorial : ℝ)^K * ‖c (-(n : ℤ))‖)
      atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop, c (-(n : ℤ)) = 0 := by
  let p := (Q 0).comp (-Polynomial.X)
  let q : Fin D → Polynomial ℂ := fun j =>
    (Q (j.val+1)).comp (-Polynomial.X - Polynomial.C ((j.val+1 : ℕ) : ℂ))
  have hp : p ≠ 0 := by simpa only [p, Ne, Polynomial.comp_neg_X_eq_zero_iff] using hQ
  apply polynomial_recurrence_eventually_zero (c := fun n => c (-(n : ℤ)))
    (M := M) p q hp _ hrapid
  intro n hn
  have h := hrec (-(n : ℤ)) (by
    rw [abs_neg, abs_of_nonneg (by positivity)]
    exact_mod_cast hn)
  rw [Finset.sum_range_succ'] at h
  simp only [Nat.cast_zero, sub_zero] at h
  have hp' : p.eval (n : ℂ) = (Q 0).eval (-(n : ℤ) : ℂ) := by simp [p]
  have hq' : (∑ j : Fin D, (q j).eval (n : ℂ)*c (-((n+j.val+1 : ℕ) : ℤ))) =
      ∑ j ∈ Finset.range D, (Q (j+1)).eval (((-(n : ℤ))-(j+1)) : ℂ) *
        c (-(n : ℤ)-(j+1)) := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [q, Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_neg,
      Polynomial.eval_X, Polynomial.eval_C, Nat.cast_add, Nat.cast_one, Int.cast_natCast]
    congr 1
    congr 1
    ring
  rw [hp', hq']
  push_cast at h
  linear_combination h

/-- A bilateral polynomial recurrence with nonzero endpoint polynomials
and superfactorial decay on both sides has finite support. -/
theorem integer_polynomial_recurrence_finite_support {c : ℤ → ℂ} {D M : ℕ}
    (Q : ℕ → Polynomial ℂ) (hQ0 : Q 0 ≠ 0) (hQD : Q D ≠ 0)
    (hrec : ∀ m : ℤ, (M : ℤ) ≤ |m| → ∑ d ∈ Finset.range (D+1),
      (Q d).eval ((m-d : ℤ) : ℂ) * c (m-d) = 0)
    (hplus : ∀ K : ℕ, Tendsto (fun n : ℕ => (n.factorial : ℝ)^K * ‖c n‖) atTop (𝓝 0))
    (hminus : ∀ K : ℕ, Tendsto (fun n : ℕ => (n.factorial : ℝ)^K * ‖c (-(n : ℤ))‖)
      atTop (𝓝 0)) :
    ∃ N : ℕ, ∀ m : ℤ, (N : ℤ) ≤ |m| → c m = 0 := by
  obtain ⟨A, hA⟩ := eventually_atTop.mp
    (integer_polynomial_recurrence_positive_tail Q hQD hrec hplus)
  obtain ⟨B, hB⟩ := eventually_atTop.mp
    (integer_polynomial_recurrence_negative_tail Q hQ0 hrec hminus)
  refine ⟨max A B, fun m hm => ?_⟩
  cases m with
  | ofNat n =>
    apply hA n
    have hn : max A B ≤ n := by
      simpa using hm
    exact (le_max_left _ _).trans hn
  | negSucc n =>
    have heq : Int.negSucc n = -((n+1 : ℕ) : ℤ) := by omega
    rw [heq]
    apply hB (n+1)
    have hn : max A B ≤ n+1 := by
      rw [heq, abs_neg, abs_of_nonneg (by positivity)] at hm
      exact_mod_cast hm
    exact (le_max_right _ _).trans hn

end LiWangWen

#print axioms LiWangWen.vanishing_tail_of_strict_future_increase
#print axioms LiWangWen.factorial_weight_future
#print axioms LiWangWen.factorial_rapid_recurrence_eventually_zero
#print axioms LiWangWen.polynomial_nat_norm_bound
#print axioms LiWangWen.polynomial_nat_eventually_norm_lower
#print axioms LiWangWen.polynomial_recurrence_norm_bound
#print axioms LiWangWen.polynomial_recurrence_eventually_zero
#print axioms LiWangWen.integer_polynomial_recurrence_positive_tail
#print axioms LiWangWen.integer_polynomial_recurrence_negative_tail
#print axioms LiWangWen.integer_polynomial_recurrence_finite_support
