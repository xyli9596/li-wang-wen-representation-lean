import LiWangWenWimanValironLower

/-!
# Extreme-frequency equations at displaced Wiman--Valiron points

The smallest nonzero derivative power is removed before taking a limit.
Consequently the endpoint polynomial has a nonzero constant coefficient.
Only a linear upper bound for the central index is used in the angular
displacement estimates; no lower growth bound or representation theorem is used.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
open Filter Finset Polynomial
open scoped Topology

namespace LiWangWen

/-- The polynomial obtained after removing the smallest nonzero power. -/
def endpointPolynomial {n : ℕ} (c : Fin (n+1) → ℂ) (m : ℕ) : Polynomial ℂ :=
  ∑ j, Polynomial.C (c j)*Polynomial.X^(j.val-m)

theorem endpointPolynomial_eval {n : ℕ} (c : Fin (n+1) → ℂ) (m : ℕ) (w : ℂ) :
    (endpointPolynomial c m).eval w = ∑ j, c j*w^(j.val-m) := by
  simp only [endpointPolynomial,eval_finsetSum,eval_mul,eval_C,eval_pow,eval_X]

theorem endpointPolynomial_eval_zero {n : ℕ} (c : Fin (n+1) → ℂ)
    (i₀ : Fin (n+1)) (hmin : ∀ j, c j ≠ 0 → i₀.val ≤ j.val) :
    (endpointPolynomial c i₀.val).eval 0 = c i₀ := by
  rw [endpointPolynomial_eval]
  have he : c i₀ * (0 : ℂ)^(i₀.val-i₀.val) = c i₀ := by simp
  rw [← he]
  apply Finset.sum_eq_single i₀
  · intro j _ hj
    by_cases hc : c j = 0
    · simp [hc]
    · have hij := hmin j hc
      have hne : j.val ≠ i₀.val := fun h => hj (Fin.ext h)
      have hpos : 0 < j.val-i₀.val := Nat.sub_pos_of_lt (lt_of_le_of_ne hij hne.symm)
      simp [Nat.ne_of_gt hpos]
  · simp

theorem endpointPolynomial_ne_zero {n : ℕ} (c : Fin (n+1) → ℂ)
    (i₀ : Fin (n+1)) (hc : c i₀ ≠ 0)
    (hmin : ∀ j, c j ≠ 0 → i₀.val ≤ j.val) :
    endpointPolynomial c i₀.val ≠ 0 := by
  intro h
  have he := endpointPolynomial_eval_zero c i₀ hmin
  rw [h,eval_zero] at he
  exact hc he.symm

/-- The endpoint product excludes the zero logarithmic derivative. -/
theorem endpoint_product_eval_zero_ne {n D : ℕ}
    (c : Fin (n+1) → Fin (D+1) → ℂ) (i₀ iD : Fin (n+1))
    (hc0 : c i₀ 0 ≠ 0) (hcD : c iD (Fin.last D) ≠ 0)
    (hmin0 : ∀ j, c j 0 ≠ 0 → i₀.val ≤ j.val)
    (hminD : ∀ j, c j (Fin.last D) ≠ 0 → iD.val ≤ j.val) :
    ((endpointPolynomial (fun j => c j 0) i₀.val)*
      endpointPolynomial (fun j => c j (Fin.last D)) iD.val).eval 0 ≠ 0 := by
  rw [eval_mul,endpointPolynomial_eval_zero _ _ hmin0,
    endpointPolynomial_eval_zero _ _ hminD]
  exact mul_ne_zero hc0 hcD

/-- Multiplication by a bounded factor preserves a zero limit. -/
theorem endpoint_zero_mul_bounded {α : Type*} {l : Filter α}
    {u v : α → ℂ} {K : ℝ} (hu : Tendsto u l (𝓝 0))
    (hv : ∀ᶠ x in l, ‖v x‖ ≤ K) :
    Tendsto (fun x => u x*v x) l (𝓝 0) := by
  have hb : l.IsBoundedUnder (· ≤ ·) (norm ∘ v) :=
    isBoundedUnder_of_eventually_le hv
  have h := NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded hu hb
  convert h using 1
  funext x
  exact (smul_eq_mul (u x) (v x)).symm

/-- WV perturbations do not change a normalized endpoint polynomial on a
bounded nonzero logarithmic-derivative path. -/
theorem endpoint_perturbation_tendsto_zero {α : Type*} {n : ℕ}
    {l : Filter α} (c : Fin (n+1) → ℂ) (i₀ : Fin (n+1))
    (hmin : ∀ j, c j ≠ 0 → i₀.val ≤ j.val)
    {w : α → ℂ} {a : α → Fin (n+1) → ℂ} {K : ℝ} (_hK : 0 ≤ K)
    (hw : ∀ᶠ x in l, ‖w x‖ ≤ K) (hwne : ∀ᶠ x in l, w x ≠ 0)
    (ha : ∀ j, Tendsto (fun x => a x j) l (𝓝 1)) :
    Tendsto (fun x =>
      (∑ j, c j*a x j*(w x)^j.val)/(w x)^i₀.val -
        (endpointPolynomial c i₀.val).eval (w x)) l (𝓝 0) := by
  have ht (j : Fin (n+1)) : Tendsto (fun x =>
      c j*(a x j-1)*(w x)^(j.val-i₀.val)) l (𝓝 0) := by
    have hz : Tendsto (fun x => c j*(a x j-1)) l (𝓝 0) := by
      simpa using (ha j).sub_const (1 : ℂ) |>.const_mul (c j)
    exact endpoint_zero_mul_bounded hz (by
      filter_upwards [hw] with x hx
      simpa only [norm_pow] using pow_le_pow_left₀ (norm_nonneg _) hx (j.val-i₀.val))
  have hh := tendsto_finsetSum Finset.univ (fun j _ => ht j)
  simp only [Finset.sum_const_zero] at hh
  apply hh.congr'
  filter_upwards [hwne] with x hx
  rw [endpointPolynomial_eval, Finset.sum_div, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hc : c j = 0
  · simp [hc]
  · have hpow : (w x)^j.val = (w x)^(j.val-i₀.val)*(w x)^i₀.val := by
      rw [← pow_add, Nat.sub_add_cancel (hmin j hc)]
    rw [hpow]
    field_simp [hx]

/-- Exponential decay absorbs a bounded polynomial numerator, even after
normalization by a fixed power of a logarithmic derivative as small as `1/r`. -/
theorem endpoint_positive_frequency_tendsto_zero {α : Type*}
    {l : Filter α} {r : α → ℝ} {z w a : α → ℂ} {K : ℝ} (_hK : 0 ≤ K)
    (hr : Tendsto r l atTop)
    (hwlo : ∀ᶠ x in l, 1/r x ≤ ‖w x‖)
    (hwup : ∀ᶠ x in l, ‖w x‖ ≤ K)
    (hz : ∀ᶠ x in l, (z x).re ≤ -(r x)^((1 : ℝ)/8)/8)
    (ha : Tendsto a l (𝓝 1)) (j m : ℕ) :
    Tendsto (fun x => Complex.exp (z x)*a x*(w x)^j/(w x)^m)
      l (𝓝 0) := by
  have hb : ∀ᶠ x in l, ‖a x*(w x)^j‖ ≤ 2*K^j := by
    have had : ∀ᶠ x in l, ‖a x‖ < 2 :=
      ((continuous_norm.tendsto (1 : ℂ)).comp ha).eventually_lt_const (by norm_num)
    filter_upwards [hwup,had] with x hx hax
    rw [norm_mul,norm_pow]
    exact mul_le_mul hax.le (pow_le_pow_left₀ (norm_nonneg _) hx j)
      (pow_nonneg (norm_nonneg _) _) (by norm_num)
  have h := endpoint_zero_mul_bounded
    (exp_div_pow_tendsto_zero_of_left_displacement hr hwlo hz m) hb
  apply h.congr'
  filter_upwards with x
  ring

/-- Evaluation of an endpoint polynomial stays bounded on a bounded path. -/
theorem endpointPolynomial_eval_bounded {α : Type*} {n : ℕ} {l : Filter α}
    (c : Fin (n+1) → ℂ) (m : ℕ) {w : α → ℂ} {K : ℝ}
    (hw : ∀ᶠ x in l, ‖w x‖ ≤ K) :
    ∀ᶠ x in l, ‖(endpointPolynomial c m).eval (w x)‖ ≤
      ∑ j, ‖c j‖*K^(j.val-m) := by
  filter_upwards [hw] with x hx
  rw [endpointPolynomial_eval]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [norm_mul,norm_pow]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) hx _) (norm_nonneg _)

/-- The actual grouped coefficient balance forces the normalized lowest
frequency polynomial to vanish asymptotically in the deep left half-plane. -/
theorem left_endpoint_tendsto_zero {α : Type*} {n D : ℕ} {l : Filter α}
    (c : Fin (n+1) → Fin (D+1) → ℂ) (i₀ : Fin (n+1))
    (hmin : ∀ j, c j 0 ≠ 0 → i₀.val ≤ j.val)
    {r : α → ℝ} {z w : α → ℂ} {a : α → Fin (n+1) → ℂ}
    {K : ℝ} (hK : 0 ≤ K) (hr : Tendsto r l atTop)
    (hwlo : ∀ᶠ x in l, 1/r x ≤ ‖w x‖)
    (hwup : ∀ᶠ x in l, ‖w x‖ ≤ K)
    (hz : ∀ᶠ x in l, (z x).re ≤ -(r x)^((1 : ℝ)/8)/8)
    (ha : ∀ j, Tendsto (fun x => a x j) l (𝓝 1))
    (hbalance : ∀ᶠ x in l,
      ∑ d, ∑ j, c j d*a x j*(w x)^j.val*Complex.exp ((d.val : ℂ)*z x) = 0) :
    Tendsto (fun x => (endpointPolynomial (fun j => c j 0) i₀.val).eval (w x))
      l (𝓝 0) := by
  have hwne : ∀ᶠ x in l, w x ≠ 0 := by
    filter_upwards [hr.eventually (eventually_gt_atTop (0 : ℝ)),hwlo] with x hx hxw
    exact norm_pos_iff.mp (lt_of_lt_of_le (one_div_pos.mpr hx) hxw)
  have ht (d : Fin (D+1)) (hd : d ≠ 0) : Tendsto (fun x =>
      (∑ j, c j d*a x j*(w x)^j.val*Complex.exp ((d.val : ℂ)*z x))/(w x)^i₀.val)
      l (𝓝 0) := by
    have hd1 : 1 ≤ d.val := Nat.one_le_iff_ne_zero.mpr
      (fun h => hd (Fin.ext h))
    have hdleft : ∀ᶠ x in l, (((d.val : ℂ)*z x).re) ≤ -(r x)^((1 : ℝ)/8)/8 := by
      filter_upwards [hz,hr.eventually (eventually_gt_atTop (0 : ℝ))] with x hx hrx
      simp only [Complex.mul_re,Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero]
      have hdr : (1 : ℝ) ≤ d.val := by exact_mod_cast hd1
      have hp := Real.rpow_pos_of_pos hrx (1/8 : ℝ)
      nlinarith
    have htj (j : Fin (n+1)) :=
      (endpoint_positive_frequency_tendsto_zero hK hr hwlo hwup hdleft (ha j)
        j.val i₀.val).const_mul (c j d)
    have hh := tendsto_finsetSum Finset.univ (fun j _ => htj j)
    simp only [mul_zero,Finset.sum_const_zero] at hh
    apply hh.congr'
    filter_upwards with x
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    ring
  let b : α → Fin (D+1) → ℂ := fun x d =>
    (∑ j, c j d*a x j*(w x)^j.val*Complex.exp ((d.val : ℂ)*z x))/(w x)^i₀.val
  have hother : Tendsto (fun x => ∑ d ∈ Finset.univ.erase (0 : Fin (D+1)), b x d)
      l (𝓝 0) := by
    have hh := tendsto_finsetSum (Finset.univ.erase (0 : Fin (D+1)))
      (fun d hd => ht d (Finset.ne_of_mem_erase hd))
    simpa only [Finset.sum_const_zero] using hh
  have hperturbed : Tendsto (fun x =>
      (∑ j, c j 0*a x j*(w x)^j.val)/(w x)^i₀.val) l (𝓝 0) := by
    have hh := hother.neg
    rw [neg_zero] at hh
    apply hh.congr'
    filter_upwards [hbalance] with x hx
    have hzero : ∑ d, b x d = 0 := by
      dsimp only [b]
      rw [← Finset.sum_div,hx,zero_div]
    have he := Finset.sum_erase_add Finset.univ (fun d => b x d)
      (Finset.mem_univ (0 : Fin (D+1)))
    rw [hzero] at he
    have hb0 : b x 0 = (∑ j, c j 0*a x j*(w x)^j.val)/(w x)^i₀.val := by
      simp [b]
    rw [hb0] at he
    linear_combination -he
  have hp := endpoint_perturbation_tendsto_zero (fun j => c j 0) i₀ hmin
    hK hwup hwne ha
  have h := hperturbed.sub hp
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards with x
  ring

/-- Dividing out the highest frequency reverses the coefficient array and
changes the deep right half-plane to the already treated left half-plane. -/
theorem reverse_frequency_balance {n D : ℕ}
    (c : Fin (n+1) → Fin (D+1) → ℂ) (a : Fin (n+1) → ℂ) (z w : ℂ)
    (hbalance : ∑ d, ∑ j, c j d*a j*w^j.val*Complex.exp ((d.val : ℂ)*z) = 0) :
    ∑ d : Fin (D+1), ∑ j, c j d.rev*a j*w^j.val*Complex.exp ((d.val : ℂ)*(-z)) = 0 := by
  have hrev : (∑ d : Fin (D+1), ∑ j, c j d.rev*a j*w^j.val*Complex.exp ((d.val : ℂ)*(-z))) =
      ∑ d : Fin (D+1), ∑ j, c j d*a j*w^j.val*Complex.exp ((d.rev.val : ℂ)*(-z)) := by
    simpa only [Fin.revPerm_apply,Fin.rev_rev] using
      (Equiv.sum_comp (Fin.revPerm (n := D+1))
        (fun d : Fin (D+1) => ∑ j,
          c j d*a j*w^j.val*Complex.exp ((d.rev.val : ℂ)*(-z))))
  rw [hrev]
  have he (d : Fin (D+1)) : Complex.exp ((d.rev.val : ℂ)*(-z)) =
      Complex.exp (-(D : ℂ)*z)*Complex.exp ((d.val : ℂ)*z) := by
    rw [← Complex.exp_add]
    congr 1
    have hval : d.rev.val = D-d.val := by rw [Fin.val_rev]; omega
    rw [hval]
    have hd : d.val ≤ D := Nat.le_of_lt_succ d.isLt
    rw [Nat.cast_sub hd]
    ring
  simp_rw [he]
  have hall : (∑ d, ∑ j, c j d*a j*w^j.val*
      (Complex.exp (-(D : ℂ)*z)*Complex.exp ((d.val : ℂ)*z))) =
      Complex.exp (-(D : ℂ)*z)*(∑ d, ∑ j, c j d*a j*w^j.val*Complex.exp ((d.val : ℂ)*z)) := by
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hall,hbalance,mul_zero]

/-- The normalized highest-frequency polynomial vanishes in the deep
right half-plane. -/
theorem right_endpoint_tendsto_zero {α : Type*} {n D : ℕ} {l : Filter α}
    (c : Fin (n+1) → Fin (D+1) → ℂ) (iD : Fin (n+1))
    (hmin : ∀ j, c j (Fin.last D) ≠ 0 → iD.val ≤ j.val)
    {r : α → ℝ} {z w : α → ℂ} {a : α → Fin (n+1) → ℂ}
    {K : ℝ} (hK : 0 ≤ K) (hr : Tendsto r l atTop)
    (hwlo : ∀ᶠ x in l, 1/r x ≤ ‖w x‖)
    (hwup : ∀ᶠ x in l, ‖w x‖ ≤ K)
    (hz : ∀ᶠ x in l, (r x)^((1 : ℝ)/8)/8 ≤ (z x).re)
    (ha : ∀ j, Tendsto (fun x => a x j) l (𝓝 1))
    (hbalance : ∀ᶠ x in l,
      ∑ d, ∑ j, c j d*a x j*(w x)^j.val*Complex.exp ((d.val : ℂ)*z x) = 0) :
    Tendsto (fun x => (endpointPolynomial (fun j => c j (Fin.last D)) iD.val).eval (w x))
      l (𝓝 0) := by
  have hrev := left_endpoint_tendsto_zero (fun j d => c j d.rev) iD
    (by simpa only [Fin.rev_zero] using hmin) hK hr hwlo hwup
    (show ∀ᶠ x in l, (-(z x)).re ≤ -(r x)^((1 : ℝ)/8)/8 from by
      filter_upwards [hz] with x hx
      simp only [Complex.neg_re]
      linarith) ha
    (show ∀ᶠ x in l,
      ∑ d : Fin (D+1), ∑ j, c j d.rev*a x j*(w x)^j.val*Complex.exp ((d.val : ℂ)*(-(z x))) = 0 from by
      filter_upwards [hbalance] with x hx
      exact reverse_frequency_balance c (a x) (z x) (w x) hx)
  simpa only [Fin.rev_zero] using hrev

/-- The product of the two normalized endpoint polynomials tends to zero
without choosing one semicircle permanently. -/
theorem endpoint_product_tendsto_zero {α : Type*} {n D : ℕ} {l : Filter α}
    (c : Fin (n+1) → Fin (D+1) → ℂ) (i₀ iD : Fin (n+1))
    (hmin0 : ∀ j, c j 0 ≠ 0 → i₀.val ≤ j.val)
    (hminD : ∀ j, c j (Fin.last D) ≠ 0 → iD.val ≤ j.val)
    {r : α → ℝ} {z w : α → ℂ} {a : α → Fin (n+1) → ℂ}
    {K : ℝ} (hK : 0 ≤ K) (hr : Tendsto r l atTop)
    (hwlo : ∀ᶠ x in l, 1/r x ≤ ‖w x‖)
    (hwup : ∀ᶠ x in l, ‖w x‖ ≤ K)
    (hz : ∀ᶠ x in l, (r x)^((1 : ℝ)/8)/8 ≤ |(z x).re|)
    (ha : ∀ j, Tendsto (fun x => a x j) l (𝓝 1))
    (hbalance : ∀ᶠ x in l,
      ∑ d, ∑ j, c j d*a x j*(w x)^j.val*Complex.exp ((d.val : ℂ)*z x) = 0) :
    Tendsto (fun x => ((endpointPolynomial (fun j => c j 0) i₀.val)*
      endpointPolynomial (fun j => c j (Fin.last D)) iD.val).eval (w x)) l (𝓝 0) := by
  let s : Set α := {x | (z x).re ≤ 0}
  let ll : Filter α := l ⊓ 𝓟 s
  let lr : Filter α := l ⊓ 𝓟 sᶜ
  have hleL : ll ≤ l := inf_le_left
  have hleR : lr ≤ l := inf_le_left
  have hleft : ∀ᶠ x in ll, (z x).re ≤ -(r x)^((1 : ℝ)/8)/8 := by
    have hsign : ∀ᶠ x in ll, (z x).re ≤ 0 := by
      exact (show ∀ᶠ x in 𝓟 s, (z x).re ≤ 0 from by simp [s]).filter_mono inf_le_right
    filter_upwards [hz.filter_mono hleL,hsign] with x hx hsx
    rw [abs_of_nonpos hsx] at hx
    linarith
  have hright : ∀ᶠ x in lr, (r x)^((1 : ℝ)/8)/8 ≤ (z x).re := by
    have hsign : ∀ᶠ x in lr, 0 < (z x).re := by
      exact (show ∀ᶠ x in 𝓟 sᶜ, 0 < (z x).re from by simp [s]).filter_mono inf_le_right
    filter_upwards [hz.filter_mono hleR,hsign] with x hx hsx
    rwa [abs_of_pos hsx] at hx
  have hL := endpoint_zero_mul_bounded
    (left_endpoint_tendsto_zero c i₀ hmin0 hK (hr.mono_left hleL)
      (hwlo.filter_mono hleL) (hwup.filter_mono hleL) hleft
      (fun j => (ha j).mono_left hleL) (hbalance.filter_mono hleL))
    (endpointPolynomial_eval_bounded (fun j => c j (Fin.last D)) iD.val
      (hwup.filter_mono hleL))
  have hR := endpoint_zero_mul_bounded
    (right_endpoint_tendsto_zero c iD hminD hK (hr.mono_left hleR)
      (hwlo.filter_mono hleR) (hwup.filter_mono hleR) hright
      (fun j => (ha j).mono_left hleR) (hbalance.filter_mono hleR))
    (endpointPolynomial_eval_bounded (fun j => c j 0) i₀.val
      (hwup.filter_mono hleR))
  have hR' : Tendsto (fun x =>
      (endpointPolynomial (fun j => c j 0) i₀.val).eval (w x)*
        (endpointPolynomial (fun j => c j (Fin.last D)) iD.val).eval (w x)) lr (𝓝 0) := by
    simpa only [mul_comm] using hR
  have heq : ll ⊔ lr = l := by
    dsimp only [ll,lr]
    rw [← inf_sup_left,Filter.sup_principal,Set.union_compl_self,Filter.principal_univ,inf_top_eq]
  have h := hL.sup hR'
  rw [heq] at h
  simpa only [eval_mul] using h

/-- The angular estimate remains valid when the central index is at most
any fixed multiple of the radius. -/
theorem angular_error_linear_radial_bound {C K r θ : ℝ} {N : ℕ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hr : 0 < r) (hNr : (N : ℝ) ≤ K*r)
    (hθ : |θ| ≤ r^(-7/8 : ℝ)) :
    (2*Real.sqrt C)*|θ| *(N : ℝ)^(13/16 : ℝ) +
      (C/2)*θ^2*(N : ℝ)^(13/8 : ℝ) ≤
        (2*Real.sqrt C)*K^(13/16 : ℝ)*r^(-1/16 : ℝ) +
          (C/2)*K^(13/8 : ℝ)*r^(-1/8 : ℝ) := by
  have hθ2 : θ^2 ≤ (r^(-7/8 : ℝ))^2 := by
    simpa only [← pow_two,sq_abs] using mul_self_le_mul_self (abs_nonneg θ) hθ
  have h1 : (N : ℝ)^(13/16 : ℝ) ≤ (K*r)^(13/16 : ℝ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg N) hNr (by norm_num)
  have h2 : (N : ℝ)^(13/8 : ℝ) ≤ (K*r)^(13/8 : ℝ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg N) hNr (by norm_num)
  calc
    _ ≤ (2*Real.sqrt C)*r^(-7/8 : ℝ)*(K*r)^(13/16 : ℝ) +
        (C/2)*(r^(-7/8 : ℝ))^2*(K*r)^(13/8 : ℝ) := by gcongr
    _ = _ := by
      rw [Real.mul_rpow hK hr.le,Real.mul_rpow hK hr.le,
        ← Real.rpow_mul_natCast hr.le]
      calc
        _ = (2*Real.sqrt C)*K^(13/16 : ℝ)*
              (r^(-7/8 : ℝ)*r^(13/16 : ℝ)) +
              (C/2)*K^(13/8 : ℝ)*(r^((-7/8 : ℝ)*2)*r^(13/8 : ℝ)) := by ring
        _ = _ := by rw [← Real.rpow_add hr,← Real.rpow_add hr]; norm_num

end LiWangWen

#print axioms LiWangWen.endpointPolynomial_eval
#print axioms LiWangWen.endpointPolynomial_eval_zero
#print axioms LiWangWen.endpointPolynomial_ne_zero
#print axioms LiWangWen.endpoint_product_eval_zero_ne
#print axioms LiWangWen.endpoint_zero_mul_bounded
#print axioms LiWangWen.endpoint_perturbation_tendsto_zero
#print axioms LiWangWen.endpoint_positive_frequency_tendsto_zero
#print axioms LiWangWen.endpointPolynomial_eval_bounded
#print axioms LiWangWen.left_endpoint_tendsto_zero
#print axioms LiWangWen.reverse_frequency_balance
#print axioms LiWangWen.right_endpoint_tendsto_zero
#print axioms LiWangWen.endpoint_product_tendsto_zero
#print axioms LiWangWen.angular_error_linear_radial_bound
