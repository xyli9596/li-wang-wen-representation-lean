import LiWangWenPeriodicity
import InceFiniteDifference

/-!
# Growth under finite differences and exponential removal

The finite differences used to isolate periodic coefficients preserve an
actual global exponential bound. These closure results do not require a
growth theorem for solutions of the differential equation.
-/

set_option autoImplicit false
noncomputable section

namespace LiWangWen

theorem ExponentialBound.neg {f : ℂ → ℂ} (hf : ExponentialBound f) :
    ExponentialBound (fun z => -f z) := by
  obtain ⟨A, B, hA, hB, hbound⟩ := hf
  exact ⟨A, B, hA, hB, by simpa only [norm_neg] using hbound⟩

theorem ExponentialBound.sub {f g : ℂ → ℂ}
    (hf : ExponentialBound f) (hg : ExponentialBound g) :
    ExponentialBound (fun z => f z - g z) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem ExponentialBound.const_mul {f : ℂ → ℂ} (hf : ExponentialBound f) (c : ℂ) :
    ExponentialBound (fun z => c * f z) := (bound_const c).mul hf

theorem ExponentialBound.difference {f : ℂ → ℂ} (hf : ExponentialBound f) (h : ℂ) :
    ExponentialBound (IncePeriodic.difference h f) :=
  (hf.translate h).sub hf

theorem ExponentialBound.iterated_difference {f : ℂ → ℂ}
    (hf : ExponentialBound f) (h : ℂ) (k : ℕ) :
    ExponentialBound (((IncePeriodic.difference h)^k) f) := by
  induction k with
  | zero => simpa using hf
  | succ k ih =>
    simpa only [pow_succ', Module.End.mul_apply] using ih.difference h

theorem ExponentialBound.remove_exponential {f : ℂ → ℂ}
    (hf : ExponentialBound f) (a : ℂ) :
    ExponentialBound (fun z => Complex.exp (-a*z) * f z) :=
  (bound_exp (-a)).mul hf

end LiWangWen

#print axioms LiWangWen.ExponentialBound.neg
#print axioms LiWangWen.ExponentialBound.sub
#print axioms LiWangWen.ExponentialBound.const_mul
#print axioms LiWangWen.ExponentialBound.difference
#print axioms LiWangWen.ExponentialBound.iterated_difference
#print axioms LiWangWen.ExponentialBound.remove_exponential
