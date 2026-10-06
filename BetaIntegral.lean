import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# The Beta integral with natural exponents

`∫_0^1 (1 - s)^a s^b ds = a! b! / (a + b + 1)!`.

This is the one-variable integral behind the volume of a join of two convex bodies in
complementary subspaces, which the anti-blocking case of the Rogers-Shephard inequality
(Eq. (4.1), catalog item `rogers_shephard_section_projection`) needs. It is proved by
induction on `a`, integrating by parts against `s^(b+1)/(b+1)`.
-/

open intervalIntegral

namespace LatticeVolumeInterpolation

/-- **The Beta integral.** `∫_0^1 (1 - s)^a s^b ds = a! b! / (a + b + 1)!`. -/
theorem integral_one_sub_pow_mul_pow (a b : ℕ) :
    ∫ s in (0 : ℝ)..1, (1 - s) ^ a * s ^ b =
      (a.factorial * b.factorial : ℝ) / ((a + b + 1).factorial : ℝ) := by
  induction a generalizing b with
  | zero =>
    simp only [pow_zero, one_mul, integral_pow, Nat.factorial_zero, Nat.cast_one, zero_add]
    rw [Nat.factorial_succ]
    push_cast
    rw [one_pow, zero_pow (Nat.succ_ne_zero b)]
    have hb : (b.factorial : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  | succ a ih =>
    -- integrate by parts with `u = (1 - s)^(a+1)` and `v = s^(b+1)/(b+1)`
    have hb1 : ((b : ℝ) + 1) ≠ 0 := by positivity
    have hu : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun s : ℝ => (1 - s) ^ (a + 1))
        (-((a + 1 : ℕ) : ℝ) * (1 - x) ^ a) x := by
      intro x _
      have h0 : HasDerivAt (fun s : ℝ => 1 - s) (-1) x := by
        simpa using (hasDerivAt_id x).const_sub 1
      refine (h0.pow (a + 1)).congr_deriv ?_
      rw [Nat.add_sub_cancel]
      ring
    have hv : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun s : ℝ => s ^ (b + 1) / ((b : ℝ) + 1))
        (x ^ b) x := by
      intro x _
      refine ((hasDerivAt_pow (b + 1) x).div_const ((b : ℝ) + 1)).congr_deriv ?_
      rw [Nat.add_sub_cancel]
      push_cast
      field_simp
    have hibp := integral_mul_deriv_eq_deriv_mul hu hv
      (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)
    simp only [sub_self, zero_pow (Nat.succ_ne_zero a), zero_mul, sub_zero, one_pow,
      zero_pow (Nat.succ_ne_zero b), zero_div, mul_zero] at hibp
    rw [hibp]
    have hrw : (fun x : ℝ => -((a + 1 : ℕ) : ℝ) * (1 - x) ^ a * (x ^ (b + 1) / ((b : ℝ) + 1))) =
        fun x => (-((a + 1 : ℕ) : ℝ) / ((b : ℝ) + 1)) * ((1 - x) ^ a * x ^ (b + 1)) := by
      funext x
      field_simp
    rw [hrw, intervalIntegral.integral_const_mul, ih (b + 1)]
    have hfa : ((a + 1).factorial : ℝ) = (a + 1 : ℝ) * a.factorial := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hfb : ((b + 1).factorial : ℝ) = (b + 1 : ℝ) * b.factorial := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hidx : a + (b + 1) + 1 = a + 1 + b + 1 := by ring
    rw [hfa, hfb, hidx]
    have hden : ((a + 1 + b + 1).factorial : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

end LatticeVolumeInterpolation
