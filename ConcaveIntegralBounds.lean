import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Lemma 5.2: chord and tangent bounds for the integral of a concave function

Catalog item `lemma_5_2_concave_integral_bounds`. For `f` concave on `[a, b]`,

* `(1/2)(f(a) + f(b))(b - a) ≤ ∫_a^b f(t) dt` (`concave_integral_chord_le`), and
* if `f` has a derivative `f'(a)` at `a`,
  `∫_a^b f(t) dt ≤ (b - a)(f(a) + (b - a) f'(a)/2)` (`concave_integral_le_tangent`).

The paper compares `f` with the affine function through `(a, f(a))` and `(b, f(b))`, and with
its tangent at `a`, and integrates. The proofs below follow that route.

Two remarks on the formal statements. The integral of `f` is not assumed to exist: a concave
function on a compact interval is bounded and continuous on the open interval, which is proved
here (`concave_intervalIntegrable`). For the tangent bound, only the derivative from the right
at `a` is assumed, which is implied by the paper's hypothesis that `f'(a)` exists.
-/

open MeasureTheory Set intervalIntegral

namespace LatticeVolumeInterpolation

variable {f : ℝ → ℝ} {a b : ℝ}

/-- A function concave on `[a, b]` is bounded there. Below by the smaller endpoint value; above
because the midpoint value controls each pair of points symmetric about it. -/
theorem concave_abs_le_of_mem_Icc (hf : ConcaveOn ℝ (Icc a b) f) :
    ∃ C, ∀ x ∈ Icc a b, |f x| ≤ C := by
  by_cases hab : a ≤ b
  · have ha : a ∈ Icc a b := left_mem_Icc.2 hab
    have hb : b ∈ Icc a b := right_mem_Icc.2 hab
    set L := min (f a) (f b)
    have hm : (a + b) / 2 ∈ Icc a b := ⟨by linarith, by linarith⟩
    refine ⟨max (|L|) (|2 * f ((a + b) / 2) - L|), fun x hx => ?_⟩
    have hlow : L ≤ f x := hf.min_le_of_mem_Icc ha hb hx
    have hx' : a + b - x ∈ Icc a b := ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have hlow' : L ≤ f (a + b - x) := hf.min_le_of_mem_Icc ha hb hx'
    have hmid := hf.2 hx hx' (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    have hpt : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • (a + b - x) = (a + b) / 2 := by
      simp only [smul_eq_mul]; ring
    rw [hpt] at hmid
    simp only [smul_eq_mul] at hmid
    have hup : f x ≤ 2 * f ((a + b) / 2) - L := by linarith
    rw [abs_le]
    constructor
    · have := neg_abs_le L
      have := le_max_left (|L|) (|2 * f ((a + b) / 2) - L|)
      linarith
    · have := le_abs_self (2 * f ((a + b) / 2) - L)
      have := le_max_right (|L|) (|2 * f ((a + b) / 2) - L|)
      linarith
  · refine ⟨0, fun x hx => ?_⟩
    exact absurd (hx.1.trans hx.2) hab

/-- A function concave on `[a, b]` is interval integrable on it. -/
theorem concave_intervalIntegrable (hab : a ≤ b) (hf : ConcaveOn ℝ (Icc a b) f) :
    IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  obtain ⟨C, hC⟩ := concave_abs_le_of_mem_Icc hf
  have hcont : ContinuousOn f (Ioo a b) := by
    simpa [interior_Icc] using hf.continuousOn_interior
  have hmeasIoo : AEStronglyMeasurable f (volume.restrict (Ioo a b)) :=
    hcont.aestronglyMeasurable measurableSet_Ioo
  have hmeas : AEStronglyMeasurable f (volume.restrict (Ioc a b)) := by
    rwa [Measure.restrict_congr_set Ioo_ae_eq_Ioc] at hmeasIoo
  refine IntegrableOn.of_bound measure_Ioc_lt_top hmeas C ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun x hx => ?_)
  rw [Real.norm_eq_abs]
  exact hC x (Ioc_subset_Icc_self hx)

/-- The integral of the affine function `c + d (t - a)` over `[a, b]`. -/
theorem integral_affine_from_left (c d : ℝ) :
    ∫ t in a..b, (c + d * (t - a)) = c * (b - a) + d * (b - a) ^ 2 / 2 := by
  have hi : IntervalIntegrable (fun t : ℝ => d * (t - a)) volume a b :=
    (intervalIntegrable_id.sub _root_.intervalIntegrable_const).const_mul d
  rw [intervalIntegral.integral_add _root_.intervalIntegrable_const hi,
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub intervalIntegrable_id _root_.intervalIntegrable_const,
    integral_id, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

/-- The affine function `c + d (t - a)` is interval integrable. -/
theorem intervalIntegrable_affine (c d : ℝ) :
    IntervalIntegrable (fun t : ℝ => c + d * (t - a)) volume a b :=
  IntervalIntegrable.add _root_.intervalIntegrable_const
    ((intervalIntegrable_id.sub _root_.intervalIntegrable_const).const_mul d)

/-- **Lemma 5.2, first inequality (the chord).** The integral of a function concave on `[a, b]`
is at least the area of the trapezoid under the chord through its endpoint values. -/
theorem concave_integral_chord_le (hab : a ≤ b) (hf : ConcaveOn ℝ (Icc a b) f) :
    (f a + f b) / 2 * (b - a) ≤ ∫ t in a..b, f t := by
  rcases hab.eq_or_lt with rfl | hlt
  · simp
  have hba : 0 < b - a := sub_pos.2 hlt
  let g : ℝ → ℝ := fun t => f a + (f b - f a) / (b - a) * (t - a)
  have hchord : ∀ t ∈ Icc a b, g t ≤ f t := by
    intro t ht
    have ha : a ∈ Icc a b := left_mem_Icc.2 hab
    have hb : b ∈ Icc a b := right_mem_Icc.2 hab
    have hw1 : 0 ≤ (b - t) / (b - a) := div_nonneg (by linarith [ht.2]) hba.le
    have hw2 : 0 ≤ (t - a) / (b - a) := div_nonneg (by linarith [ht.1]) hba.le
    have hsum : (b - t) / (b - a) + (t - a) / (b - a) = 1 := by
      field_simp; ring
    have h := hf.2 ha hb hw1 hw2 hsum
    have hpt : ((b - t) / (b - a)) • a + ((t - a) / (b - a)) • b = t := by
      simp only [smul_eq_mul]
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hba.ne']
      ring
    rw [hpt] at h
    simp only [smul_eq_mul] at h
    have hg : g t = (b - t) / (b - a) * f a + (t - a) / (b - a) * f b := by
      simp only [g]; field_simp; ring
    rw [hg]
    exact h
  have hgint : ∫ t in a..b, g t = (f a + f b) / 2 * (b - a) := by
    simp only [g]
    rw [integral_affine_from_left]
    field_simp
    ring
  rw [← hgint]
  exact intervalIntegral.integral_mono_on hab (intervalIntegrable_affine _ _)
    (concave_intervalIntegrable hab hf) hchord

/-- **Lemma 5.2, second inequality (the tangent).** If `f` is concave on `[a, b]` and has
derivative `f'` at `a` from the right, its integral is at most that of the tangent line at
`a`. -/
theorem concave_integral_le_tangent (hab : a ≤ b) (hf : ConcaveOn ℝ (Icc a b) f) {f' : ℝ}
    (hderiv : HasDerivWithinAt f f' (Ioi a) a) :
    ∫ t in a..b, f t ≤ (b - a) * (f a + (b - a) * f' / 2) := by
  let h : ℝ → ℝ := fun t => f a + f' * (t - a)
  have htangent : ∀ t ∈ Icc a b, f t ≤ h t := by
    intro t ht
    rcases ht.1.eq_or_lt with rfl | hat
    · simp [h]
    have hslope := hf.slope_le_of_hasDerivWithinAt_Ioi (left_mem_Icc.2 hab) ht hat hderiv
    rw [slope_def_field] at hslope
    have hta : 0 < t - a := sub_pos.2 hat
    have := (div_le_iff₀ hta).1 hslope
    simp only [h]
    linarith
  have hhint : ∫ t in a..b, h t = (b - a) * (f a + (b - a) * f' / 2) := by
    simp only [h]
    rw [integral_affine_from_left]
    ring
  rw [← hhint]
  exact intervalIntegral.integral_mono_on hab (concave_intervalIntegrable hab hf)
    (intervalIntegrable_affine _ _) htangent

end LatticeVolumeInterpolation
