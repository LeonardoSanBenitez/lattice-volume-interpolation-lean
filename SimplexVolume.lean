import SimplexLattice
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The volume of the dilated standard simplex

Catalog item `simplex_equality_cases` (Sec. 1, the two unnumbered displays after
Conjecture 2) uses the classical value `vol(m T_n) = m^n/n!`, where
`T_n = conv{0, e_1, ..., e_n}`. The paper takes it for granted; this file proves it.

The proof is by induction on the dimension. Splitting off the first coordinate `t`, the
slice of `{x ≥ 0, x_1 + ... + x_{n+1} ≤ r}` over `t ∈ [0, r]` is the `n`-dimensional
simplex of size `r - t`, so Fubini gives
`vol_{n+1} = ∫_0^r (r - t)^n / n! dt = r^{n+1} / (n+1)!`.
-/

open MeasureTheory Set

namespace LatticeVolumeInterpolation

/-- The simplex `{x ≥ 0, ∑ x_i ≤ r}` of real size `r`. For a natural `m` it is
`realDilatedStandardSimplex n m`. -/
def realSizeSimplex (n : ℕ) (r : ℝ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ r}

theorem realDilatedStandardSimplex_eq_realSizeSimplex (n m : ℕ) :
    realDilatedStandardSimplex n m = realSizeSimplex n m := rfl

theorem measurableSet_realSizeSimplex (n : ℕ) (r : ℝ) :
    MeasurableSet (realSizeSimplex n r) := by
  have h1 : MeasurableSet {x : Fin n → ℝ | ∀ i, 0 ≤ x i} := by
    rw [Set.setOf_forall]
    exact MeasurableSet.iInter fun i =>
      measurableSet_le measurable_const (measurable_pi_apply i)
  have h2 : MeasurableSet {x : Fin n → ℝ | ∑ i, x i ≤ r} :=
    measurableSet_le (Finset.measurable_sum _ fun i _ => measurable_pi_apply i)
      measurable_const
  exact h1.inter h2

/-- The slice of the `(n+1)`-dimensional simplex over a value `t` of its first coordinate. -/
theorem slice_realSizeSimplex_succ (n : ℕ) (r t : ℝ) :
    {y : Fin n → ℝ | 0 ≤ t ∧ (∀ i, 0 ≤ y i) ∧ t + ∑ i, y i ≤ r} =
      if t ∈ Icc 0 r then realSizeSimplex n (r - t) else ∅ := by
  ext y
  split_ifs with ht
  · simp only [mem_setOf_eq, realSizeSimplex]
    constructor
    · rintro ⟨-, hy, hs⟩
      exact ⟨hy, by linarith⟩
    · rintro ⟨hy, hs⟩
      exact ⟨ht.1, hy, by linarith⟩
  · simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
    rintro ⟨h0, hy, hs⟩
    have hsum : 0 ≤ ∑ i, y i := Finset.sum_nonneg fun i _ => hy i
    exact ht ⟨h0, by linarith⟩

/-- Integral of the slice volumes: `∫_0^r (r - t)^n / n! dt = r^{n+1} / (n+1)!`. -/
theorem integral_slice_volume (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    ∫ t in Icc 0 r, (r - t) ^ n / (n.factorial : ℝ) =
      r ^ (n + 1) / ((n + 1).factorial : ℝ) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hr,
    intervalIntegral.integral_div, intervalIntegral.integral_comp_sub_left
      (fun t => t ^ n) r, integral_pow]
  simp only [sub_self, sub_zero]
  rw [Nat.factorial_succ]
  push_cast
  rw [zero_pow (Nat.succ_ne_zero n), sub_zero]
  field_simp

/-- **The volume of the simplex of size `r`:** `vol {x ≥ 0, ∑ x_i ≤ r} = r^n / n!`. -/
theorem volume_realSizeSimplex (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    volume (realSizeSimplex n r) = ENNReal.ofReal (r ^ n / (n.factorial : ℝ)) := by
  induction n generalizing r with
  | zero =>
    have huniv : realSizeSimplex 0 r = univ := by
      ext x
      simp [realSizeSimplex, hr]
    rw [huniv, volume_pi, Measure.pi_of_empty]
    simp
  | succ n ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
    have hpres : MeasurePreserving e volume (volume.prod volume) :=
      measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => (volume : Measure ℝ)) 0
    let T : Set (ℝ × (Fin n → ℝ)) :=
      {p | 0 ≤ p.1 ∧ (∀ i, 0 ≤ p.2 i) ∧ p.1 + ∑ i, p.2 i ≤ r}
    have hT : MeasurableSet T := by
      have hfirst : MeasurableSet {p : ℝ × (Fin n → ℝ) | 0 ≤ p.1} :=
        measurableSet_le measurable_const measurable_fst
      have hrest : MeasurableSet {p : ℝ × (Fin n → ℝ) | ∀ i, 0 ≤ p.2 i} := by
        rw [Set.setOf_forall]
        exact MeasurableSet.iInter fun i =>
          measurableSet_le measurable_const ((measurable_pi_apply i).comp measurable_snd)
      have hsum : MeasurableSet {p : ℝ × (Fin n → ℝ) | p.1 + ∑ i, p.2 i ≤ r} :=
        measurableSet_le (measurable_fst.add
          (Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).comp measurable_snd))
          measurable_const
      exact hfirst.inter (hrest.inter hsum)
    have hpre : realSizeSimplex (n + 1) r = e ⁻¹' T := by
      ext x
      simp only [realSizeSimplex, mem_setOf_eq, mem_preimage, T, e,
        MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_symm_apply,
        Fin.forall_fin_succ, Fin.sum_univ_succ]
      tauto
    rw [hpre, hpres.measure_preimage hT.nullMeasurableSet, Measure.prod_apply hT]
    have hslice : ∀ t : ℝ, volume (Prod.mk t ⁻¹' T) =
        (Icc (0 : ℝ) r).indicator
          (fun t => ENNReal.ofReal ((r - t) ^ n / (n.factorial : ℝ))) t := by
      intro t
      have hset : Prod.mk t ⁻¹' T =
          if t ∈ Icc 0 r then realSizeSimplex n (r - t) else ∅ :=
        slice_realSizeSimplex_succ n r t
      rw [hset]
      split_ifs with ht
      · rw [indicator_of_mem ht, ih (by linarith [ht.2])]
      · rw [indicator_of_notMem ht, measure_empty]
    simp_rw [hslice]
    rw [lintegral_indicator measurableSet_Icc,
      ← ofReal_integral_eq_lintegral_ofReal, integral_slice_volume n hr]
    · exact (Continuous.integrableOn_Icc (by fun_prop))
    · refine (ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ fun t ht => ?_)
      exact div_nonneg (pow_nonneg (by linarith [ht.2]) _) (by positivity)

/-- **The volume of `m T_n`:** `vol(m T_n) = m^n / n!`, the value the paper uses in both
simplex equality displays. -/
theorem volume_realDilatedStandardSimplex_toReal (n m : ℕ) :
    (volume (realDilatedStandardSimplex n m)).toReal = (m : ℝ) ^ n / (n.factorial : ℝ) := by
  rw [realDilatedStandardSimplex_eq_realSizeSimplex,
    volume_realSizeSimplex n (Nat.cast_nonneg m), ENNReal.toReal_ofReal (by positivity)]

end LatticeVolumeInterpolation
