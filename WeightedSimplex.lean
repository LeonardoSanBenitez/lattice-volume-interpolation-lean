import SimplexVolume
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The volume of a coordinate simplex with arbitrary edge lengths

For a finite index type `ι` with `k` elements and positive edge lengths `s_i`,

  `vol {x ≥ 0 : ∑_i x_i / s_i ≤ 1} = (∏_i s_i) / k!`.

This is `vol_k(conv{0, s_i e_i : i ∈ I})`, the simplex the proof of Theorem 1.1 places inside
`K ∩ L_I` (catalog item `theorem_1_1_upper_bound`, which notes that the paper uses the value
`(1/k!) ∏_{i ∈ I} (2/λ_i)` without stating it). It follows from `volume_realSizeSimplex` by
reindexing the coordinates and by the diagonal linear change of variables `x_i ↦ x_i / s_i`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace LatticeVolumeInterpolation

variable {ι : Type*} [Fintype ι]

/-- `{x ≥ 0, ∑ x_i ≤ r}` on an arbitrary finite index type has volume `r^k / k!`. -/
theorem volume_sizeSimplex_fintype {r : ℝ} (hr : 0 ≤ r) :
    volume {x : ι → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ r} =
      ENNReal.ofReal (r ^ Fintype.card ι / ((Fintype.card ι).factorial : ℝ)) := by
  set e := MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) (Fintype.equivFin ι).symm with he
  have hpres : MeasurePreserving e volume volume :=
    volume_measurePreserving_piCongrLeft (fun _ : ι => ℝ) (Fintype.equivFin ι).symm
  have happly : ∀ (y : Fin (Fintype.card ι) → ℝ) (i : ι), e y i = y (Fintype.equivFin ι i) := by
    intro y i
    simp [he, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  have hmeas : MeasurableSet {x : ι → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ r} := by
    have h1 : MeasurableSet {x : ι → ℝ | ∀ i, 0 ≤ x i} := by
      rw [Set.setOf_forall]
      exact MeasurableSet.iInter fun i => measurableSet_le measurable_const (measurable_pi_apply i)
    have h2 : MeasurableSet {x : ι → ℝ | ∑ i, x i ≤ r} :=
      measurableSet_le (Finset.measurable_sum _ fun i _ => measurable_pi_apply i)
        measurable_const
    exact h1.inter h2
  have hpre : e ⁻¹' {x : ι → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ r} =
      realSizeSimplex (Fintype.card ι) r := by
    ext y
    simp only [mem_preimage, mem_setOf_eq, happly, realSizeSimplex]
    constructor
    · rintro ⟨h0, hs⟩
      refine ⟨fun j => ?_, ?_⟩
      · simpa using h0 ((Fintype.equivFin ι).symm j)
      · rwa [Equiv.sum_comp (Fintype.equivFin ι) y] at hs
    · rintro ⟨h0, hs⟩
      exact ⟨fun i => h0 _, by rwa [Equiv.sum_comp (Fintype.equivFin ι) y]⟩
  rw [← hpres.measure_preimage hmeas.nullMeasurableSet, hpre, volume_realSizeSimplex _ hr]

/-- The simplex `conv{0, s_i e_i}` written by inequalities. -/
def weightedSimplex (s : ι → ℝ) : Set (ι → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i / s i ≤ 1}

/-- **`vol(conv{0, s_i e_i}) = (∏ s_i) / k!`.** -/
theorem volume_weightedSimplex [DecidableEq ι] {s : ι → ℝ} (hs : ∀ i, 0 < s i) :
    volume (weightedSimplex s) =
      ENNReal.ofReal ((∏ i, s i) / ((Fintype.card ι).factorial : ℝ)) := by
  set f : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) := Matrix.toLin' (Matrix.diagonal fun i => (s i)⁻¹) with hf
  have hfapply : ∀ x i, f x i = x i / s i := by
    intro x i
    simp [hf, Matrix.toLin'_apply, Matrix.mulVec_diagonal, div_eq_inv_mul]
  have hdet : LinearMap.det f = ∏ i, (s i)⁻¹ := by
    rw [hf, LinearMap.det_toLin', Matrix.det_diagonal]
  have hdet0 : LinearMap.det f ≠ 0 := by
    rw [hdet]
    exact Finset.prod_ne_zero_iff.2 fun i _ => inv_ne_zero (hs i).ne'
  have hpre : weightedSimplex s = f ⁻¹' {x : ι → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1} := by
    ext x
    simp only [weightedSimplex, mem_setOf_eq, mem_preimage, hfapply]
    constructor
    · rintro ⟨h0, h1⟩
      exact ⟨fun i => div_nonneg (h0 i) (hs i).le, h1⟩
    · rintro ⟨h0, h1⟩
      refine ⟨fun i => ?_, h1⟩
      have := h0 i
      rwa [div_nonneg_iff, or_iff_left (fun h => absurd h.2 (not_le.2 (hs i))),
        and_iff_left (hs i).le] at this
  rw [hpre, Measure.addHaar_preimage_linearMap _ hdet0, volume_sizeSimplex_fintype zero_le_one,
    hdet, ← Finset.prod_inv_distrib, one_pow]
  simp only [inv_inv]
  rw [abs_of_pos (Finset.prod_pos fun i _ => hs i), ← ENNReal.ofReal_mul
    (Finset.prod_pos fun i _ => hs i).le]
  congr 1
  ring

end LatticeVolumeInterpolation
