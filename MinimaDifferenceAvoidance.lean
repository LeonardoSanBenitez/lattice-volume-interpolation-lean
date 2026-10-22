import LviBasic

/-!
# Successive minima exclude scaled lattice differences

Catalog items `bhw_lattice_conjecture_dimension_two_symmetric` and
`bhw_lattice_conjecture_dimension_three_symmetric`.

Malikiosis, Lemma 2.1: when `q > 2 / λᵢ`, the difference body avoids
`q (Λ \ Λ^{i-1})`. The adapted real flag is used before choosing lattice
coordinates; no extra difference-avoidance premise is introduced.
-/

open Set Module
open scoped Pointwise

namespace LatticeVolumeInterpolation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {K : Set E} {Λ : Submodule ℤ E}
  [DiscreteTopology Λ] [IsZLattice ℝ Λ]

omit [FiniteDimensional ℝ E] in
/-- A rescaled difference of two body points belongs to the corresponding
dilate of the central symmetral. -/
theorem mem_smul_halfDifference_of_scaled_difference
    {x y z : E} (hx : x ∈ K) (hy : y ∈ K) {q : ℝ} (hq : q ≠ 0)
    (heq : x - y = q • z) :
    z ∈ (2 / q) • DiscreteMinkowski.halfDifferenceBody K := by
  refine ⟨(2 : ℝ)⁻¹ • (x - y), ?_, ?_⟩
  · rw [DiscreteMinkowski.halfDifferenceBody_apply]
    exact ⟨x - y, ⟨x, hx, y, hy, rfl⟩, rfl⟩
  · change (2 / q) • ((2 : ℝ)⁻¹ • (x - y)) = z
    rw [heq, smul_smul, smul_smul]
    have hcoef : (2 / q) * (2 : ℝ)⁻¹ * q = 1 := by field_simp
    rw [hcoef, one_smul]

/-- Source Lemma 2.1 in flag notation: a nonflag lattice vector cannot
occur as a difference at a scale strictly above the critical reciprocal. -/
theorem difference_ne_smul_outside_minima_flag
    (hK : DiscreteMinkowski.IsPaperConvexBody K) {i : ℕ}
    (hi : i < finrank ℝ E) {q : ℝ} (hq : 0 < q)
    (hcritical : 2 / q < DiscreteMinkowski.successiveMinimum K Λ (i + 1))
    {z : E} (hz : z ∈ Λ) (hzflag : z ∉ DiscreteMinkowski.flagSpan K Λ i)
    {x y : E} (hx : x ∈ K) (hy : y ∈ K) : x - y ≠ q • z := by
  intro heq
  have hmem := mem_smul_halfDifference_of_scaled_difference hx hy hq.ne' heq
  have hg := DiscreteMinkowski.gauge_le_of_mem_smul (by positivity : 0 ≤ 2 / q) hmem
  have hmin := DiscreteMinkowski.successiveMinimum_le_gauge_of_notMem hK hi hz hzflag
  exact (not_lt_of_ge (hmin.trans hg)) hcritical

/-- At the first minimum the excluded flag is zero, so every nonzero
lattice vector is excluded. -/
theorem difference_ne_smul_of_first_minimum
    (hK : DiscreteMinkowski.IsPaperConvexBody K) (hdim : 0 < finrank ℝ E)
    {q : ℝ} (hq : 0 < q)
    (hcritical : 2 / q < DiscreteMinkowski.successiveMinimum K Λ 1)
    {z : E} (hz : z ∈ Λ) (hz0 : z ≠ 0)
    {x y : E} (hx : x ∈ K) (hy : y ∈ K) : x - y ≠ q • z := by
  apply difference_ne_smul_outside_minima_flag hK hdim hq hcritical hz ?_ hx hy
  simpa only [DiscreteMinkowski.flagSpan_zero, Submodule.mem_bot] using hz0

end LatticeVolumeInterpolation
