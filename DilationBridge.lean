import LviBasic

/-!
# Dilation bridges for the paper's successive minima and lattice counts

Catalog items `successive_minima`, `lattice_point_enumerator`,
`volume_lattice_point_limit` and `product_bound_implies_minkowski`.
Dilating the body by a positive scalar is equivalent to refining the lattice by
its reciprocal. This identifies both the exact lattice count and the successive
minima used in the paper's asymptotic arguments.
-/

open Set Module
open scoped Pointwise

namespace LatticeVolumeInterpolation

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The central symmetral commutes with dilation. -/
theorem halfDifferenceBody_smul (r : ℝ) (K : Set E) :
    DiscreteMinkowski.halfDifferenceBody (r • K) =
      r • DiscreteMinkowski.halfDifferenceBody K := by
  have hsub : r • K - r • K = r • (K - K) := by
    ext z
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨x - y, sub_mem_sub hx hy, smul_sub r x y⟩
    · rintro ⟨_, ⟨x, hx, y, hy, rfl⟩, rfl⟩
      change r • (x - y) ∈ r • K - r • K
      rw [smul_sub]
      exact sub_mem_sub (smul_mem_smul_set hx) (smul_mem_smul_set hy)
  simp only [DiscreteMinkowski.halfDifferenceBody_apply, hsub, smul_smul, mul_comm]

/-- The defining span for a dilated body is exactly the span for the refined lattice. -/
theorem scaledLatticeSpan_smul_body {r : ℝ} (hr : 0 < r) (K : Set E)
    (Λ : Submodule ℤ E) (t : ℝ) :
    DiscreteMinkowski.scaledLatticeSpan (r • K) Λ t =
      DiscreteMinkowski.scaledLatticeSpan K (r⁻¹ • Λ) t := by
  rw [DiscreteMinkowski.scaledLatticeSpan_smul_lattice (inv_pos.mpr hr)]
  simp only [DiscreteMinkowski.scaledLatticeSpan, halfDifferenceBody_smul,
    smul_smul, inv_inv, mul_comm]

/-- The paper's scaling `λ_i(rK) = λ_i(K)/r`, without an attainment assumption. -/
theorem successiveMinimum_smul_body {r : ℝ} (hr : 0 < r) (K : Set E)
    (Λ : Submodule ℤ E) (i : ℕ) :
    DiscreteMinkowski.successiveMinimum (r • K) Λ i =
      DiscreteMinkowski.successiveMinimum K Λ i / r := by
  have heq : DiscreteMinkowski.successiveMinimum (r • K) Λ i =
      DiscreteMinkowski.successiveMinimum K (r⁻¹ • Λ) i := by
    unfold DiscreteMinkowski.successiveMinimum
    congr 1
    ext t
    change (0 < t ∧ i ≤ finrank ℝ (DiscreteMinkowski.scaledLatticeSpan (r • K) Λ t)) ↔
      (0 < t ∧ i ≤ finrank ℝ (DiscreteMinkowski.scaledLatticeSpan K (r⁻¹ • Λ) t))
    rw [scaledLatticeSpan_smul_body hr K Λ t]
  rw [heq, DiscreteMinkowski.successiveMinimum_smul_lattice (inv_pos.mpr hr)]
  exact (div_eq_inv_mul _ _).symm

/-- Lattice points in `rK` are the dilates of points in `K` on the refined lattice. -/
theorem latticePoints_smul_body {r : ℝ} (hr : r ≠ 0) (K : Set E)
    (Λ : Submodule ℤ E) :
    DiscreteMinkowski.latticePoints (r • K) Λ =
      r • DiscreteMinkowski.latticePoints K (r⁻¹ • Λ) := by
  rw [DiscreteMinkowski.latticePoints_apply, DiscreteMinkowski.latticePoints_apply,
    Submodule.coe_pointwise_smul, Set.smul_set_inter₀ hr, smul_smul,
    mul_inv_cancel₀ hr, one_smul]

/-- The corresponding lattice point counts agree, including empty intersections. -/
theorem ncard_latticePoints_smul_body {r : ℝ} (hr : r ≠ 0) (K : Set E)
    (Λ : Submodule ℤ E) :
    (DiscreteMinkowski.latticePoints (r • K) Λ).ncard =
      (DiscreteMinkowski.latticePoints K (r⁻¹ • Λ)).ncard := by
  rw [latticePoints_smul_body hr]
  exact Set.ncard_image_of_injective _ (smul_right_injective E hr)

/-- Positive dilations preserve the paper's convex-body hypotheses. -/
theorem isPaperConvexBody_smul {r : ℝ} (hr : 0 < r) {K : Set E}
    (hK : DiscreteMinkowski.IsPaperConvexBody K) :
    DiscreteMinkowski.IsPaperConvexBody (r • K) := by
  refine ⟨hK.1.smul₀ r, hK.2.1.smul r, ?_⟩
  rw [interior_smul₀ hr.ne']
  exact hK.2.2.smul_set

end

end LatticeVolumeInterpolation
