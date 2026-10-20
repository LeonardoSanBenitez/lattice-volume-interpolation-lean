import OrthogonalLatticeSplit
import Mathlib.Topology.DiscreteSubset

/-!
# Discreteness of rational orthogonal projections

Catalog items `projection_of_lattice_is_lattice` and
`projected_lattice_determinant_bound`. Reduce the subspace component modulo
the integral span of a selected real basis to obtain bounded representatives.
-/

open Set Module Metric

namespace LatticeVolumeInterpolation

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem orthogonalImageLattice_finite_inter_bounded
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] (L : Submodule ℝ E)
    {ι : Type*} [Finite ι] (v : Basis ι ℝ L)
    (hv : ∀ i, ((v i : L) : E) ∈ Λ)
    {B : Set Lᗮ} (hB : Bornology.IsBounded B) :
    ((orthogonalImageLattice Λ L : Set Lᗮ) ∩ B).Finite := by
  classical
  letI := Fintype.ofFinite ι
  let p := Lᗮ.orthogonalProjectionOnto
  obtain ⟨R, hR⟩ := hB.subset_closedBall 0
  let S := ∑ i, ‖(v i : E)‖
  have hfin : (closedBall (0 : E) (R + S) ∩ (Λ : Set E)).Finite := by
    refine Metric.finite_isBounded_inter_isClosed
      (show IsDiscrete (Λ : Set E) from DiscreteTopology.isDiscrete) isBounded_closedBall ?_
    rw [← Submodule.coe_toAddSubgroup]
    exact AddSubgroup.isClosed_of_discrete
  refine (hfin.image p).subset ?_
  rintro y ⟨⟨x, hx, rfl⟩, hyB⟩
  have hl : x - (p x : E) ∈ L := by
    change x - Lᗮ.starProjection x ∈ L
    simpa only [Submodule.orthogonal_orthogonal] using
      Lᗮ.sub_starProjection_mem_orthogonal x
  let l : L := ⟨x - (p x : E), hl⟩
  let μ := ∑ i, (⌊v.repr l i⌋ : ℤ) • ((v i : L) : E)
  have hμΛ : μ ∈ Λ := Λ.sum_mem (fun i _ => Λ.smul_mem _ (hv i))
  have hμL : μ ∈ L := L.sum_mem (fun i _ => L.smul_of_tower_mem _ (v i).property)
  have hsum : ∑ i, (v.repr l i) • ((v i : L) : E) = x - (p x : E) := by
    calc
      _ = L.subtype (∑ i, (v.repr l i) • v i) := by
        simp only [map_sum, map_smul, Submodule.subtype_apply]
      _ = _ := congrArg L.subtype (v.sum_repr l)
  have hdecomp : x - μ = (p x : E) +
      ∑ i, (v.repr l i - ⌊v.repr l i⌋) • ((v i : L) : E) := by
    have hs : ∑ i, (v.repr l i - ⌊v.repr l i⌋) • ((v i : L) : E) =
        (∑ i, (v.repr l i) • ((v i : L) : E)) - μ := by
      simp only [sub_smul, Finset.sum_sub_distrib, Int.cast_smul_eq_zsmul, μ]
    rw [hs, hsum]
    abel
  have hnorm : ‖x - μ‖ ≤ R + S := by
    rw [hdecomp]
    apply (norm_add_le _ _).trans
    apply add_le_add
    · have h := hR hyB
      rw [mem_closedBall, dist_zero_right] at h
      exact h
    · apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [Int.floor_le (v.repr l i)])]
      exact mul_le_of_le_one_left (norm_nonneg _) (by linarith [Int.lt_floor_add_one (v.repr l i)])
  refine ⟨x - μ, ⟨?_, Λ.sub_mem hx hμΛ⟩, ?_⟩
  · simpa only [mem_closedBall, dist_zero_right] using hnorm
  · have hzero : p μ = 0 := by
      apply Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr
      simpa only [Submodule.orthogonal_orthogonal] using hμL
    change p (x - μ) = p x
    rw [map_sub, hzero, sub_zero]

theorem orthogonalImageLattice_discrete
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] (L : Submodule ℝ E)
    {ι : Type*} [Finite ι] (v : Basis ι ℝ L)
    (hv : ∀ i, ((v i : L) : E) ∈ Λ) :
    DiscreteTopology (orthogonalImageLattice Λ L) := by
  apply discreteTopology_subtype_iff'.mpr
  intro y hy
  have hfin := orthogonalImageLattice_finite_inter_bounded Λ L v hv
    (B := closedBall y 1) isBounded_closedBall
  have hyT : y ∈ ((orthogonalImageLattice Λ L : Set Lᗮ) ∩ closedBall y 1) :=
    ⟨hy, mem_closedBall_self (by norm_num)⟩
  obtain ⟨U, hU, hUeq⟩ := isDiscrete_iff_forall_exists_isOpen.mp hfin.isDiscrete y hyT
  refine ⟨U ∩ ball y 1, hU.inter isOpen_ball, ?_⟩
  ext z
  constructor
  · rintro ⟨⟨hzU, hzB⟩, hzP⟩
    exact hUeq ▸ (show z ∈ U ∩ ((orthogonalImageLattice Λ L : Set Lᗮ) ∩ closedBall y 1)
      from ⟨hzU, hzP, ball_subset_closedBall hzB⟩)
  · intro hz
    have hzy : z = y := mem_singleton_iff.mp hz
    subst z
    have hyU : y ∈ U := (show y ∈ U ∩
      ((orthogonalImageLattice Λ L : Set Lᗮ) ∩ closedBall y 1) from hUeq ▸ rfl).1
    exact ⟨⟨hyU, mem_ball_self (by norm_num)⟩, hy⟩

theorem orthogonalImageLattice_span_top
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (L : Submodule ℝ E) :
    Submodule.span ℝ (orthogonalImageLattice Λ L : Set Lᗮ) = ⊤ := by
  change Submodule.span ℝ (Lᗮ.orthogonalProjectionOnto.toLinearMap '' (Λ : Set E)) = ⊤
  rw [← Submodule.map_span, IsZLattice.span_top (L := Λ), Submodule.map_top]
  apply LinearMap.range_eq_top.mpr
  intro y
  exact ⟨y, by simp⟩

end
end LatticeVolumeInterpolation
