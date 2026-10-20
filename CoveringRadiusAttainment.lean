import CoveringRadius
import StandardLattice
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Attainment of the covering radius

Catalog item `covering_radius`, Sec. 1 before Proposition 1.6. For a compact
convex body in positive dimension, the infimum of the positive covering scales
is itself a positive covering scale, as required by the paper's minimum notation.
The zero-dimensional case is excluded: every positive scale covers there and
the infimum zero is not a positive scale.
-/

open Set Module Filter Topology
open scoped Pointwise

namespace LatticeVolumeInterpolation

noncomputable section

variable {n : ℕ}

/-- Compactness makes the covering relation closed in the real dilation parameter.
The relation here allows zero and negative scales; positivity is proved separately. -/
theorem isClosed_setOf_covering {K : Set (Fin n → ℝ)} (hK : IsCompact K) :
    IsClosed {r : ℝ | ∀ y : Fin n → ℝ,
      ∃ k ∈ K, y - r • k ∈ standardIntegerLattice n} := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hΛ : IsClosed (standardIntegerLattice n : Set (Fin n → ℝ)) := by
    letI : DiscreteTopology (standardIntegerLattice n).toAddSubgroup :=
      inferInstanceAs (DiscreteTopology (standardIntegerLattice n))
    rw [← Submodule.coe_toAddSubgroup]
    exact AddSubgroup.isClosed_of_discrete
  have hclosed (y : Fin n → ℝ) :
      IsClosed {r : ℝ | ∃ k ∈ K, y - r • k ∈ standardIntegerLattice n} := by
    have hpre : IsClosed {p : ℝ × K | y - p.1 • (p.2 : Fin n → ℝ) ∈
        standardIntegerLattice n} := hΛ.preimage (by fun_prop)
    have himage : Prod.fst '' {p : ℝ × K | y - p.1 • (p.2 : Fin n → ℝ) ∈
        standardIntegerLattice n} =
        {r : ℝ | ∃ k ∈ K, y - r • k ∈ standardIntegerLattice n} := by
      ext r
      simp only [mem_image, mem_setOf_eq, Prod.exists, exists_and_right, exists_eq_right]
      exact ⟨fun ⟨k, hk⟩ => ⟨k, k.property, hk⟩,
        fun ⟨k, hk, hp⟩ => ⟨⟨k, hk⟩, hp⟩⟩
    rw [← himage]
    exact isClosedMap_fst_of_compactSpace _ hpre
  have hset : {r : ℝ | ∀ y : Fin n → ℝ,
      ∃ k ∈ K, y - r • k ∈ standardIntegerLattice n} =
      ⋂ y : Fin n → ℝ, {r : ℝ | ∃ k ∈ K, y - r • k ∈ standardIntegerLattice n} := by
    ext r
    simp
  rw [hset]
  exact isClosed_iInter hclosed

/-- The infimum covering scale covers, before asserting that it is positive. -/
theorem coveringRadius_covers {K : Set (Fin n → ℝ)} (hKcpt : IsCompact K)
    (hKb : DiscreteMinkowski.IsPaperConvexBody K) (hn : 0 < n) :
    ∀ y : Fin n → ℝ, ∃ k ∈ K, y - coveringRadius K • k ∈ standardIntegerLattice n := by
  have hne : (coveringSet K).Nonempty := ⟨_, sum_minima_mem_coveringSet hKcpt hKb hn⟩
  have hsub : coveringSet K ⊆ {r : ℝ | ∀ y : Fin n → ℝ,
      ∃ k ∈ K, y - r • k ∈ standardIntegerLattice n} := by
    intro r hr y
    obtain ⟨z, hz, k, hk, heq⟩ := hr.2 y
    exact ⟨k, hk, by simpa only [heq, sub_sub_cancel] using hz⟩
  exact closure_minimal hsub (isClosed_setOf_covering hKcpt)
    (csInf_mem_closure hne ⟨0, fun _ hr => hr.1.le⟩)

theorem coveringRadius_pos {K : Set (Fin n → ℝ)} (hKcpt : IsCompact K)
    (hKb : DiscreteMinkowski.IsPaperConvexBody K) (hn : 0 < n) :
    0 < coveringRadius K := by
  apply lt_of_le_of_ne (coveringRadius_nonneg K)
  intro hzero
  obtain ⟨k, _, hk⟩ := coveringRadius_covers hKcpt hKb hn (fun _ => (1 / 2 : ℝ))
  rw [← hzero, zero_smul, sub_zero] at hk
  obtain ⟨z, hz⟩ := (mem_standardIntegerLattice_iff n _).mp hk
  let i : Fin n := ⟨0, hn⟩
  have hp : (0 : ℝ) < (z i : ℝ) := by rw [← hz i]; norm_num
  have hq : (z i : ℝ) < 1 := by rw [← hz i]; norm_num
  have hp' : (0 : ℤ) < z i := by exact_mod_cast hp
  have hq' : z i < 1 := by exact_mod_cast hq
  omega

/-- The paper's minimum is attained, in every positive dimension. -/
theorem coveringRadius_mem_coveringSet {K : Set (Fin n → ℝ)} (hKcpt : IsCompact K)
    (hKb : DiscreteMinkowski.IsPaperConvexBody K) (hn : 0 < n) :
    coveringRadius K ∈ coveringSet K := by
  refine ⟨coveringRadius_pos hKcpt hKb hn, fun y => ?_⟩
  obtain ⟨k, hk, hz⟩ := coveringRadius_covers hKcpt hKb hn y
  refine ⟨y - coveringRadius K • k, hz, ?_⟩
  exact ⟨k, hk, by abel⟩

/-- The infimum definition agrees with the least positive covering scale. -/
theorem coveringRadius_isLeast {K : Set (Fin n → ℝ)} (hKcpt : IsCompact K)
    (hKb : DiscreteMinkowski.IsPaperConvexBody K) (hn : 0 < n) :
    IsLeast (coveringSet K) (coveringRadius K) :=
  ⟨coveringRadius_mem_coveringSet hKcpt hKb hn,
    fun _ hr => csInf_le ⟨0, fun _ hs => hs.1.le⟩ hr⟩

end
end LatticeVolumeInterpolation
