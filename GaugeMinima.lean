import MinimaAntiBlocking
import StandardLattice

/-!
# Gauge minima with ties

Catalog item `successive_minima_via_gauge`, Sec. 2. The printed recurrence
excludes the full span at the previous critical scale, which may already be
the whole space when minima repeat. The corrected recurrence excludes the
chosen `(i-1)`-dimensional greedy flag. Its minimum is attained and equals
`lambda_i`, without a strict inequality between consecutive minima.
-/

open Set Module

namespace LatticeVolumeInterpolation

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {K : Set E} {Λ : Submodule ℤ E}
  [DiscreteTopology Λ] [IsZLattice ℝ Λ]

/-- The chosen greedy vector attains the next successive minimum, also at ties.
This combines both inequalities proved by the dilation/flag argument. -/
theorem gauge_flagVector_eq_successiveMinimum
    (hK : DiscreteMinkowski.IsPaperConvexBody K) {k : ℕ} (hk : k < finrank ℝ E) :
    gauge (DiscreteMinkowski.halfDifferenceBody K) (DiscreteMinkowski.flagVector K Λ k) =
      DiscreteMinkowski.successiveMinimum K Λ (k + 1) :=
  le_antisymm (gauge_flagVector_le_successiveMinimum hK hk)
    (DiscreteMinkowski.successiveMinimum_le_gauge_flagVector hK hk)

/-- The corrected recursive minimum: exclude a flag of dimension `k`, rather
than all lattice vectors at a possibly repeated critical scale. -/
theorem successiveMinimum_isLeast_gauge_outside_flag
    (hK : DiscreteMinkowski.IsPaperConvexBody K) {k : ℕ} (hk : k < finrank ℝ E) :
    IsLeast
      (gauge (DiscreteMinkowski.halfDifferenceBody K) ''
        ((Λ : Set E) \ (DiscreteMinkowski.flagSpan K Λ k : Set E)))
      (DiscreteMinkowski.successiveMinimum K Λ (k + 1)) := by
  have hchoice := DiscreteMinkowski.greedyChoice_flagSpan (Λ := Λ) hK hk
  refine ⟨?_, ?_⟩
  · exact ⟨DiscreteMinkowski.flagVector K Λ k,
      ⟨DiscreteMinkowski.flagVector_mem k hchoice,
        DiscreteMinkowski.flagVector_notMem k hchoice⟩,
      gauge_flagVector_eq_successiveMinimum hK hk⟩
  · rintro r ⟨z, ⟨hzΛ, hzn⟩, rfl⟩
    rw [← gauge_flagVector_eq_successiveMinimum hK hk]
    exact DiscreteMinkowski.flagVector_gauge_min k hchoice hzΛ hzn

/-- The first minimum is the least gauge of a nonzero lattice vector. -/
theorem firstMinimum_isLeast_gauge_nonzero
    (hK : DiscreteMinkowski.IsPaperConvexBody K) (hdim : 0 < finrank ℝ E) :
    IsLeast
      (gauge (DiscreteMinkowski.halfDifferenceBody K) ''
        {z : E | z ∈ Λ ∧ z ≠ 0})
      (DiscreteMinkowski.successiveMinimum K Λ 1) := by
  have hset : ((Λ : Set E) \ (DiscreteMinkowski.flagSpan K Λ 0 : Set E)) =
      {z : E | z ∈ Λ ∧ z ≠ 0} := by
    ext z
    simp [DiscreteMinkowski.flagSpan_zero]
  simpa only [zero_add, hset] using
    (successiveMinimum_isLeast_gauge_outside_flag (Λ := Λ) hK hdim)

end
end LatticeVolumeInterpolation
