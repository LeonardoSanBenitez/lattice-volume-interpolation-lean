import ProjectedLattice

open Set Module Metric

namespace LatticeVolumeInterpolation

noncomputable section

variable {n : ℕ}

/-- The image of an integer lattice in the orthogonal complement of a lattice subspace. -/
def projectedLattice (Λ : Submodule ℤ (Fin n → ℝ)) (X : Set (Fin n → ℝ)) :
    Submodule ℤ ((Submodule.span ℝ X).map (toEucl n).toLinearMap)ᗮ :=
  Λ.map ((projMap (Submodule.span ℝ X)).restrictScalars ℤ)

theorem coe_projectedLattice (Λ : Submodule ℤ (Fin n → ℝ)) (X : Set (Fin n → ℝ)) :
    (projectedLattice Λ X : Set ((Submodule.span ℝ X).map (toEucl n).toLinearMap)ᗮ) =
      projMap (Submodule.span ℝ X) '' (Λ : Set (Fin n → ℝ)) := rfl

theorem projectedLattice_discrete (Λ : Submodule ℤ (Fin n → ℝ)) [DiscreteTopology Λ]
    {X : Set (Fin n → ℝ)} (hX : X ⊆ Λ) : DiscreteTopology (projectedLattice Λ X) := by
  classical
  let S := projectedLattice Λ X
  apply discreteTopology_subtype_iff'.mpr
  intro y hy
  have hfin : ((S : Set _) ∩ closedBall y 1).Finite := by
    rw [coe_projectedLattice]
    exact finite_projMap_inter_bounded Λ hX isBounded_closedBall
  have hyT : y ∈ ((S : Set _) ∩ closedBall y 1) :=
    ⟨hy, mem_closedBall_self (by norm_num)⟩
  obtain ⟨U, hUopen, hUeq⟩ := isDiscrete_iff_forall_exists_isOpen.mp hfin.isDiscrete y hyT
  refine ⟨U ∩ ball y 1, hUopen.inter isOpen_ball, ?_⟩
  ext z
  constructor
  · intro hz
    have hzT : z ∈ ((S : Set _) ∩ closedBall y 1) :=
      ⟨hz.2, ball_subset_closedBall hz.1.2⟩
    have hzU : z ∈ U ∩ ((S : Set _) ∩ closedBall y 1) := ⟨hz.1.1, hzT⟩
    exact hUeq ▸ hzU
  · intro hz
    rw [mem_singleton_iff] at hz
    subst z
    have hyU : y ∈ U := by
      have : y ∈ U ∩ ((S : Set _) ∩ closedBall y 1) := by
        rw [hUeq]
        exact rfl
      exact this.1
    exact ⟨⟨hyU, mem_ball_self (by norm_num)⟩, hy⟩

theorem projectedLattice_span_top (Λ : Submodule ℤ (Fin n → ℝ))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (X : Set (Fin n → ℝ)) :
    Submodule.span ℝ (projectedLattice Λ X).carrier = ⊤ := by
  change Submodule.span ℝ (projMap (Submodule.span ℝ X) '' (Λ : Set (Fin n → ℝ))) = ⊤
  exact span_projMap_eq_top _ (IsZLattice.span_top (L := Λ))

/-- The projected lattice has a positive covolume in its Euclidean ambient subspace. -/
theorem projectedLattice_covolume_pos (Λ : Submodule ℤ (Fin n → ℝ))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {X : Set (Fin n → ℝ)} (hX : X ⊆ Λ) :
    0 < ZLattice.covolume (projectedLattice Λ X) MeasureTheory.volume := by
  letI : DiscreteTopology (projectedLattice Λ X) := projectedLattice_discrete Λ hX
  letI : IsZLattice ℝ (projectedLattice Λ X) := ⟨projectedLattice_span_top Λ X⟩
  exact ZLattice.covolume_pos (projectedLattice Λ X) MeasureTheory.volume

end

end LatticeVolumeInterpolation
