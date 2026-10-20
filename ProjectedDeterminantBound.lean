import ProjectedCovolume
import ProjectedLatticeInstances
import UpperBound

/-!
# The determinant bound after Theorem 1.3

Catalog item `projected_lattice_determinant_bound`. For selected independent
integer vectors spanning `L`, the paper's `vol_k(P_I)` is the intrinsic volume
of their parallelepiped. The full section lattice can have a strictly smaller
covolume than this selected-vector lattice. Consequently the projected lattice
has covolume at least `1 / vol_k(P_I)`, as printed.
-/

open Set Module MeasureTheory

namespace LatticeVolumeInterpolation

noncomputable section

/-- Standard integer lattice transported to the Euclidean norm, without changing volume. -/
def euclideanIntegerLattice (n : ℕ) : Submodule ℤ (EuclideanSpace ℝ (Fin n)) :=
  ZLattice.comap ℝ (standardIntegerLattice n) (EuclideanSpace.equiv (Fin n) ℝ).toLinearMap

instance (n : ℕ) : DiscreteTopology (euclideanIntegerLattice n) :=
  inferInstanceAs (DiscreteTopology (ZLattice.comap ℝ (standardIntegerLattice n)
    (EuclideanSpace.equiv (Fin n) ℝ).toLinearMap))

instance (n : ℕ) : IsZLattice ℝ (euclideanIntegerLattice n) :=
  inferInstanceAs (IsZLattice ℝ (ZLattice.comap ℝ (standardIntegerLattice n)
    (EuclideanSpace.equiv (Fin n) ℝ).toLinearMap))

theorem covolume_euclideanIntegerLattice (n : ℕ) :
    ZLattice.covolume (euclideanIntegerLattice n) volume = 1 := by
  rw [euclideanIntegerLattice, ZLattice.covolume_comap (standardIntegerLattice n)
    volume volume (e := EuclideanSpace.equiv (Fin n) ℝ)
    (PiLp.volume_preserving_ofLp (Fin n)), covolume_standardIntegerLattice]

/-- The paper's projected lattice agrees with the intrinsic orthogonal image lattice. -/
theorem orthogonalImageLattice_eq_projectedLattice (n : ℕ) (X : Set (Fin n → ℝ)) :
    orthogonalImageLattice (euclideanIntegerLattice n)
      ((Submodule.span ℝ X).map (toEucl n).toLinearMap) =
      projectedLattice (standardIntegerLattice n) X := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(toEucl n).symm x, hx, ?_⟩
    change ((Submodule.span ℝ X).map (toEucl n).toLinearMap)ᗮ.orthogonalProjectionOnto
      (toEucl n ((toEucl n).symm x)) = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  · rintro ⟨x, hx, rfl⟩
    refine ⟨toEucl n x, ?_, rfl⟩
    change (toEucl n).symm (toEucl n x) ∈ standardIntegerLattice n
    rwa [LinearEquiv.symm_apply_apply]

/-- The reciprocal-zonotope determinant bound, for any lattice-generated subspace
of standard Euclidean space. A basis here is precisely the selected independent
vectors, not a primitive basis of the full intersection lattice. -/
theorem projected_lattice_determinant_bound
    (n : ℕ) (L : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    {ι : Type*} [Fintype ι] (v : Basis ι ℝ L)
    (hv : ∀ i, ((v i : L) : EuclideanSpace ℝ (Fin n)) ∈ euclideanIntegerLattice n) :
    (volume.real (parallelepiped v))⁻¹ ≤
      ZLattice.covolume (orthogonalImageLattice (euclideanIntegerLattice n) L) volume := by
  simpa only [covolume_euclideanIntegerLattice, one_div] using
    projected_covolume_ge_reciprocal_zonotope (euclideanIntegerLattice n) L v hv

end
end LatticeVolumeInterpolation
