import CoordinateLattice

/-!
# Standard lattice instances

Shared infrastructure for catalog item `lattice_point_enumerator`: the standard
integer lattice is the integral span of the coordinate basis, is discrete, and spans
the ambient real space. Kept below counting inequalities so coordinate changes and
translation averaging do not depend on Davenport.
-/

open Set Module

namespace LatticeVolumeInterpolation

noncomputable section

/-- `ℤ^n` is the integral span of the standard basis. -/
theorem standardIntegerLattice_eq_span (n : ℕ) :
    standardIntegerLattice n = Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n))) := by
  ext x
  rw [Basis.mem_span_iff_repr_mem, mem_standardIntegerLattice_iff]
  simp only [Pi.basisFun_repr, Set.mem_range, eq_intCast]
  constructor
  · rintro ⟨z, hz⟩ i
    exact ⟨z i, (hz i).symm⟩
  · intro h
    choose z hz using h
    exact ⟨z, fun i => (hz i).symm⟩

instance (n : ℕ) : DiscreteTopology (standardIntegerLattice n) := by
  rw [standardIntegerLattice_eq_span]; infer_instance

instance (n : ℕ) : IsZLattice ℝ (standardIntegerLattice n) where
  span_top := by
    rw [standardIntegerLattice_eq_span]
    exact ZSpan.span_top (Pi.basisFun ℝ (Fin n))

end

end LatticeVolumeInterpolation
