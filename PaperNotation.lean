import StandardLattice
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# The paper's convex bodies, support function and enumerator

Catalog items `convex_body_class`, `support_function`, and
`lattice_point_enumerator`, Sections 1 and 2. Compactness is explicit in the
convex-body predicate. The support-function supremum is attained on a nonempty
compact set. The enumerator agrees with the cardinality of the finite lattice
intersection; its use on compact sets avoids infinite-set cardinal conventions.
-/

open Set MeasureTheory

namespace LatticeVolumeInterpolation

noncomputable section

variable {n : ℕ}

/-- The paper's class `K^n`, with the full-dimensional convention from Section 1. -/
def IsConvexBody (K : Set (Fin n → ℝ)) : Prop :=
  IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty

/-- The working hypotheses encode exactly the paper's compact convex bodies. -/
theorem isConvexBody_iff (K : Set (Fin n → ℝ)) :
    IsConvexBody K ↔ IsCompact K ∧ DiscreteMinkowski.IsPaperConvexBody K := by
  constructor
  · rintro ⟨hc, hv, hi⟩
    exact ⟨hc, hc.isBounded, hv, hi⟩
  · rintro ⟨hc, _, hv, hi⟩
    exact ⟨hc, hv, hi⟩

/-- Section 2's support function, in the standard coordinate scalar product. -/
def supportFunction (K : Set (Fin n → ℝ)) (x : Fin n → ℝ) : ℝ :=
  sSup ((fun y => x ⬝ᵥ y) '' K)

/-- Compactness turns the supremum definition into the paper's attained maximum. -/
theorem supportFunction_attained {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (hne : K.Nonempty) (x : Fin n → ℝ) :
    ∃ y ∈ K, supportFunction K x = x ⬝ᵥ y ∧ ∀ z ∈ K, x ⬝ᵥ z ≤ x ⬝ᵥ y := by
  have hcont : Continuous (fun y : Fin n → ℝ => x ⬝ᵥ y) := by
    unfold dotProduct
    fun_prop
  have himage := hK.image hcont
  obtain ⟨y, hy, hmax⟩ := hK.exists_isMaxOn hne hcont.continuousOn
  refine ⟨y, hy, le_antisymm ?_ ?_, hmax⟩
  · exact csSup_le (hne.image _) (by rintro _ ⟨z, hz, rfl⟩; exact hmax hz)
  · exact le_csSup himage.bddAbove ⟨y, hy, rfl⟩

/-- Section 2's lattice enumerator, used when the intersection is finite. -/
def latticePointEnumerator (K : Set (Fin n → ℝ)) (Λ : Submodule ℤ (Fin n → ℝ)) : ℕ :=
  (DiscreteMinkowski.latticePoints K Λ).ncard

/-- The enumerator is the cardinality of the finite lattice intersection. -/
theorem latticePointEnumerator_eq_card {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (Λ : Submodule ℤ (Fin n → ℝ)) [DiscreteTopology Λ] :
    latticePointEnumerator K Λ =
      (DiscreteMinkowski.finite_inter_lattice hK.isBounded Λ).toFinset.card := by
  exact Set.ncard_eq_toFinset_card _ _

/-- The integral span in Section 2 consists exactly of integer linear combinations.
Linear independence specifies when these generating vectors form a lattice basis. -/
theorem mem_integerSpan_iff {k : ℕ} (v : Fin k → (Fin n → ℝ)) (x : Fin n → ℝ) :
    x ∈ Submodule.span ℤ (Set.range v) ↔ ∃ c : Fin k → ℤ, ∑ i, c i • v i = x :=
  Submodule.mem_span_range_iff_exists_fun ℤ

end

end LatticeVolumeInterpolation
