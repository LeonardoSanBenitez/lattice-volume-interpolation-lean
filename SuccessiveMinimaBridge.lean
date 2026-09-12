import LviBasic

/-!
Paper-notation bridge for the central symmetral, gauge, and successive-minimum definitions
in Freyer--Lucas, *Interpolating between volume and lattice point enumerator with successive
minima*.

Catalog items: `central_symmetral`, `gauge_function`, `successive_minima`, and
`successive_minima_via_gauge`.

The paper writes $\operatorname{cs}(K) = \frac12(K-K)$ and defines the successive minima
through the dilates of this body.  `DiscreteMinkowski.halfDifferenceBody` and
`DiscreteMinkowski.successiveMinimum` use exactly those objects.  The paper's recursive
gauge formula is not restated here: it is false at repeated successive minima.  The two
gauge--dilation implications below are the valid bridge used by the greedy-flag result in
the dependency.
-/

open Set
open scoped Pointwise

namespace LatticeVolumeInterpolation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Freyer--Lucas' central symmetral `cs(K)`, in the paper's notation. -/
theorem centralSymmetral_eq_halfDifferenceBody (K : Set E) :
    DiscreteMinkowski.halfDifferenceBody K = (2 : ℝ)⁻¹ • (K - K) :=
  DiscreteMinkowski.halfDifferenceBody_apply K

/-- The correction to the gauge display at the exceptional point `x = 0`: the gauge is
zero, whereas the paper's set of strictly positive admissible radii has no minimum there. -/
theorem gauge_zero_correction (K : Set E) :
    gauge (DiscreteMinkowski.halfDifferenceBody K) 0 = 0 :=
  gauge_zero

/-- Eq. (1.1) in the origin-symmetric case, stated in the paper's dilation notation.
The library's infimum is the exact formal reading; attainment is supplied separately by
the successive-minima development when the index is in the ambient dimension. -/
theorem paper_successiveMinimum_of_originSymmetric {K : Set E}
    (hconv : Convex ℝ K) (hsym : DiscreteMinkowski.IsOriginSymmetric K)
    (Λ : Submodule ℤ E) (i : ℕ) :
    DiscreteMinkowski.successiveMinimum K Λ i =
      sInf {r : ℝ | 0 < r ∧ i ≤ Module.finrank ℝ
        (Submodule.span ℝ ((r • K) ∩ (Λ : Set E)))} :=
  DiscreteMinkowski.successiveMinimum_of_originSymmetric hconv hsym Λ i

/-- A lattice point whose central-symmetral gauge is strictly below `r` lies in the
corresponding paper dilation.  This is the strict half of the gauge bridge. -/
theorem latticePoint_mem_dilate_of_gauge_lt {K : Set E} {Λ : Submodule ℤ E}
    (hK : DiscreteMinkowski.IsPaperConvexBody K) {r : ℝ} {x : E}
    (hxΛ : x ∈ (Λ : Set E))
    (hxg : gauge (DiscreteMinkowski.halfDifferenceBody K) x < r) :
    x ∈ (r • DiscreteMinkowski.halfDifferenceBody K) ∩ (Λ : Set E) :=
  DiscreteMinkowski.latticeGaugeLt_subset hK r ⟨hxΛ, hxg⟩

/-- A lattice point in a nonnegative paper dilation has central-symmetral gauge at most
its dilation parameter.  This is the closed half of the gauge bridge. -/
theorem gauge_le_of_latticePoint_mem_dilate {K : Set E} {Λ : Submodule ℤ E}
    {r : ℝ} (hr : 0 ≤ r) {x : E}
    (hx : x ∈ (r • DiscreteMinkowski.halfDifferenceBody K) ∩ (Λ : Set E)) :
    gauge (DiscreteMinkowski.halfDifferenceBody K) x ≤ r :=
  (DiscreteMinkowski.subset_latticeGaugeLe (K := K) (Λ := Λ) hr hx).2

end LatticeVolumeInterpolation
