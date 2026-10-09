import Pick
import TheoremOneFour
import UpperBound
import BoundarySections
import BoundaryFirstDirection

/-!
# Proposition 1.5: the Pick–boundary–Minkowski deduction

Catalog item `proposition_1_5_symmetric_lattice_polygon` (Sec. 5, Proposition 1.5).
This file mechanizes the paper's deduction in its original order: Pick's theorem
(Eq. (5.1)), the Henk–Schürmann–Wills boundary inequality (Eq. (5.2)), and
Minkowski's second theorem supply the three terms of the product bound.

The boundary inequality is proved unconditionally in `BoundaryFirstDirection.lean`.
The intermediate conditional bridges remain below to expose the paper's
dependency structure.
-/

open Set MeasureTheory

namespace LatticeVolumeInterpolation

noncomputable section

/-- The paper's exact Proposition 1.5 deduction, conditional only on the quoted
Henk–Schürmann–Wills inequality (5.2). -/
theorem proposition_1_5_of_boundary_bound {P : Set (Fin 2 → ℝ)}
    (hP : IsLatticePolygon P) (hint : (interior P).Nonempty)
    (_hsym : DiscreteMinkowski.IsOriginSymmetric P)
    (hboundary : (G2 (frontier P) : ℝ) / 2 ≤
      (volume P).toReal * (lam2 P 1 / 2 + lam2 P 2 / 2)) :
    (volume P).toReal * ((1 - lam2 P 1 / 2) * (1 - lam2 P 2 / 2)) ≤
      (G2 (interior P) : ℝ) := by
  have hc : IsCompact P := hP.isCompact
  have hb : DiscreteMinkowski.IsPaperConvexBody P :=
    ⟨hc.isBounded, hP.convex, hint⟩
  have hpick := pick_theorem_interior hP hint
  have hdim : Module.finrank ℝ (Fin 2 → ℝ) = 2 := Module.finrank_fin_fun ℝ
  have hmink := DiscreteMinkowski.minkowski_second_theorem volume hb
    (standardIntegerLattice 2) 1 (by rw [hdim])
  rw [covolume_standardIntegerLattice, mul_one,
    show (∏ i ∈ Finset.range 2,
      DiscreteMinkowski.successiveMinimum P (standardIntegerLattice 2) (i + 1)) =
      lam2 P 1 * lam2 P 2 by simp [lam2, Finset.prod_range_succ]] at hmink
  norm_num at hmink
  nlinarith

/-- Proposition 1.5 after the symmetric-section part of the cited boundary
proof has been discharged. The two facet identities `harea` and `hedges`
remain explicit until the lattice-polygon edge construction supplies them. -/
theorem proposition_1_5_of_pyramid_partition {P : Set (Fin 2 → ℝ)}
    (hP : IsLatticePolygon P) (hint : (interior P).Nonempty)
    (hsym : DiscreteMinkowski.IsOriginSymmetric P) (A B : ℝ)
    (harea : A + B = (volume P).toReal)
    (hB : B = (yHi P - yLo P) *
      (rowHi P (yLo P) - rowLo P (yLo P)) / 2)
    (hedges : (G2 (frontier P) : ℝ) / 2 ≤ lam2 P 1 * A + lam2 P 2 * B) :
    (volume P).toReal * ((1 - lam2 P 1 / 2) * (1 - lam2 P 2 / 2)) ≤
      (G2 (interior P) : ℝ) := by
  have hboundary := boundary_bound_of_symmetric_pyramid_partition
    hP.isCompact hP.convex hint hsym A B harea hB hedges
  exact proposition_1_5_of_boundary_bound hP hint hsym hboundary

/-- **Proposition 1.5.** The lower Freyer--Lucas product bound for every
origin-symmetric convex lattice polygon with nonempty interior. -/
theorem proposition_1_5_symmetric_lattice_polygon {P : Set (Fin 2 → ℝ)}
    (hP : IsLatticePolygon P) (hint : (interior P).Nonempty)
    (hsym : DiscreteMinkowski.IsOriginSymmetric P) :
    (volume P).toReal * ((1 - lam2 P 1 / 2) * (1 - lam2 P 2 / 2)) ≤
      (G2 (interior P) : ℝ) :=
  proposition_1_5_of_boundary_bound hP hint hsym
    (henk_schurmann_wills_boundary_bound hP hint hsym)

end

end LatticeVolumeInterpolation
