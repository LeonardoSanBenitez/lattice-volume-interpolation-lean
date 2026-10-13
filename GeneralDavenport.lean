import Davenport
import ProjectionShaking

/-!
# Davenport's coordinate-projection inequality

Catalog item `davenport_inequality`, Eq. (1.10). For any compact convex set,
the lattice point enumerator is bounded by the sum of all intrinsic coordinate
projection volumes. The empty index set contributes the body's volume; it must
be included, as in the cited Davenport inequality.

The proof uses the paper's anti-blocking prism decomposition after successive
coordinate shakings. The lattice count increases, every projection volume
decreases, and the final body is anti-blocking. This derives the quoted upper
bound without using Davenport's stronger two-sided discrepancy estimate.
-/

open Set MeasureTheory
open scoped ENNReal

namespace LatticeVolumeInterpolation

noncomputable section

variable {n : ℕ}

/-- **Davenport's inequality**, with all coordinate subsets, including the
full-dimensional term. No interior or anti-blocking assumption is needed. -/
theorem davenport_inequality {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (hKc : Convex ℝ K) :
    ((DiscreteMinkowski.latticePoints K (standardIntegerLattice n)).ncard : ℝ≥0∞) ≤
      ∑ I : Finset (Fin n), volume (projectionOff I K) := by
  calc
    _ ≤ ((DiscreteMinkowski.latticePoints (shakeUpTo K n)
        (standardIntegerLattice n)).ncard : ℝ≥0∞) := by
      exact_mod_cast ncard_latticePoints_le_shakeUpTo hK n
    _ ≤ ∑ I : Finset (Fin n), volume (projectionOff I (shakeUpTo K n)) :=
      davenport_antiBlocking (isCompact_shakeUpTo hK n) (isAntiBlocking_shakeUpTo hK hKc)
    _ ≤ _ := Finset.sum_le_sum fun I _ => volume_projectionOff_shakeUpTo_le I hK hKc n

end

end LatticeVolumeInterpolation
