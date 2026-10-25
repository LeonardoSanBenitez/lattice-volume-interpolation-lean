import SuccessiveMinimaBridge
import Mathlib.Data.Pi.Interval

/-!
The coordinatewise count used by the integer-box equality cases in Freyer--Lucas,
*Interpolating between volume and lattice point enumerator with successive minima*.

Catalog items: `integer_box_equality_for_bhw_lattice_conjecture` and
`symmetric_box_equality_case`.

For nonnegative integer half-side lengths `m i`, the integral points in the closed
coordinate box are the functions whose `i`-th coordinate lies in `[-m i, m i]`.  This
file proves their product count directly.  `CoordinateLattice.lean` identifies the finite sets
with lattice points of the corresponding real boxes; their successive minima are a separate
remaining obligation.
-/

open scoped BigOperators

namespace LatticeVolumeInterpolation

variable {n : ℕ}

/-- The integral points of the closed coordinate box with half-side lengths `m`. -/
noncomputable def integerBox (m : Fin n → ℕ) : Finset (Fin n → ℤ) :=
  Finset.Icc (fun i => -(m i : ℤ)) (fun i => m i)

/-- The closed coordinate box with half-side lengths `m` contains exactly
`∏ i, (2 * m i + 1)` integral points. -/
theorem card_integerBox (m : Fin n → ℕ) :
    (integerBox m).card = ∏ i, (2 * m i + 1) := by
  rw [integerBox, Pi.card_Icc]
  simp only [Int.card_Icc]
  apply Finset.prod_congr rfl
  intro i _
  omega

/-- The integral points in the interior of the coordinate box with half-side lengths `m`. -/
noncomputable def integerInteriorBox (m : Fin n → ℕ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset fun i => Finset.Ioo (-(m i : ℤ)) (m i)

/-- If every half-side length is positive, the interior coordinate box contains exactly
`∏ i, (2 * m i - 1)` integral points. -/
theorem card_integerInteriorBox (m : Fin n → ℕ) (hm : ∀ i, 0 < m i) :
    (integerInteriorBox m).card = ∏ i, (2 * m i - 1) := by
  rw [integerInteriorBox, Fintype.card_piFinset]
  simp only [Int.card_Ioo]
  apply Finset.prod_congr rfl
  intro i _
  have hmi : 0 < m i := hm i
  omega

end LatticeVolumeInterpolation
