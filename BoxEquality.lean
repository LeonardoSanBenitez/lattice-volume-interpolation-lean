import CoordinateMinima
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
The two axis-parallel box equality calculations asserted in Freyer--Lucas,
*Interpolating between volume and lattice point enumerator with successive minima*.

Catalog items: `integer_box_equality_for_bhw_lattice_conjecture` and
`symmetric_box_equality_case`.

The successive minima are supplied by `CoordinateMinima.lean`.  This file performs the
remaining floor-product and volume-product calculations in the paper's notation.
-/

open MeasureTheory
open scoped BigOperators

namespace LatticeVolumeInterpolation

/-- The floor factor in the Betke--Henk--Wills product at an integral box minimum. -/
theorem floor_two_div_reciprocal_nat_add_one (m : ℕ) (hm : 0 < m) :
    ⌊2 / (m : ℝ)⁻¹ + 1⌋ = (2 * m + 1 : ℤ) := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hreal : 2 / (m : ℝ)⁻¹ + 1 = (2 * m + 1 : ℕ) := by
    field_simp [hm0]
    norm_num
  calc
    ⌊2 / (m : ℝ)⁻¹ + 1⌋ = ⌊((2 * m + 1 : ℕ) : ℝ)⌋ := congrArg Int.floor hreal
    _ = (2 * m + 1 : ℤ) := Int.floor_natCast _

/-- A positive integral coordinate box attains the conjectured Betke--Henk--Wills
lattice-point upper bound. -/
theorem integerBox_attains_bhw_lattice_conjecture {n : ℕ} (m : Fin n → ℕ)
    (hmpos : ∀ i, 0 < m i) (hmono : Antitone m) :
    ((coordinateLatticePoints m).card : ℤ) =
      ∏ i : Fin n, ⌊2 / DiscreteMinkowski.successiveMinimum
        (realCoordinateBox m) (standardIntegerLattice n) (i.1 + 1) + 1⌋ := by
  rw [card_coordinateLatticePoints]
  push_cast
  apply Finset.prod_congr rfl
  intro i _
  rw [successiveMinimum_realCoordinateBox_eq_reciprocal_of_antitone m hmpos hmono i,
    floor_two_div_reciprocal_nat_add_one (m i) (hmpos i)]

/-- Euclidean volume of the coordinate box, in the product normalization used by the paper. -/
theorem volume_realCoordinateBox_toReal {n : ℕ} (m : Fin n → ℕ) :
    (volume (realCoordinateBox m)).toReal = ∏ i, (2 * m i : ℝ) := by
  have hle : (fun i : Fin n => -(m i : ℝ)) ≤ fun i => (m i : ℝ) := by
    intro i
    exact neg_le_self (Nat.cast_nonneg _)
  rw [realCoordinateBox, Real.volume_Icc_pi_toReal hle]
  apply Finset.prod_congr rfl
  intro i _
  ring

/-- One coordinate factor in the symmetric lower equality. -/
theorem two_mul_one_sub_reciprocal_div_two (m : ℕ) (hm : 0 < m) :
    (2 * (m : ℝ)) * (1 - (m : ℝ)⁻¹ / 2) = ((2 * m - 1 : ℕ) : ℝ) := by
  rw [Nat.cast_sub (by omega : 1 ≤ 2 * m)]
  push_cast
  field_simp [Nat.cast_ne_zero.mpr hm.ne']

/-- The intended integral-vertex axis-parallel boxes attain the symmetric lower bound
from Conjecture 2.  This is the exact subfamily for which the paper's final equality
sentence is valid. -/
theorem symmetricIntegerBox_attains_lower_conjectured_bound {n : ℕ} (m : Fin n → ℕ)
    (hmpos : ∀ i, 0 < m i) (hmono : Antitone m) :
    (volume (realCoordinateBox m)).toReal *
        ∏ i : Fin n, (1 - DiscreteMinkowski.successiveMinimum
          (realCoordinateBox m) (standardIntegerLattice n) (i.1 + 1) / 2) =
      ((coordinateInteriorLatticePoints m).card : ℝ) := by
  rw [volume_realCoordinateBox_toReal m, card_coordinateInteriorLatticePoints m hmpos]
  simp_rw [successiveMinimum_realCoordinateBox_eq_reciprocal_of_antitone m hmpos hmono]
  rw [← Finset.prod_mul_distrib]
  simp only [Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact two_mul_one_sub_reciprocal_div_two (m i) (hmpos i)

end LatticeVolumeInterpolation
