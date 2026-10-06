import SimplexMinima
import SimplexInteriorLattice
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Fintype.BigOperators

/-! Arithmetic closure of the standard-simplex upper and lower equality displays. -/

open scoped BigOperators

namespace LatticeVolumeInterpolation

/-- The product `∏_{j=1}^n (m+j)` is the ascending-factorial form of the binomial
coefficient in the closed simplex count. -/
theorem prod_add_fin_eq_factorial_mul_choose (n m : ℕ) :
    (∏ i : Fin n, (m + (i.1 + 1))) = n.factorial * (m + n).choose n := by
  calc
    (∏ i : Fin n, (m + (i.1 + 1))) = (m + 1).ascFactorial n := by
      rw [Finset.prod_fin_eq_prod_range]
      rw [Nat.ascFactorial_eq_prod_range]
      apply Finset.prod_congr rfl
      intro i hi
      simp [Finset.mem_range.mp hi]
      omega
    _ = n.factorial * (m + n).choose n := by
      rw [Nat.ascFactorial_eq_factorial_mul_choose']
      congr 2
      omega

/-- Real-valued factorial-product form of the closed stars-and-bars count. -/
theorem cast_choose_add_eq_prod_div_factorial (n m : ℕ) :
    ((m + n).choose n : ℝ) =
      (∏ i : Fin n, ((m : ℝ) + (i.1 + 1))) / (n.factorial : ℝ) := by
  have h := prod_add_fin_eq_factorial_mul_choose n m
  have hcast : (∏ i : Fin n, ((m : ℝ) + (i.1 + 1))) =
      (n.factorial : ℝ) * ((m + n).choose n : ℝ) := by
    exact_mod_cast h
  rw [hcast]
  field_simp

/-- The algebraic upper expression after substituting `λ_i(mT_n)=2/m`. -/
theorem simplex_upper_product_identity (n m : ℕ) (hm : 0 < m) :
    ((m : ℝ) ^ n / (n.factorial : ℝ)) *
        (∏ i : Fin n, (1 + ((i.1 + 1 : ℕ) : ℝ) * (2 / (m : ℝ)) / 2)) =
      ((m + n).choose n : ℝ) := by
  rw [cast_choose_add_eq_prod_div_factorial]
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hprod :
      (∏ i : Fin n, (1 + ((i.1 + 1 : ℕ) : ℝ) * (2 / (m : ℝ)) / 2)) =
        (∏ i : Fin n, ((m : ℝ) + (i.1 + 1))) / (m : ℝ) ^ n := by
    calc
      _ = ∏ i : Fin n, (((m : ℝ) + (i.1 + 1)) / m) := by
        apply Finset.prod_congr rfl
        intro i _hi
        field_simp
        norm_num
      _ = (∏ i : Fin n, ((m : ℝ) + (i.1 + 1))) /
          (∏ _i : Fin n, (m : ℝ)) := by
        rw [Finset.prod_div_distrib]
      _ = (∏ i : Fin n, ((m : ℝ) + (i.1 + 1))) / (m : ℝ) ^ n := by simp
  rw [hprod]
  field_simp

/-- The conjectured upper product, written with the actual successive minima of `mT_n`,
equals its closed lattice-point count. The prefactor is the classical simplex-volume
expression `m^n/n!`; identifying it with Lebesgue volume is kept as a separate bridge. -/
theorem simplex_upper_equality_with_volume_expression (n m : ℕ) (hm : 0 < m) :
    ((m : ℝ) ^ n / (n.factorial : ℝ)) *
        (∏ i : Fin n, (1 + ((i.1 + 1 : ℕ) : ℝ) *
          DiscreteMinkowski.successiveMinimum (realDilatedStandardSimplex n m)
            (standardIntegerLattice n) (i.1 + 1) / 2)) =
      ((simplexCoordinateLatticePoints n m).card : ℝ) := by
  rw [card_simplexCoordinateLatticePoints]
  simp_rw [successiveMinimum_realDilatedStandardSimplex_eq_two_div hm]
  exact simplex_upper_product_identity n m hm

/-- Truncated-natural descending-factorial identity underlying the interior count. -/
theorem prod_sub_fin_eq_factorial_mul_choose (n m : ℕ) :
    (∏ i : Fin n, (m - (i.1 + 1))) = n.factorial * (m - 1).choose n := by
  calc
    (∏ i : Fin n, (m - (i.1 + 1))) = (m - 1).descFactorial n := by
      rw [Finset.prod_fin_eq_prod_range, Nat.descFactorial_eq_prod_range]
      apply Finset.prod_congr rfl
      intro i hi
      simp [Finset.mem_range.mp hi]
      omega
    _ = n.factorial * (m - 1).choose n :=
      Nat.descFactorial_eq_factorial_mul_choose _ _

/-- Signed real-product form of the strict-interior stars-and-bars count. The proof splits
at `n < m`: above the threshold it casts the descending factorial; below it both sides
vanish at the factor indexed by `m-1`. -/
theorem cast_choose_sub_eq_prod_div_factorial (n m : ℕ) (hm : 0 < m) :
    ((m - 1).choose n : ℝ) =
      (∏ i : Fin n, ((m : ℝ) - (i.1 + 1))) / (n.factorial : ℝ) := by
  by_cases hnm : n < m
  · have hnat := prod_sub_fin_eq_factorial_mul_choose n m
    have hcastprod :
        (∏ i : Fin n, ((m - (i.1 + 1) : ℕ) : ℝ)) =
          ∏ i : Fin n, ((m : ℝ) - (i.1 + 1)) := by
      apply Finset.prod_congr rfl
      intro i _hi
      rw [Nat.cast_sub]
      · norm_num
      · omega
    have hcast : (∏ i : Fin n, ((m : ℝ) - (i.1 + 1))) =
        (n.factorial : ℝ) * ((m - 1).choose n : ℝ) := by
      rw [← hcastprod]
      exact_mod_cast hnat
    rw [hcast]
    field_simp
  · have hmn : m ≤ n := by omega
    have hchoose : (m - 1).choose n = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [hchoose, Nat.cast_zero]
    have hk : m - 1 < n := by omega
    let k : Fin n := ⟨m - 1, hk⟩
    have hfactor : (m : ℝ) - (k.1 + 1) = 0 := by
      dsimp [k]
      have hnat : m - 1 + 1 = m := Nat.sub_add_cancel hm
      have hcast : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by exact_mod_cast hnat
      linarith
    rw [Finset.prod_eq_zero (Finset.mem_univ k) hfactor, zero_div]

/-- The algebraic lower expression after substituting `λ_i(mT_n)=2/m`. -/
theorem simplex_lower_product_identity (n m : ℕ) (hm : 0 < m) :
    ((m : ℝ) ^ n / (n.factorial : ℝ)) *
        (∏ i : Fin n, (1 - ((i.1 + 1 : ℕ) : ℝ) * (2 / (m : ℝ)) / 2)) =
      ((m - 1).choose n : ℝ) := by
  rw [cast_choose_sub_eq_prod_div_factorial n m hm]
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hprod :
      (∏ i : Fin n, (1 - ((i.1 + 1 : ℕ) : ℝ) * (2 / (m : ℝ)) / 2)) =
        (∏ i : Fin n, ((m : ℝ) - (i.1 + 1))) / (m : ℝ) ^ n := by
    calc
      _ = ∏ i : Fin n, (((m : ℝ) - (i.1 + 1)) / m) := by
        apply Finset.prod_congr rfl
        intro i _hi
        field_simp
        norm_num
      _ = (∏ i : Fin n, ((m : ℝ) - (i.1 + 1))) /
          (∏ _i : Fin n, (m : ℝ)) := by
        rw [Finset.prod_div_distrib]
      _ = (∏ i : Fin n, ((m : ℝ) - (i.1 + 1))) / (m : ℝ) ^ n := by simp
  rw [hprod]
  field_simp

/-- The conjectured lower product, with the actual minima of `mT_n`, equals the strict
interior lattice-point count. -/
theorem simplex_lower_equality_with_volume_expression (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    ((m : ℝ) ^ n / (n.factorial : ℝ)) *
        (∏ i : Fin n, (1 - ((i.1 + 1 : ℕ) : ℝ) *
          DiscreteMinkowski.successiveMinimum (realDilatedStandardSimplex n m)
            (standardIntegerLattice n) (i.1 + 1) / 2)) =
      ((simplexInteriorCoordinateLatticePoints n m).card : ℝ) := by
  rw [card_simplexInteriorCoordinateLatticePoints n m hn]
  simp_rw [successiveMinimum_realDilatedStandardSimplex_eq_two_div hm]
  exact simplex_lower_product_identity n m hm

/-- Exact upper equality in the paper's volume notation, isolated behind the one classical
simplex-volume statement not presently available in the pinned Mathlib. -/
theorem simplex_upper_equality_of_volume_formula (n m : ℕ) (hm : 0 < m)
    (hvol : (MeasureTheory.volume (realDilatedStandardSimplex n m)).toReal =
      (m : ℝ) ^ n / (n.factorial : ℝ)) :
    (MeasureTheory.volume (realDilatedStandardSimplex n m)).toReal *
        (∏ i : Fin n, (1 + ((i.1 + 1 : ℕ) : ℝ) *
          DiscreteMinkowski.successiveMinimum (realDilatedStandardSimplex n m)
            (standardIntegerLattice n) (i.1 + 1) / 2)) =
      ((simplexCoordinateLatticePoints n m).card : ℝ) := by
  rw [hvol]
  exact simplex_upper_equality_with_volume_expression n m hm

/-- Exact lower equality in the paper's volume notation, with the same explicit classical
simplex-volume bridge. -/
theorem simplex_lower_equality_of_volume_formula (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (hvol : (MeasureTheory.volume (realDilatedStandardSimplex n m)).toReal =
      (m : ℝ) ^ n / (n.factorial : ℝ)) :
    (MeasureTheory.volume (realDilatedStandardSimplex n m)).toReal *
        (∏ i : Fin n, (1 - ((i.1 + 1 : ℕ) : ℝ) *
          DiscreteMinkowski.successiveMinimum (realDilatedStandardSimplex n m)
            (standardIntegerLattice n) (i.1 + 1) / 2)) =
      ((simplexInteriorCoordinateLatticePoints n m).card : ℝ) := by
  rw [hvol]
  exact simplex_lower_equality_with_volume_expression n m hn hm

end LatticeVolumeInterpolation
