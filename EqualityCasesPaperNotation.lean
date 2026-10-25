import BoxEquality
import SimplexEquality
import Tiles

/-!
# The equality cases in the paper's notation

Catalog items `integer_box_equality_for_bhw_lattice_conjecture`, `simplex_equality_cases`,
`symmetric_box_equality_case` and `lattice_tile_sandwich`.

The equality calculations in `BoxEquality.lean` and `SimplexEquality.lean` count finite coordinate
enumerations. This file states the same equalities with the paper's `G(B)` and `G(int B)`: the
enumerations are identified with the lattice points of the closed bodies, and the strict-inequality
sets they enumerate are identified with the interiors of those bodies. It also proves the sharpness
sentence of the lattice-tile display: for `K = [0,1]^n`, a lattice tile, and every integer `m ≥ 1`,
both outer inequalities are equalities.
-/

open Set MeasureTheory Topology
open scoped Pointwise

namespace LatticeVolumeInterpolation

noncomputable section

variable {n : ℕ}

/-- The interior of the closed coordinate box `∏ [-m_i, m_i]` is the open box. -/
theorem interior_realCoordinateBox (m : Fin n → ℕ) :
    interior (realCoordinateBox m) = realInteriorCoordinateBox m := by
  rw [realCoordinateBox, ← Set.pi_univ_Icc, interior_pi_set Set.finite_univ]
  ext x
  simp [realInteriorCoordinateBox, interior_Icc]

/-- A point of the interior of `S` can be moved a positive amount in any direction inside `S`. -/
theorem exists_pos_add_smul_mem_of_mem_interior {S : Set (Fin n → ℝ)} {x : Fin n → ℝ}
    (hx : x ∈ interior S) (v : Fin n → ℝ) : ∃ ε : ℝ, 0 < ε ∧ x + ε • v ∈ S := by
  have hS : S ∈ 𝓝 x := mem_interior_iff_mem_nhds.1 hx
  have hc : Continuous fun t : ℝ => x + t • v :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hpre : (fun t : ℝ => x + t • v) ⁻¹' S ∈ 𝓝 (0 : ℝ) := by
    apply hc.continuousAt.preimage_mem_nhds
    simpa using hS
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hpre
  refine ⟨ε / 2, half_pos hε, hball ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]
  linarith

/-- In positive dimension, the interior of `m T_n = {x ≥ 0, ∑ x_i ≤ m}` is the strict set
`{x > 0, ∑ x_i < m}`. -/
theorem interior_realDilatedStandardSimplex (hn : 0 < n) (m : ℕ) :
    interior (realDilatedStandardSimplex n m) = realInteriorDilatedStandardSimplex n m := by
  apply Set.Subset.antisymm
  · intro x hx
    have hxS := interior_subset hx
    refine ⟨fun i => ?_, ?_⟩
    · obtain ⟨ε, hε, h⟩ := exists_pos_add_smul_mem_of_mem_interior hx (-Pi.single i (1 : ℝ))
      have h0 := h.1 i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, Pi.single_eq_same, smul_eq_mul,
        mul_neg, mul_one] at h0
      linarith
    · obtain ⟨ε, hε, h⟩ :=
        exists_pos_add_smul_mem_of_mem_interior hx (Pi.single ⟨0, hn⟩ (1 : ℝ))
      have h1 := h.2
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum, Finset.sum_pi_single', Finset.mem_univ, if_true, mul_one] at h1
      linarith
  · apply interior_maximal
    · intro x hx
      exact ⟨fun i => (hx.1 i).le, hx.2.le⟩
    · have h1 : IsOpen {x : Fin n → ℝ | ∀ i, 0 < x i} := by
        simp only [Set.setOf_forall]
        exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)
      have h2 : IsOpen {x : Fin n → ℝ | ∑ i, x i < m} :=
        isOpen_lt (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
      exact h1.inter h2

/-- **Integer boxes attain Conjecture 1**, in the paper's notation:
`G(B) = ∏ ⌊2/λ_i(B) + 1⌋` for `B = ∏ [-m_i, m_i]`, `m_1 ≥ ⋯ ≥ m_n ≥ 1`. -/
theorem integerBox_attains_bhw_lattice_conjecture_paper (m : Fin n → ℕ)
    (hmpos : ∀ i, 0 < m i) (hmono : Antitone m) :
    ((DiscreteMinkowski.latticePoints (realCoordinateBox m) (standardIntegerLattice n)).ncard : ℤ) =
      ∏ i : Fin n, ⌊2 / DiscreteMinkowski.successiveMinimum
        (realCoordinateBox m) (standardIntegerLattice n) (i.1 + 1) + 1⌋ := by
  rw [← coordinateLatticePoints_coe_eq_latticePoints, Set.ncard_coe_finset]
  exact integerBox_attains_bhw_lattice_conjecture m hmpos hmono

/-- **Symmetric integer boxes attain Eq. (1.7)**, in the paper's notation:
`G(int B) = vol(B) ∏ (1 - λ_i(B)/2)` for `B = ∏ [-m_i, m_i]`, `m_1 ≥ ⋯ ≥ m_n ≥ 1`. -/
theorem symmetricIntegerBox_attains_lower_conjectured_bound_paper (m : Fin n → ℕ)
    (hmpos : ∀ i, 0 < m i) (hmono : Antitone m) :
    (volume (realCoordinateBox m)).toReal *
        ∏ i : Fin n, (1 - DiscreteMinkowski.successiveMinimum
          (realCoordinateBox m) (standardIntegerLattice n) (i.1 + 1) / 2) =
      ((DiscreteMinkowski.latticePoints (interior (realCoordinateBox m))
        (standardIntegerLattice n)).ncard : ℝ) := by
  rw [interior_realCoordinateBox, ← coordinateInteriorLatticePoints_coe_eq_latticePoints,
    Set.ncard_coe_finset]
  exact symmetricIntegerBox_attains_lower_conjectured_bound m hmpos hmono

/-- **The simplex dilates attain Eq. (1.5)**, in the paper's notation:
`vol(m T_n) ∏ (1 + i λ_i(m T_n)/2) = G(m T_n)` for every integer `m ≥ 1`. -/
theorem simplex_upper_equality_paper (n m : ℕ) (hm : 0 < m) :
    (volume (realDilatedStandardSimplex n m)).toReal *
        (∏ i : Fin n, (1 + ((i.1 + 1 : ℕ) : ℝ) *
          DiscreteMinkowski.successiveMinimum (realDilatedStandardSimplex n m)
            (standardIntegerLattice n) (i.1 + 1) / 2)) =
      ((DiscreteMinkowski.latticePoints (realDilatedStandardSimplex n m)
        (standardIntegerLattice n)).ncard : ℝ) := by
  rw [← simplexCoordinateLatticePoints_coe_eq_latticePoints, Set.ncard_coe_finset]
  exact simplex_upper_equality n m hm

/-- **The simplex dilates attain Eq. (1.6)**, in the paper's notation:
`vol(m T_n) ∏ (1 - i λ_i(m T_n)/2) = G(int(m T_n))` for `n ≥ 1` and every integer `m ≥ 1`. -/
theorem simplex_lower_equality_paper (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    (volume (realDilatedStandardSimplex n m)).toReal *
        (∏ i : Fin n, (1 - ((i.1 + 1 : ℕ) : ℝ) *
          DiscreteMinkowski.successiveMinimum (realDilatedStandardSimplex n m)
            (standardIntegerLattice n) (i.1 + 1) / 2)) =
      ((DiscreteMinkowski.latticePoints (interior (realDilatedStandardSimplex n m))
        (standardIntegerLattice n)).ncard : ℝ) := by
  rw [interior_realDilatedStandardSimplex hn, DiscreteMinkowski.latticePoints_apply,
    ← simplexInteriorCoordinateLatticePoints_coe, Set.ncard_coe_finset]
  exact simplex_lower_equality n m hn hm

/-- The unit cube `[0,1]^n` is a convex lattice tile. -/
theorem isLatticeTile_cube_one : IsLatticeTile (cube n 1) := by
  refine ⟨fun y => ?_, fun z hz hz0 => ?_⟩
  · refine ⟨castCoords fun i => ⌊y i⌋, (mem_standardIntegerLattice_iff_castCoords _).2 ⟨_, rfl⟩, ?_⟩
    simp only [cube, Set.mem_pi, mem_univ, true_implies, Pi.sub_apply, castCoords, mem_Icc,
      Nat.cast_one]
    intro i
    exact ⟨sub_nonneg.2 (Int.floor_le _), by linarith [Int.lt_floor_add_one (y i)]⟩
  · obtain ⟨w, rfl⟩ := (mem_standardIntegerLattice_iff_castCoords z).1 hz
    have hw : ∃ i, w i ≠ 0 := by
      by_contra h
      push Not at h
      exact hz0 (funext fun i => by simp [castCoords, h i])
    obtain ⟨i, hi⟩ := hw
    rw [Set.disjoint_left]
    intro x hx hx'
    rw [interior_cube] at hx
    obtain ⟨y, hy, rfl⟩ := hx'
    rw [interior_cube] at hy
    have h1 := hx i (mem_univ i)
    have h2 := hy i (mem_univ i)
    simp only [vadd_eq_add, Pi.add_apply, castCoords, mem_Ioo, Nat.cast_one] at h1 h2
    rcases lt_or_gt_of_ne hi with h | h
    · have : (w i : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt h
      linarith [h1.1, h2.2]
    · have : (1 : ℝ) ≤ w i := by exact_mod_cast h
      linarith [h1.2, h2.1]

/-- The dilate `m [0,1]^n` is `[0,m]^n`. -/
theorem natCast_smul_cube_one {m : ℕ} (hm : 1 ≤ m) : (m : ℝ) • cube n 1 = cube n m := by
  ext y
  rw [mem_smul_cube_iff (by exact_mod_cast hm)]
  simp only [cube, Set.mem_pi, mem_univ, true_implies, mem_Icc, Nat.cast_one, mul_one]

/-- **The lattice-tile display is sharp** for `K = [0,1]^n` and integer `r = m ≥ 1`:
`G(int(mK)) = (m-1)^n` and `G(mK) = (m+1)^n`, with `K` a lattice tile. -/
theorem lattice_tile_sandwich_sharp {m : ℕ} (hm : 1 ≤ m) :
    IsLatticeTile (cube n 1) ∧
      ((DiscreteMinkowski.latticePoints (interior ((m : ℝ) • cube n 1))
          (standardIntegerLattice n)).ncard : ℝ) = ((m : ℝ) - 1) ^ n ∧
      ((DiscreteMinkowski.latticePoints ((m : ℝ) • cube n 1)
          (standardIntegerLattice n)).ncard : ℝ) = ((m : ℝ) + 1) ^ n := by
  refine ⟨isLatticeTile_cube_one, ?_, ?_⟩
  · rw [natCast_smul_cube_one hm, ncard_latticePoints_interior_cube hm]
    push_cast [Nat.cast_sub hm]
    ring
  · rw [natCast_smul_cube_one hm, ncard_latticePoints_cube]
    push_cast
    ring

end

end LatticeVolumeInterpolation
