import MinkowskiLower
import UpperBound
import BoxEquality
import SimplexMinima
import SimplexVolume

/-!
# Minkowski's two-sided bound in the paper's normalization

Catalog items `minkowski_second_theorem` and
`minkowski_second_theorem_equality_examples`, Eq. (1.2). The lower bound is the
segment construction in `MinkowskiLower`. The upper bound specializes the pinned
`DiscreteMinkowski.minkowski_second_theorem` to the standard integer lattice,
whose covolume is one, and rewrites its product-of-minima normalization as the
paper's product of reciprocal minima. Dimension zero is handled explicitly.
-/

open Set MeasureTheory Module
open scoped ENNReal

namespace LatticeVolumeInterpolation

noncomputable section

variable {n : ℕ}

/-- The upper half of Eq. (1.2), in the paper's reciprocal-minima normalization. -/
theorem minkowski_second_theorem_upper {K : Set (Fin n → ℝ)} (hKc : IsCompact K)
    (hKb : DiscreteMinkowski.IsPaperConvexBody K) :
    volume K ≤ ENNReal.ofReal (∏ i : Fin n,
      2 / DiscreteMinkowski.successiveMinimum K (standardIntegerLattice n) (i.1 + 1)) := by
  let lam : Fin n → ℝ := fun i =>
    DiscreteMinkowski.successiveMinimum K (standardIntegerLattice n) (i.1 + 1)
  have hdim : finrank ℝ (Fin n → ℝ) = n := Module.finrank_fin_fun ℝ
  have hpos : ∀ i, 0 < lam i := fun i =>
    DiscreteMinkowski.successiveMinimum_pos hKb (by omega) (by rw [hdim]; exact i.2)
  have hmink : (volume K).toReal * ∏ i : Fin n, lam i ≤ 2 ^ n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one, pow_zero]
      have hunit : volume (Set.univ : Set (Fin 0 → ℝ)) = 1 := by
        rw [volume_pi, Measure.pi_of_empty]; simp
      have hle := measure_mono (μ := volume) (Set.subset_univ K)
      rw [hunit] at hle
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hle)
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have h := DiscreteMinkowski.minkowski_second_theorem volume hKb
        (standardIntegerLattice (m + 1)) m (by rw [hdim])
      rw [covolume_standardIntegerLattice, mul_one,
        ← Fin.prod_univ_eq_prod_range
          (fun i => DiscreteMinkowski.successiveMinimum K
            (standardIntegerLattice (m + 1)) (i + 1)) (m + 1)] at h
      exact h
  have hprodpos : 0 < ∏ i : Fin n, lam i := Finset.prod_pos fun i _ => hpos i
  have hreal : (volume K).toReal ≤ ∏ i : Fin n, 2 / lam i := by
    rw [Finset.prod_div_distrib, Fin.prod_const]
    exact (le_div_iff₀ hprodpos).2 hmink
  rw [← ENNReal.ofReal_toReal hKc.measure_lt_top.ne]
  exact ENNReal.ofReal_le_ofReal hreal

/-- **Minkowski's second theorem, Eq. (1.2)**, with both bounds and all dimensions. -/
theorem minkowski_second_theorem_bounds {K : Set (Fin n → ℝ)} (hKc : IsCompact K)
    (hKb : DiscreteMinkowski.IsPaperConvexBody K) :
    ENNReal.ofReal ((1 / (n.factorial : ℝ)) * ∏ i : Fin n,
      2 / DiscreteMinkowski.successiveMinimum K (standardIntegerLattice n) (i.1 + 1)) ≤
        volume K ∧
    volume K ≤ ENNReal.ofReal (∏ i : Fin n,
      2 / DiscreteMinkowski.successiveMinimum K (standardIntegerLattice n) (i.1 + 1)) :=
  ⟨minkowski_second_theorem_lower hKc hKb, minkowski_second_theorem_upper hKc hKb⟩

/-- The standard simplex has all minima two and attains the lower bound of Eq. (1.2). -/
theorem simplex_attains_minkowski_lower (n : ℕ) :
    (∀ i : Fin n, DiscreteMinkowski.successiveMinimum (realStandardSimplex n)
      (standardIntegerLattice n) (i.1 + 1) = 2) ∧
    (volume (realStandardSimplex n)).toReal =
      (1 / (n.factorial : ℝ)) * ∏ i : Fin n,
        2 / DiscreteMinkowski.successiveMinimum (realStandardSimplex n)
          (standardIntegerLattice n) (i.1 + 1) := by
  refine ⟨successiveMinimum_realStandardSimplex_eq_two, ?_⟩
  simp_rw [successiveMinimum_realStandardSimplex_eq_two]
  simp [realStandardSimplex, volume_realDilatedStandardSimplex_toReal]

/-- The cube `[-1,1]^n` has all minima one and attains the upper bound of Eq. (1.2). -/
theorem cube_attains_minkowski_upper (n : ℕ) :
    (∀ i : Fin n, DiscreteMinkowski.successiveMinimum
      (realCoordinateBox (fun _ : Fin n => 1)) (standardIntegerLattice n) (i.1 + 1) = 1) ∧
    (volume (realCoordinateBox (fun _ : Fin n => 1))).toReal =
      ∏ i : Fin n, 2 / DiscreteMinkowski.successiveMinimum
        (realCoordinateBox (fun _ : Fin n => 1)) (standardIntegerLattice n) (i.1 + 1) := by
  have hmin : ∀ i : Fin n, DiscreteMinkowski.successiveMinimum
      (realCoordinateBox (fun _ : Fin n => 1)) (standardIntegerLattice n) (i.1 + 1) = 1 := by
    intro i
    simpa using successiveMinimum_realCoordinateBox_eq_reciprocal_of_antitone
      (fun _ : Fin n => 1) (fun _ => Nat.zero_lt_one) (fun _ _ _ => le_rfl) i
  refine ⟨hmin, ?_⟩
  simp_rw [hmin]
  simp [volume_realCoordinateBox_toReal]

end

end LatticeVolumeInterpolation
