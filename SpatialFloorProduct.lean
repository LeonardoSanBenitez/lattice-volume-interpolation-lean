import SpatialPeriodBound
import AdaptedMinimaCoordinates
import PlanarFloorProduct

/-!
# The three-dimensional floor-product lattice bound

Catalog item `bhw_lattice_conjecture_dimension_three_symmetric`, the
dimension-three confirmation sentence after Conjecture 1.

The adapted-minimum flag supplies the three period exclusions, and the
residue-slice argument supplies their product. This instantiates the
dimension-three theorem quoted from Malikiosis in Freyer--Lucas.
-/

open Set Module
open scoped BigOperators Pointwise

namespace LatticeVolumeInterpolation

theorem spatial_lattice_count_le_of_minima_thresholds
    {K : Set (Fin 3 → ℝ)} (hc : IsCompact K)
    (hK : DiscreteMinkowski.IsPaperConvexBody K)
    {q₁ q₂ q₃ : ℕ} (hq₃ : 0 < q₃) (hq₃₂ : q₃ ≤ q₂) (hq₂₁ : q₂ ≤ q₁)
    (hfirst : 2 / (q₁ : ℝ) < DiscreteMinkowski.successiveMinimum K (standardIntegerLattice 3) 1)
    (hsecond : 2 / (q₂ : ℝ) < DiscreteMinkowski.successiveMinimum K (standardIntegerLattice 3) 2)
    (hthird : 2 / (q₃ : ℝ) < DiscreteMinkowski.successiveMinimum K (standardIntegerLattice 3) 3) :
    (DiscreteMinkowski.latticePoints K (standardIntegerLattice 3)).ncard ≤ q₁ * q₂ * q₃ := by
  obtain ⟨V, hΛ, havoid⟩ := exists_unimodular_minima_difference_coordinates hK
  have hQ := isPaperConvexBody_image V hK
  have hq₁r : (0 : ℝ) < q₁ := by exact_mod_cast (hq₃.trans_le (hq₃₂.trans hq₂₁))
  have hq₂r : (0 : ℝ) < q₂ := by exact_mod_cast (hq₃.trans_le hq₃₂)
  have hq₃r : (0 : ℝ) < q₃ := by exact_mod_cast hq₃
  have hb := spatial_lattice_count_le_of_period_avoidance (isCompact_image V hc)
    hQ.2.1 (hQ.2.2.mono interior_subset) hq₃ hq₃₂ hq₂₁
    (by
      intro x hx y hy z hz hn
      obtain ⟨l, hl⟩ : ∃ l : Fin 3, z l ≠ 0 := by
        by_contra hh
        push Not at hh
        apply hn
        ext l
        exact hh l
      exact havoid 0 (by norm_num) q₁ hq₁r hfirst x hx y hy z hz l (Nat.zero_le _) hl)
    (by
      intro x hx y hy z hz hn
      exact havoid 1 (by norm_num) q₂ hq₂r hsecond x hx y hy z hz 1 (by norm_num) hn)
    (by
      intro x hx y hy z hz hn
      exact havoid 2 (by norm_num) q₃ hq₃r hthird x hx y hy z hz (Fin.last 2) (by norm_num) hn)
  rwa [ncard_latticePoints_image V hΛ] at hb

theorem spatial_floor_product_bound
    {K : Set (Fin 3 → ℝ)} (hc : IsCompact K)
    (hK : DiscreteMinkowski.IsPaperConvexBody K) :
    (DiscreteMinkowski.latticePoints K (standardIntegerLattice 3)).ncard ≤
      ⌊2 / DiscreteMinkowski.successiveMinimum K (standardIntegerLattice 3) 1 + 1⌋₊ *
      ⌊2 / DiscreteMinkowski.successiveMinimum K (standardIntegerLattice 3) 2 + 1⌋₊ *
      ⌊2 / DiscreteMinkowski.successiveMinimum K (standardIntegerLattice 3) 3 + 1⌋₊ := by
  let l := fun i => DiscreteMinkowski.successiveMinimum K (standardIntegerLattice 3) i
  have hdim : finrank ℝ (Fin 3 → ℝ) = 3 := Module.finrank_fin_fun ℝ
  have hp : ∀ i, 1 ≤ i → i ≤ 3 → 0 < l i := by
    intro i hi hi3
    exact DiscreteMinkowski.successiveMinimum_pos (Λ := standardIntegerLattice 3) hK hi
      (by rwa [hdim])
  have hm : ∀ i j, i ≤ j → j ≤ 3 → l i ≤ l j := by
    intro i j hij hj
    exact DiscreteMinkowski.successiveMinimum_mono_of_le_finrank
      (Λ := standardIntegerLattice 3) hK hij (by rwa [hdim])
  have hfloor : ∀ i j, 1 ≤ i → i ≤ j → j ≤ 3 →
      ⌊2 / l j + 1⌋₊ ≤ ⌊2 / l i + 1⌋₊ := by
    intro i j hi hij hj
    apply Nat.floor_mono
    have hdiv : 2 / l j ≤ 2 / l i := by
      apply (div_le_div_iff₀ (hp j (hi.trans hij) hj) (hp i hi (hij.trans hj))).mpr
      nlinarith [hm i j hij hj]
    linarith
  obtain ⟨_, hcrit₁⟩ := floor_reciprocal_minimum_threshold (hp 1 (by norm_num) (by norm_num))
  obtain ⟨_, hcrit₂⟩ := floor_reciprocal_minimum_threshold (hp 2 (by norm_num) (by norm_num))
  obtain ⟨hq₃, hcrit₃⟩ := floor_reciprocal_minimum_threshold (hp 3 (by norm_num) (by norm_num))
  exact spatial_lattice_count_le_of_minima_thresholds hc hK hq₃
    (hfloor 2 3 (by norm_num) (by norm_num) (by norm_num))
    (hfloor 1 2 (by norm_num) (by norm_num) (by norm_num)) hcrit₁ hcrit₂ hcrit₃

/-- The precise origin-symmetric dimension-three result quoted by the paper.
The source's difference-body argument also proves the preceding general form. -/
theorem symmetric_spatial_floor_product_bound
    {K : Set (Fin 3 → ℝ)} (hc : IsCompact K)
    (hK : DiscreteMinkowski.IsPaperConvexBody K)
    (_hsym : DiscreteMinkowski.IsOriginSymmetric K) :
    (DiscreteMinkowski.latticePoints K (standardIntegerLattice 3)).ncard ≤
      ⌊2 / DiscreteMinkowski.successiveMinimum K (standardIntegerLattice 3) 1 + 1⌋₊ *
      ⌊2 / DiscreteMinkowski.successiveMinimum K (standardIntegerLattice 3) 2 + 1⌋₊ *
      ⌊2 / DiscreteMinkowski.successiveMinimum K (standardIntegerLattice 3) 3 + 1⌋₊ :=
  spatial_floor_product_bound hc hK

end LatticeVolumeInterpolation
