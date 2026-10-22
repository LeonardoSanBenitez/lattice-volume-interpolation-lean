import PaperConjectures
import DilationBridge
import ProductBoundLimit

/-!
# The real-dilation ratio limit conditional on Conjecture 2

This follows the paper's squeeze argument, including the lower bound's
eventual smallness regime. No conjecture is asserted as a theorem.
-/

open Set MeasureTheory Filter Topology
open scoped BigOperators Pointwise

namespace LatticeVolumeInterpolation

private theorem reciprocal_scale_tendsto_zero (a : ℝ) :
    Tendsto (fun r : ℝ => a / r) atTop (𝓝 0) := by
  simpa only [div_eq_mul_inv, mul_zero] using
    (tendsto_const_nhds.mul tendsto_inv_atTop_zero :
      Tendsto (fun r : ℝ => a * r⁻¹) atTop (𝓝 (a * 0)))

theorem volume_count_ratio_limit_of_ratio_conjecture {n : ℕ} (hn : 0 < n)
    (hconj : BHWRatioConjecture n) {K : Set (Fin n → ℝ)} (hK : IsConvexBody K) :
    Tendsto (fun r : ℝ => (volume (r • K)).toReal /
      ((DiscreteMinkowski.latticePoints (r • K) (standardIntegerLattice n)).ncard : ℝ))
      atTop (𝓝 1) := by
  classical
  let l := fun i => DiscreteMinkowski.successiveMinimum K (standardIntegerLattice n) i
  let U := fun r : ℝ => ∏ i : Fin n, (1 + (i.1 + 1 : ℝ) * (l (i.1 + 1) / r) / 2)
  let L := fun r : ℝ => ∏ i : Fin n, (1 - (i.1 + 1 : ℝ) * (l (i.1 + 1) / r) / 2)
  have hU : Tendsto U atTop (𝓝 1) := by
    have hh : Tendsto U atTop (𝓝 (∏ _i : Fin n, (1 : ℝ))) := by
      apply tendsto_finsetProd
      intro i _
      have hh : Tendsto
          (fun r : ℝ => 1 + (i.1 + 1 : ℝ) * (l (i.1 + 1) / r) / 2)
          atTop (𝓝 (1 + (i.1 + 1 : ℝ) * 0 / 2)) := tendsto_const_nhds.add
        ((tendsto_const_nhds.mul (reciprocal_scale_tendsto_zero (l (i.1 + 1)))).div_const 2)
      simpa only [mul_zero, zero_div, add_zero] using hh
    simpa using hh
  have hL : Tendsto L atTop (𝓝 1) := by
    have hh : Tendsto L atTop (𝓝 (∏ _i : Fin n, (1 : ℝ))) := by
      apply tendsto_finsetProd
      intro i _
      have hh : Tendsto
          (fun r : ℝ => 1 - (i.1 + 1 : ℝ) * (l (i.1 + 1) / r) / 2)
          atTop (𝓝 (1 - (i.1 + 1 : ℝ) * 0 / 2)) := tendsto_const_nhds.sub
        ((tendsto_const_nhds.mul (reciprocal_scale_tendsto_zero (l (i.1 + 1)))).div_const 2)
      simpa only [mul_zero, zero_div, sub_zero] using hh
    simpa using hh
  have hsmall : ∀ᶠ r : ℝ in atTop, l n / r ≤ 2 / (n : ℝ) := by
    have hpos : (0 : ℝ) < 2 / (n : ℝ) := div_pos (by norm_num) (by exact_mod_cast hn)
    exact ((reciprocal_scale_tendsto_zero (l n)).eventually (gt_mem_nhds hpos)).mono
      (fun _ hh => hh.le)
  have hbounds : ∀ᶠ r : ℝ in atTop,
      L r ≤ ((DiscreteMinkowski.latticePoints (r • K) (standardIntegerLattice n)).ncard : ℝ) /
        (volume (r • K)).toReal ∧
      ((DiscreteMinkowski.latticePoints (r • K) (standardIntegerLattice n)).ncard : ℝ) /
        (volume (r • K)).toReal ≤ U r := by
    filter_upwards [eventually_gt_atTop 0, hsmall] with r hr hsr
    have hb := isPaperConvexBody_smul hr ((isConvexBody_iff K).mp hK).2
    have hkc : IsCompact K := hK.1
    have hrc : IsCompact (r • K) := hkc.smul r
    have hrbody : IsConvexBody (r • K) := (isConvexBody_iff _).mpr ⟨hrc, hb⟩
    have hvpos : 0 < (volume (r • K)).toReal :=
      ENNReal.toReal_pos (Measure.measure_pos_of_nonempty_interior volume hb.2.2).ne' hrc.measure_ne_top
    have hu := hconj.1 (r • K) hrbody
    have hl := hconj.2.1 (r • K) hrbody
      (by rwa [successiveMinimum_smul_body hr])
    simp_rw [successiveMinimum_smul_body hr] at hu hl
    have hi : ((DiscreteMinkowski.latticePoints (interior (r • K)) (standardIntegerLattice n)).ncard : ℝ) ≤
        ((DiscreteMinkowski.latticePoints (r • K) (standardIntegerLattice n)).ncard : ℝ) := by
      exact_mod_cast Set.ncard_le_ncard (Set.inter_subset_inter_left _ interior_subset)
        (DiscreteMinkowski.finite_inter_lattice hrc.isBounded (standardIntegerLattice n))
    constructor
    · apply (le_div_iff₀ hvpos).mpr
      simpa only [L, l, mul_comm] using hl.trans hi
    · apply (div_le_iff₀ hvpos).mpr
      simpa only [U, l, mul_comm] using hu
  have hdensity := hL.squeeze' hU (hbounds.mono fun _ hh => hh.1) (hbounds.mono fun _ hh => hh.2)
  have hh := hdensity.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  simpa only [inv_div, inv_one] using hh

end LatticeVolumeInterpolation
