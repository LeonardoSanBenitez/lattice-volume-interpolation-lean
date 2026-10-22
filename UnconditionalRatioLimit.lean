import PropOneSix
import DilationBridge
import PaperNotation

/-!
# Unconditional real-dilation volume/count limit

Supplement to catalog item `volume_lattice_point_limit`. The terminal
paper-route theorem remains the conditional Conjecture2 squeeze. Here the
already proved covering-radius bounds (1.15)--(1.16) give the classical
unconditional version, including the exact scaling of the covering radius.
-/

open Set MeasureTheory Filter Topology
open scoped Pointwise
set_option autoImplicit false

namespace LatticeVolumeInterpolation

theorem coveringSet_smul_body {n : ℕ} (K : Set (Fin n → ℝ)) {r : ℝ} (hr : 0 < r) :
    coveringSet (r • K) = r⁻¹ • coveringSet K := by
  ext t
  constructor
  · rintro ⟨ht, hcover⟩
    refine ⟨r * t, ⟨mul_pos hr ht, ?_⟩, ?_⟩
    · intro y
      obtain ⟨z, hz, hyz⟩ := hcover y
      refine ⟨z, hz, ?_⟩
      simpa only [smul_smul, mul_comm] using hyz
    · change r⁻¹ * (r * t) = t
      rw [← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
  · rintro ⟨s, ⟨hs, hcover⟩, rfl⟩
    refine ⟨mul_pos (inv_pos.mpr hr) hs, ?_⟩
    intro y
    obtain ⟨z, hz, hyz⟩ := hcover y
    refine ⟨z, hz, ?_⟩
    have he : (r⁻¹ * s) * r = s := by field_simp
    simpa only [smul_smul, smul_eq_mul, he] using hyz

theorem coveringRadius_smul_body {n : ℕ} (K : Set (Fin n → ℝ)) {r : ℝ} (hr : 0 < r) :
    coveringRadius (r • K) = coveringRadius K / r := by
  unfold coveringRadius
  rw [coveringSet_smul_body K hr, Real.sInf_smul_of_nonneg (inv_nonneg.mpr hr.le), smul_eq_mul]
  exact (div_eq_inv_mul _ _).symm

theorem volume_count_ratio_limit {n : ℕ} {K : Set (Fin n → ℝ)} (hK : IsConvexBody K) :
    Tendsto (fun r : ℝ => (volume (r • K)).toReal /
      ((DiscreteMinkowski.latticePoints (r • K) (standardIntegerLattice n)).ncard : ℝ))
      atTop (𝓝 1) := by
  have hmu : Tendsto (fun r : ℝ => coveringRadius K / r) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds.mul tendsto_inv_atTop_zero :
        Tendsto (fun r : ℝ => coveringRadius K * r⁻¹) atTop (𝓝 (coveringRadius K * 0)))
  have hU : Tendsto (fun r : ℝ => (1 + coveringRadius K / r) ^ n) atTop (𝓝 1) := by
    have hh : Tendsto (fun r : ℝ => 1 + coveringRadius K / r) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add hmu
    simpa using hh.pow n
  have hL : Tendsto (fun r : ℝ => (1 - coveringRadius K / r) ^ n) atTop (𝓝 1) := by
    have hh : Tendsto (fun r : ℝ => 1 - coveringRadius K / r) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub hmu
    simpa using hh.pow n
  have hsmall : ∀ᶠ r : ℝ in atTop, coveringRadius K / r ≤ 1 :=
    (hmu.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono (fun _ h => h.le)
  have hbounds : ∀ᶠ r : ℝ in atTop,
      (1 - coveringRadius K / r) ^ n ≤
        ((DiscreteMinkowski.latticePoints (r • K) (standardIntegerLattice n)).ncard : ℝ) /
          (volume (r • K)).toReal ∧
      ((DiscreteMinkowski.latticePoints (r • K) (standardIntegerLattice n)).ncard : ℝ) /
        (volume (r • K)).toReal ≤ (1 + coveringRadius K / r) ^ n := by
    filter_upwards [eventually_gt_atTop 0, hsmall] with r hr hsr
    have hkc : IsCompact K := hK.1
    have hrc : IsCompact (r • K) := hkc.smul r
    have hb := isPaperConvexBody_smul hr ((isConvexBody_iff K).mp hK).2
    have hvpos : 0 < (volume (r • K)).toReal :=
      ENNReal.toReal_pos (Measure.measure_pos_of_nonempty_interior volume hb.2.2).ne' hrc.measure_ne_top
    have hu := proposition_1_6_upper_by_translate_count hrc hb
    have hl := proposition_1_6_lower hrc hb (by rwa [coveringRadius_smul_body K hr])
    rw [coveringRadius_smul_body K hr] at hu hl
    have hi : ((DiscreteMinkowski.latticePoints (interior (r • K)) (standardIntegerLattice n)).ncard : ℝ) ≤
        ((DiscreteMinkowski.latticePoints (r • K) (standardIntegerLattice n)).ncard : ℝ) := by
      exact_mod_cast Set.ncard_le_ncard (Set.inter_subset_inter_left _ interior_subset)
        (DiscreteMinkowski.finite_inter_lattice hrc.isBounded (standardIntegerLattice n))
    constructor
    · apply (le_div_iff₀ hvpos).mpr
      simpa only [mul_comm] using hl.trans hi
    · apply (div_le_iff₀ hvpos).mpr
      simpa only [mul_comm] using hu
  have hd := hL.squeeze' hU (hbounds.mono fun _ h => h.1) (hbounds.mono fun _ h => h.2)
  simpa only [inv_div, inv_one] using hd.inv₀ (by norm_num : (1 : ℝ) ≠ 0)

end LatticeVolumeInterpolation
