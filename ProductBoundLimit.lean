import LviBasic
import DilationBridge
import UpperBound

/-!
# A lattice-point product bound implies the volume product bound

This is the limit argument following (1.4) in Freyer--Lucas. The counting
asymptotic and the scaling of successive minima come from the pinned
DiscreteMinkowski dependency.
-/

open MeasureTheory Filter Topology Module
open scoped BigOperators ENNReal Pointwise

namespace LatticeVolumeInterpolation

noncomputable section

private theorem tendsto_product_with_constants {d : ℕ} (lam c : ℕ → ℝ) :
    Tendsto (fun n : ℕ => ∏ i ∈ Finset.range d, (2 / lam i + c i / (n : ℝ))) atTop
      (𝓝 (∏ i ∈ Finset.range d, 2 / lam i)) := by
  apply tendsto_finsetProd
  intro i _
  have hzero : Tendsto (fun n : ℕ => c i / (n : ℝ)) atTop (𝓝 0) := by
    have hh : Tendsto (fun n : ℕ => c i * (1 / (n : ℝ))) atTop (𝓝 (c i * 0)) :=
      tendsto_const_nhds.mul tendsto_one_div_atTop_nhds_zero_nat
    simpa only [div_eq_mul_inv, one_mul, mul_zero] using hh
  simpa using (tendsto_const_nhds.add hzero)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The paper's limit step, with arbitrary constants independent of the refinement scale. -/
theorem product_bound_implies_volume_bound {K : Set E} (hK : DiscreteMinkowski.IsPaperConvexBody K)
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (c : ℕ → ℝ)
    (hbound : ∀ n : ℕ, 0 < n →
      ((DiscreteMinkowski.latticePoints K (((n : ℝ))⁻¹ • Λ)).ncard : ℝ) ≤
        ∏ i ∈ Finset.range (finrank ℝ E),
          (2 / DiscreteMinkowski.successiveMinimum K (((n : ℝ))⁻¹ • Λ) (i + 1) + c i)) :
    (volume K).toReal ≤
      (∏ i ∈ Finset.range (finrank ℝ E),
        2 / DiscreteMinkowski.successiveMinimum K Λ (i + 1)) *
        ZLattice.covolume Λ volume := by
  let d := finrank ℝ E
  let lam : ℕ → ℝ := fun i => DiscreteMinkowski.successiveMinimum K Λ (i + 1)
  have hcount := DiscreteMinkowski.tendsto_latticePoints_ncard hK Λ
  have hupper := tendsto_product_with_constants (d := d) lam c
  have hle : ∀ᶠ n : ℕ in atTop,
      ((DiscreteMinkowski.latticePoints K (((n : ℝ))⁻¹ • Λ)).ncard : ℝ) /
          (n : ℝ) ^ d ≤
        ∏ i ∈ Finset.range d, (2 / lam i + c i / (n : ℝ)) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
    have hinv : (0 : ℝ) < (n : ℝ)⁻¹ := inv_pos.mpr hnreal
    have hfactor : ∀ i ∈ Finset.range d,
        (2 / DiscreteMinkowski.successiveMinimum K (((n : ℝ))⁻¹ • Λ) (i + 1) + c i) /
          (n : ℝ) = 2 / lam i + c i / (n : ℝ) := by
      intro i hi
      rw [DiscreteMinkowski.successiveMinimum_smul_lattice hinv]
      dsimp [lam]
      have hpos := DiscreteMinkowski.successiveMinimum_pos (Λ := Λ) hK
        (by omega : 0 < i + 1) (by simpa [d] using Finset.mem_range.mp hi)
      field_simp
    have hrewrite :
        (∏ i ∈ Finset.range d,
          (2 / DiscreteMinkowski.successiveMinimum K (((n : ℝ))⁻¹ • Λ) (i + 1) + c i)) /
          (n : ℝ) ^ d =
        ∏ i ∈ Finset.range d, (2 / lam i + c i / (n : ℝ)) := by
      calc
        _ = ∏ i ∈ Finset.range d,
            (2 / DiscreteMinkowski.successiveMinimum K (((n : ℝ))⁻¹ • Λ) (i + 1) + c i) /
              (n : ℝ) := by rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]
        _ = _ := Finset.prod_congr rfl hfactor
    rw [← hrewrite]
    exact div_le_div_of_nonneg_right (hbound n hn) (pow_nonneg hnreal.le _)
  have hlimit := le_of_tendsto_of_tendsto hcount hupper hle
  exact (div_le_iff₀ (ZLattice.covolume_pos Λ volume)).mp hlimit

/-- The Riemann-sum limit in the paper's standard-lattice notation. Compactness
and convexity give measurability and a null frontier; the lattice has covolume one. -/
theorem tendsto_standardLattice_refinement {d : ℕ} {K : Set (Fin d → ℝ)}
    (hKc : IsCompact K) (hKb : DiscreteMinkowski.IsPaperConvexBody K) :
    Tendsto (fun k : ℕ =>
      ((DiscreteMinkowski.latticePoints K ((k : ℝ)⁻¹ • standardIntegerLattice d)).ncard : ℝ) /
        (k : ℝ) ^ d) atTop (𝓝 (volume K).toReal) := by
  have h := ZLattice.covolume.tendsto_card_div_pow (standardIntegerLattice d)
    (standardLatticeBasis d) hKc.isBounded hKc.isClosed.measurableSet
    (hKb.2.1.addHaar_frontier volume)
  simpa [Nat.card_coe_set_eq, DiscreteMinkowski.latticePoints_apply,
    Submodule.coe_pointwise_smul, Fintype.card_fin, measureReal_def,
    covolume_standardIntegerLattice] using h

/-- **Eq. (1.4), its implication to Minkowski's upper bound.** The hypothesis is
exactly a universal bound for bodies on the standard lattice, with constants
independent of the body. Apply it to integer dilates, then take the Riemann-sum limit. -/
theorem product_bound_implies_minkowski {d : ℕ} (c : ℕ → ℝ)
    (hbound : ∀ B : Set (Fin d → ℝ), IsCompact B →
      DiscreteMinkowski.IsPaperConvexBody B →
      ((DiscreteMinkowski.latticePoints B (standardIntegerLattice d)).ncard : ℝ) ≤
        ∏ i ∈ Finset.range d,
          (2 / DiscreteMinkowski.successiveMinimum B (standardIntegerLattice d) (i + 1) + c i))
    {K : Set (Fin d → ℝ)} (hKc : IsCompact K)
    (hKb : DiscreteMinkowski.IsPaperConvexBody K) :
    (volume K).toReal ≤ ∏ i ∈ Finset.range d,
      2 / DiscreteMinkowski.successiveMinimum K (standardIntegerLattice d) (i + 1) := by
  let lam : ℕ → ℝ := fun i =>
    DiscreteMinkowski.successiveMinimum K (standardIntegerLattice d) (i + 1)
  have hcount := tendsto_standardLattice_refinement hKc hKb
  have hupper := tendsto_product_with_constants (d := d) lam c
  apply le_of_tendsto_of_tendsto hcount hupper
  filter_upwards [eventually_gt_atTop 0] with k hk
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  have hB := hbound ((k : ℝ) • K) (hKc.smul (k : ℝ))
    (isPaperConvexBody_smul hkreal hKb)
  rw [ncard_latticePoints_smul_body hkreal.ne'] at hB
  simp_rw [successiveMinimum_smul_body hkreal] at hB
  have hfactor : ∀ i ∈ Finset.range d,
      (2 / (lam i / (k : ℝ)) + c i) / (k : ℝ) =
        2 / lam i + c i / (k : ℝ) := by
    intro i hi
    have hpos : 0 < lam i := DiscreteMinkowski.successiveMinimum_pos hKb
      (by omega) (by simpa using Finset.mem_range.mp hi)
    field_simp
  have hrewrite :
      (∏ i ∈ Finset.range d, (2 / (lam i / (k : ℝ)) + c i)) / (k : ℝ) ^ d =
        ∏ i ∈ Finset.range d, (2 / lam i + c i / (k : ℝ)) := by
    calc
      _ = ∏ i ∈ Finset.range d, (2 / (lam i / (k : ℝ)) + c i) / (k : ℝ) := by
        rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]
      _ = _ := Finset.prod_congr rfl hfactor
  rw [← hrewrite]
  exact div_le_div_of_nonneg_right hB (pow_nonneg hkreal.le _)

end

end LatticeVolumeInterpolation
