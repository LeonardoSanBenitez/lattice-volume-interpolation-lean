import BoundaryRowCount

/-!
# Coordinate-height control of the second successive minimum

Support for the horizontal-row route toward catalog item
`henk_schurmann_wills_boundary_bound`. A dilation whose vertical range lies
strictly between the two nearest nonzero integer heights contains lattice
points only on the horizontal axis. Their real span has dimension at most one.
-/

open Set MeasureTheory
open scoped Pointwise

namespace LatticeVolumeInterpolation

noncomputable section

/-- If the entire vertical range of `rP` lies inside `(-1,1)`, lattice
points of `rP` span at most one real dimension. -/
theorem finrank_scaled_lattice_span_le_one_of_narrow_height
    {P : Set (Fin 2 → ℝ)} (hc : IsCompact P) (hv : Convex ℝ P)
    (hsym : DiscreteMinkowski.IsOriginSymmetric P)
    {r : ℝ} (hr : 0 < r) (hlo : -1 < r * yLo P)
    (hhi : r * yHi P < 1) :
    Module.finrank ℝ (DiscreteMinkowski.scaledLatticeSpan P
      (standardIntegerLattice 2) r) ≤ 1 := by
  rw [DiscreteMinkowski.scaledLatticeSpan,
    DiscreteMinkowski.halfDifferenceBody_eq_self hv hsym]
  have hsubset : (r • P) ∩ (standardIntegerLattice 2 : Set (Fin 2 → ℝ)) ⊆
      Pi.spanSubset ℝ ({0} : Set (Fin 2)) := by
    rintro x ⟨hx, hxΛ⟩
    refine Pi.mem_spanSubset_iff.mpr ?_
    intro j hj
    have hj1 : j = 1 := by fin_cases j <;> simp_all
    subst j
    obtain ⟨p, hp, rfl⟩ := mem_smul_set.1 hx
    have hpy := mem_Icc_of_mem hc hv hp
    have hlow : -1 < (r • p) 1 := by
      simp only [Pi.smul_apply, smul_eq_mul]
      exact hlo.trans_le (mul_le_mul_of_nonneg_left hpy.1 hr.le)
    have hhigh : (r • p) 1 < 1 := by
      simp only [Pi.smul_apply, smul_eq_mul]
      exact (mul_le_mul_of_nonneg_left hpy.2 hr.le).trans_lt hhi
    obtain ⟨z, hz⟩ := (mem_standardIntegerLattice_iff 2 (r • p)).1 hxΛ
    have hz1 : (r • p) 1 = (z 1 : ℝ) := hz 1
    rw [hz1] at hlow hhigh ⊢
    have hzlow : (-1 : ℤ) < z 1 := by exact_mod_cast hlow
    have hzhigh : z 1 < (1 : ℤ) := by exact_mod_cast hhigh
    have : z 1 = 0 := by omega
    simp [this]
  calc
    Module.finrank ℝ (Submodule.span ℝ
      ((r • P) ∩ (standardIntegerLattice 2 : Set (Fin 2 → ℝ))))
        ≤ Module.finrank ℝ (Pi.spanSubset ℝ ({0} : Set (Fin 2))) :=
      Submodule.finrank_mono (Submodule.span_le.mpr hsubset)
    _ = 1 := by rw [Pi.dim_spanSubset]; simp

/-- The second successive minimum cannot be smaller than the reciprocal
half-height: below that scale every lattice point remains on the horizontal
axis. The reflection identity for the two heights is stated explicitly here
and discharged for symmetric bodies in the next bridge. -/
theorem reciprocal_half_height_le_second_minimum
    {P : Set (Fin 2 → ℝ)} (hc : IsCompact P)
    (hPb : DiscreteMinkowski.IsPaperConvexBody P)
    (hsym : DiscreteMinkowski.IsOriginSymmetric P)
    (hheight : 0 < yHi P) (hreflect : yLo P = -yHi P) :
    (yHi P)⁻¹ ≤ lam2 P 2 := by
  rw [lam2, DiscreteMinkowski.successiveMinimum_eq_sInf]
  have hdim : Module.finrank ℝ (Fin 2 → ℝ) = 2 := Module.finrank_fin_fun ℝ
  refine le_csInf (DiscreteMinkowski.minimaSet_nonempty hPb (by rw [hdim])) ?_
  rintro r ⟨hr, hrank⟩
  by_contra hnot
  have hsmall : r < (yHi P)⁻¹ := lt_of_not_ge hnot
  have hhi : r * yHi P < 1 := by
    calc
      r * yHi P < (yHi P)⁻¹ * yHi P :=
        mul_lt_mul_of_pos_right hsmall hheight
      _ = 1 := inv_mul_cancel₀ hheight.ne'
  have hlo : -1 < r * yLo P := by rw [hreflect]; nlinarith
  have hle := finrank_scaled_lattice_span_le_one_of_narrow_height hc hPb.2.1
    hsym hr hlo hhi
  omega

/-- In the paper's notation, `λ₂(P)` is at least twice the reciprocal
vertical height of an origin-symmetric planar body. -/
theorem two_div_height_le_second_minimum
    {P : Set (Fin 2 → ℝ)} (hc : IsCompact P)
    (hPb : DiscreteMinkowski.IsPaperConvexBody P)
    (hsym : DiscreteMinkowski.IsOriginSymmetric P) :
    2 / (yHi P - yLo P) ≤ lam2 P 2 := by
  have hreflect := yLo_eq_neg_yHi_of_symmetric hsym
  have hne : P.Nonempty := hPb.2.2.mono interior_subset
  obtain ⟨c, hcI⟩ := hPb.2.2
  have hcHeight := ((mem_interior_iff_rows hc hPb.2.1 hne c).1 hcI).1
  have hheight : 0 < yHi P := by
    rw [hreflect] at hcHeight
    rcases hcHeight with ⟨hlo, hhi⟩
    linarith
  have hrecip := reciprocal_half_height_le_second_minimum hc hPb hsym
    hheight hreflect
  have heq : 2 / (yHi P - yLo P) = (yHi P)⁻¹ := by
    rw [hreflect]
    field_simp
    ring
  rw [heq]
  exact hrecip

/-- The boundary estimate from horizontal rows and the split-section
concavity argument. The remaining premise says that the chosen horizontal
axis is a first-minimum direction. -/
theorem boundary_bound_of_central_first_minimum
    {P : Set (Fin 2 → ℝ)} (hP : IsLatticePolygon P)
    (hint : (interior P).Nonempty)
    (hsym : DiscreteMinkowski.IsOriginSymmetric P)
    (hfirst : 2 ≤ lam2 P 1 * (rowHi P 0 - rowLo P 0)) :
    (G2 (frontier P) : ℝ) / 2 ≤
      (volume P).toReal * (lam2 P 1 / 2 + lam2 P 2 / 2) := by
  have hc := hP.isCompact
  have hv := hP.convex
  have hne : P.Nonempty := hint.mono interior_subset
  have hPb : DiscreteMinkowski.IsPaperConvexBody P :=
    ⟨hc.isBounded, hv, hint⟩
  let H := yHi P - yLo P
  let W := rowHi P (yLo P) - rowLo P (yLo P)
  let C := rowHi P 0 - rowLo P 0
  let V := (volume P).toReal
  have hH : 0 < H := by
    obtain ⟨c, hcI⟩ := hint
    have h := ((mem_interior_iff_rows hc hv hne c).1 hcI).1
    rcases h with ⟨hlo, hhi⟩
    dsimp [H]
    linarith
  have hW : 0 ≤ W := by
    dsimp [W]
    apply sub_nonneg.mpr
    apply rowLo_le_rowHi hc
    apply (hsec_nonempty_iff hc hv hne _).2
    exact ⟨le_rfl, (yLo_le_yHi hc hv hne)⟩
  have hL : 0 ≤ lam2 P 1 :=
    DiscreteMinkowski.successiveMinimum_nonneg P (standardIntegerLattice 2) 1
  have harea : H * (W + C) / 2 ≤ V :=
    area_ge_symmetric_extreme_plus_central_section hc hv hne hsym
  have hrow : (G2 (frontier P) : ℝ) ≤ 2 * W + 2 * H :=
    boundary_count_le_symmetric_extreme_width_and_height hP hint hsym
  have hsecond : 2 / H ≤ lam2 P 2 :=
    two_div_height_le_second_minimum hc hPb hsym
  have hsecondH : 2 ≤ lam2 P 2 * H := by
    have := (div_le_iff₀ hH).mp hsecond
    nlinarith
  have hcentral : 2 * H ≤ lam2 P 1 * C * H := by
    change 2 ≤ lam2 P 1 * C at hfirst
    have := mul_le_mul_of_nonneg_right hfirst hH.le
    nlinarith
  have hparallel : 2 * W ≤ lam2 P 2 * H * W := by
    have := mul_le_mul_of_nonneg_right hsecondH hW
    nlinarith
  have hweighted : lam2 P 1 * H * (W + C) / 2 ≤ lam2 P 1 * V := by
    calc
      lam2 P 1 * H * (W + C) / 2 = lam2 P 1 * (H * (W + C) / 2) := by ring
      _ ≤ lam2 P 1 * V := mul_le_mul_of_nonneg_left harea hL
  have hmono : lam2 P 1 ≤ lam2 P 2 := by
    have hdim : Module.finrank ℝ (Fin 2 → ℝ) = 2 := Module.finrank_fin_fun ℝ
    exact DiscreteMinkowski.successiveMinimum_mono_of_le_finrank hPb
      (by omega) (by rw [hdim])
  have hrect : H * W ≤ V :=
    area_ge_symmetric_extreme_section_rectangle hc hv hne hsym
  have hgain : 0 ≤ (lam2 P 2 - lam2 P 1) * (V - H * W) :=
    mul_nonneg (sub_nonneg.mpr hmono) (sub_nonneg.mpr hrect)
  have hA : H ≤ lam2 P 1 * (V - H * W / 2) := by
    nlinarith [hweighted, hcentral]
  have hB : W ≤ lam2 P 2 * H * W / 2 := by
    nlinarith [hparallel]
  nlinarith [hrow, hgain, hA, hB]

end

end LatticeVolumeInterpolation
