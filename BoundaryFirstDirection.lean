import BoundaryMinima
import Unimodular

/-!
# Aligning the first-minimum direction for the planar boundary estimate

The Henk--Schürmann--Wills proof chooses a first-minimum lattice vector as
the horizontal direction. The row proof uses its central chord instead of
enumerating all primitive facet normals.
-/

open Set MeasureTheory
open scoped Pointwise

namespace LatticeVolumeInterpolation

noncomputable section

/-- Any nonzero horizontal integer point of `λ₁ P` forces the central
horizontal chord of a symmetric body to have width at least `2/λ₁`. -/
theorem central_width_of_horizontal_first_point
    {P : Set (Fin 2 → ℝ)} (hc : IsCompact P)
    (hsym : DiscreteMinkowski.IsOriginSymmetric P)
    {v : Fin 2 → ℝ} (hvΛ : v ∈ standardIntegerLattice 2)
    (hv0 : v ≠ 0) (hvy : v 1 = 0)
    (hvP : v ∈ lam2 P 1 • P) :
    2 ≤ lam2 P 1 * (rowHi P 0 - rowLo P 0) := by
  obtain ⟨z, hz⟩ := (mem_standardIntegerLattice_iff_castCoords v).1 hvΛ
  have hz0 : z 0 ≠ 0 := by
    intro heq
    apply hv0
    funext i
    fin_cases i
    · simp [hz, castCoords, heq]
    · simpa [hvy]
  have hzabs : 1 ≤ |(z 0 : ℝ)| := by
    have : (1 : ℤ) ≤ |z 0| := Int.one_le_abs hz0
    exact_mod_cast this
  obtain ⟨p, hp, hpv⟩ := mem_smul_set.1 hvP
  have hpy : p 1 = 0 := by
    -- Positivity follows from the nonzero first-minimum point.
    have hLam : lam2 P 1 ≠ 0 := by
      intro heq
      apply hv0
      rw [← hpv, heq, zero_smul]
    have hy := congrFun hpv 1
    simp only [Pi.smul_apply, smul_eq_mul] at hy
    rw [hvy] at hy
    exact (mul_eq_zero.mp hy).resolve_left hLam
  have hpneg : -p ∈ P := by
    have h : -p ∈ -P := Set.neg_mem_neg.mpr hp
    change -P = P at hsym
    rwa [hsym] at h
  have hppt : pt (p 0) 0 ∈ P := by
    convert hp using 1
    ext i; fin_cases i <;> simp [pt, hpy]
  have hnpt : pt (-p 0) 0 ∈ P := by
    convert hpneg using 1
    ext i; fin_cases i <;> simp [pt, hpy]
  have hhi := le_rowHi hc hppt
  have hlo := rowLo_le hc hnpt
  have hhi' := le_rowHi hc hnpt
  have hlo' := rowLo_le hc hppt
  have hvx := congrFun hpv 0
  simp only [Pi.smul_apply, smul_eq_mul] at hvx
  have hvzx : (v 0) = (z 0 : ℝ) := congrFun hz 0
  have hLamNonneg : 0 ≤ lam2 P 1 :=
    DiscreteMinkowski.successiveMinimum_nonneg P (standardIntegerLattice 2) 1
  have hhiM := mul_le_mul_of_nonneg_left hhi hLamNonneg
  have hloM := mul_le_mul_of_nonneg_left hlo hLamNonneg
  have hhiM' := mul_le_mul_of_nonneg_left hhi' hLamNonneg
  have hloM' := mul_le_mul_of_nonneg_left hlo' hLamNonneg
  by_cases hsign : 0 ≤ (z 0 : ℝ)
  · rw [abs_of_nonneg hsign] at hzabs
    nlinarith
  · have hneg : (z 0 : ℝ) < 0 := lt_of_not_ge hsign
    rw [abs_of_neg hneg] at hzabs
    nlinarith

/-- The horizontal gauge vector is the complete remaining directional input
for the row-based version of the Henk--Schürmann--Wills bound. -/
theorem boundary_bound_of_horizontal_first_gauge
    {P : Set (Fin 2 → ℝ)} (hP : IsLatticePolygon P)
    (hint : (interior P).Nonempty)
    (hsym : DiscreteMinkowski.IsOriginSymmetric P)
    {v : Fin 2 → ℝ} (hvΛ : v ∈ standardIntegerLattice 2)
    (hv0 : v ≠ 0) (hvy : v 1 = 0)
    (hg : gauge P v ≤ lam2 P 1) :
    (G2 (frontier P) : ℝ) / 2 ≤
      (volume P).toReal * (lam2 P 1 / 2 + lam2 P 2 / 2) := by
  have hc := hP.isCompact
  have hb : DiscreteMinkowski.IsPaperConvexBody P :=
    ⟨hc.isBounded, hP.convex, hint⟩
  have hdim : Module.finrank ℝ (Fin 2 → ℝ) = 2 := Module.finrank_fin_fun ℝ
  have hpos : 0 < lam2 P 1 :=
    DiscreteMinkowski.successiveMinimum_pos hb (by omega) (by rw [hdim]; norm_num)
  have hclosure := (DiscreteMinkowski.mem_closure_smul_iff_gauge_le hb hpos v).2
    (by rwa [DiscreteMinkowski.halfDifferenceBody_eq_self hP.convex hsym])
  rw [DiscreteMinkowski.halfDifferenceBody_eq_self hP.convex hsym] at hclosure
  have hclosed : IsClosed (lam2 P 1 • P) := (hc.smul _).isClosed
  rw [hclosed.closure_eq] at hclosure
  exact boundary_bound_of_central_first_minimum hP hint hsym
    (central_width_of_horizontal_first_point hc hsym hvΛ hv0 hvy hclosure)

/-- The greedy flag construction realizes the first successive minimum by a
nonzero lattice vector at the gauge level. -/
theorem exists_first_minimum_lattice_vector
    {P : Set (Fin 2 → ℝ)}
    (hPb : DiscreteMinkowski.IsPaperConvexBody P)
    (hsym : DiscreteMinkowski.IsOriginSymmetric P) :
    ∃ v : Fin 2 → ℝ, v ∈ standardIntegerLattice 2 ∧ v ≠ 0 ∧
      gauge P v ≤ lam2 P 1 := by
  have hdim : Module.finrank ℝ (Fin 2 → ℝ) = 2 := Module.finrank_fin_fun ℝ
  let v := DiscreteMinkowski.flagVector P (standardIntegerLattice 2) 0
  have hvΛ : v ∈ standardIntegerLattice 2 :=
    DiscreteMinkowski.flagVector_mem 0
      (DiscreteMinkowski.greedyChoice_flagSpan hPb (by rw [hdim]; norm_num))
  have hv0 : v ≠ 0 :=
    (linearIndependent_flagVector hPb).ne_zero (0 : Fin 2)
  have hg := gauge_flagVector_le_successiveMinimum
    (Λ := standardIntegerLattice 2) (k := 0) hPb (by rw [hdim]; norm_num)
  rw [DiscreteMinkowski.halfDifferenceBody_eq_self hPb.2.1 hsym] at hg
  exact ⟨v, hvΛ, hv0, hg⟩

/-- Align the first flag vector horizontally by an integer unimodular map.
The two-vector flag is used only to obtain an integral automorphism. -/
theorem exists_unimodular_horizontal_first_vector
    {P : Set (Fin 2 → ℝ)}
    (hPb : DiscreteMinkowski.IsPaperConvexBody P)
    (hsym : DiscreteMinkowski.IsOriginSymmetric P) :
    ∃ (V : (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ)) (w : Fin 2 → ℝ),
      (∀ x, V x ∈ standardIntegerLattice 2 ↔ x ∈ standardIntegerLattice 2) ∧
      |LinearMap.det (V : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ))| = 1 ∧
      w ∈ standardIntegerLattice 2 ∧ w ≠ 0 ∧ w 1 = 0 ∧
      gauge (V '' P) w ≤ lam2 (V '' P) 1 := by
  classical
  have hdim : Module.finrank ℝ (Fin 2 → ℝ) = 2 := Module.finrank_fin_fun ℝ
  let v : Fin 2 → (Fin 2 → ℝ) := fun k =>
    DiscreteMinkowski.flagVector P (standardIntegerLattice 2) k.1
  have hvΛ : ∀ k, v k ∈ standardIntegerLattice 2 := fun k =>
    DiscreteMinkowski.flagVector_mem k.1
      (DiscreteMinkowski.greedyChoice_flagSpan hPb (by rw [hdim]; exact k.2))
  have hvind : LinearIndependent ℝ v := linearIndependent_flagVector hPb
  choose z hz using fun k => (mem_standardIntegerLattice_iff_castCoords (v k)).1 (hvΛ k)
  have hzind : LinearIndependent ℤ z := by
    rw [Fintype.linearIndependent_iff] at hvind ⊢
    intro g hg k
    have hreal : ∑ j, (g j : ℝ) • v j = 0 := by
      funext l
      have := congrFun hg l
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
      simp only [hz, castCoords]
      exact_mod_cast this
    exact_mod_cast hvind _ hreal k
  obtain ⟨U, hU⟩ := exists_triangularizing 2 z hzind
  obtain ⟨V, hV, hVs, hdet⟩ := realize_unimodular U
  have hΛ := mem_lattice_iff_of_realize V hV hVs
  let w := V (v 0)
  have hwΛ : w ∈ standardIntegerLattice 2 := (hΛ (v 0)).2 (hvΛ 0)
  have hw0 : w ≠ 0 := fun h => (hvind.ne_zero 0) (V.injective (by simpa [w] using h))
  have hwy : w 1 = 0 := by
    simp only [w, hz 0, hV, castCoords]
    exact_mod_cast hU 0 1 (by decide)
  have hg := gauge_flagVector_le_successiveMinimum
    (Λ := standardIntegerLattice 2) (k := 0) hPb (by rw [hdim]; norm_num)
  rw [DiscreteMinkowski.halfDifferenceBody_eq_self hPb.2.1 hsym] at hg
  have hwg : gauge (V '' P) w ≤ lam2 (V '' P) 1 := by
    change gauge (V '' P) (V (v 0)) ≤
      DiscreteMinkowski.successiveMinimum (V '' P) (standardIntegerLattice 2) 1
    rw [gauge_image_apply V P (v 0), successiveMinimum_image V hΛ]
    exact hg
  exact ⟨V, w, hΛ, hdet, hwΛ, hw0, hwy, hwg⟩

/-- An integer-preserving real linear automorphism sends a lattice polygon
to a lattice polygon. -/
theorem IsLatticePolygon.image_unimodular {P : Set (Fin 2 → ℝ)}
    (hP : IsLatticePolygon P)
    (V : (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ))
    (hΛ : ∀ x, V x ∈ standardIntegerLattice 2 ↔ x ∈ standardIntegerLattice 2) :
    IsLatticePolygon (V '' P) := by
  classical
  obtain ⟨S, hS, rfl⟩ := hP
  refine ⟨S.image V, fun s hs => ?_, ?_⟩
  · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hs
    exact (hΛ t).2 (hS t ht)
  · rw [Finset.coe_image]
    exact V.toLinearMap.image_convexHull _

/-- Origin symmetry is invariant under a linear automorphism. -/
theorem symmetric_image_linearEquiv {P : Set (Fin 2 → ℝ)}
    (hsym : DiscreteMinkowski.IsOriginSymmetric P)
    (V : (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ)) :
    DiscreteMinkowski.IsOriginSymmetric (V '' P) := by
  change -P = P at hsym
  change -(V '' P) = V '' P
  ext y
  constructor
  · intro hy
    rw [Set.mem_neg] at hy
    obtain ⟨x, hx, hxy⟩ := hy
    have hnx : -x ∈ P := by
      have : -x ∈ -P := Set.neg_mem_neg.mpr hx
      rwa [hsym] at this
    refine ⟨-x, hnx, ?_⟩
    rw [map_neg, hxy, neg_neg]
  · rintro ⟨x, hx, rfl⟩
    rw [Set.mem_neg]
    have hnx : -x ∈ P := by
      have : -x ∈ -P := Set.neg_mem_neg.mpr hx
      rwa [hsym] at this
    exact ⟨-x, hnx, by simp⟩

/-- The lattice boundary count is unchanged by an integer-preserving real
linear automorphism. -/
theorem boundary_count_image_unimodular (P : Set (Fin 2 → ℝ))
    (V : (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ))
    (hΛ : ∀ x, V x ∈ standardIntegerLattice 2 ↔ x ∈ standardIntegerLattice 2) :
    G2 (frontier (V '' P)) = G2 (frontier P) := by
  let W := LinearEquiv.toContinuousLinearEquiv V
  have hfront : frontier (V '' P) = V '' frontier P := by
    simpa [W] using (W.toHomeomorph.image_frontier P).symm
  rw [hfront]
  exact ncard_latticePoints_image V hΛ (frontier P)

/-- The planar Henk--Schürmann--Wills boundary bound (Eq. (5.2)) for a
centrally symmetric lattice polygon. The proof combines the source's
first-minimum alignment and concave-section estimate with exact row counts. -/
theorem henk_schurmann_wills_boundary_bound
    {P : Set (Fin 2 → ℝ)} (hP : IsLatticePolygon P)
    (hint : (interior P).Nonempty)
    (hsym : DiscreteMinkowski.IsOriginSymmetric P) :
    (G2 (frontier P) : ℝ) / 2 ≤
      (volume P).toReal * (lam2 P 1 / 2 + lam2 P 2 / 2) := by
  have hPb : DiscreteMinkowski.IsPaperConvexBody P :=
    ⟨hP.isCompact.isBounded, hP.convex, hint⟩
  obtain ⟨V, w, hΛ, hdet, hwΛ, hw0, hwy, hwg⟩ :=
    exists_unimodular_horizontal_first_vector hPb hsym
  have hQ : IsLatticePolygon (V '' P) := hP.image_unimodular V hΛ
  have hQb := isPaperConvexBody_image V hPb
  have hQsym := symmetric_image_linearEquiv hsym V
  have hbound := boundary_bound_of_horizontal_first_gauge hQ hQb.2.2 hQsym
    hwΛ hw0 hwy hwg
  rw [boundary_count_image_unimodular P V hΛ,
    volume_image_of_det V hdet P] at hbound
  simp only [lam2, successiveMinimum_image V hΛ] at hbound
  exact hbound

end

end LatticeVolumeInterpolation
