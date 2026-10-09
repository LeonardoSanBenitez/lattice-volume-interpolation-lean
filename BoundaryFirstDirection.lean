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

end

end LatticeVolumeInterpolation
