import PlanarRows
import ConcaveIntegralBounds

/-!
# Planar section estimate for the Henk–Schürmann–Wills bound

Catalog item `henk_schurmann_wills_boundary_bound` (Sec. 5, Eq. (5.2)),
source Lemma 3.1 specialized to dimension two. The source compares the area
under the two support edges parallel to the first-minimum vector with half the
polygon's total area. The analytic core is below: when the two extreme parallel
sections have equal length, their common length times the full height is at
most the area. Central symmetry will give the equal-length premise when this
lemma is connected to the lattice polygon's edge and facet data.
-/

open Set MeasureTheory

namespace LatticeVolumeInterpolation

noncomputable section

/-- Splitting a concave section at its central height retains the stronger
trapezoid bound involving the central section. -/
theorem concave_integral_midpoint_chords {f : ℝ → ℝ} {a b : ℝ}
    (ha : a ≤ 0) (hb : 0 ≤ b) (hf : ConcaveOn ℝ (Icc a b) f) :
    ((f a + f 0) / 2) * (0 - a) +
      ((f 0 + f b) / 2) * (b - 0) ≤ ∫ t in a..b, f t := by
  have hab : a ≤ b := ha.trans hb
  have hleft : ConcaveOn ℝ (Icc a 0) f :=
    hf.subset (Icc_subset_Icc_right hb) (convex_Icc _ _)
  have hright : ConcaveOn ℝ (Icc 0 b) f :=
    hf.subset (Icc_subset_Icc_left ha) (convex_Icc _ _)
  have hi1 := concave_intervalIntegrable ha hleft
  have hi2 := concave_intervalIntegrable hb hright
  have h1 := concave_integral_chord_le ha hleft
  have h2 := concave_integral_chord_le hb hright
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
  linarith

/-- A convex body's area dominates the rectangle whose width is its common
top and bottom section length. This is the planar concave-section part of the
Henk–Schürmann–Wills volume estimate. -/
theorem area_ge_extreme_section_rectangle {P : Set (Fin 2 → ℝ)}
    (hc : IsCompact P) (hv : Convex ℝ P) (hne : P.Nonempty)
    (hwidth : rowHi P (yLo P) - rowLo P (yLo P) =
      rowHi P (yHi P) - rowLo P (yHi P)) :
    (yHi P - yLo P) * (rowHi P (yLo P) - rowLo P (yLo P)) ≤
      (volume P).toReal := by
  have hab := yLo_le_yHi hc hv hne
  have hconc := concaveOn_rowWidth hc hv hne
  have hchord := concave_integral_chord_le hab hconc
  rw [← hwidth] at hchord
  have hintnonneg : 0 ≤ ∫ t in (yLo P)..(yHi P),
      (rowHi P t - rowLo P t) := by
    refine intervalIntegral.integral_nonneg hab fun t ht => ?_
    exact sub_nonneg.2 (rowLo_le_rowHi hc ((hsec_nonempty_iff hc hv hne t).2 ht))
  have hvol := volume_eq_integral_rows hc hv hne
  rw [hvol, ENNReal.toReal_ofReal hintnonneg]
  nlinarith

/-- The vertical range of an origin-symmetric planar set is symmetric. -/
theorem yLo_eq_neg_yHi_of_symmetric {P : Set (Fin 2 → ℝ)}
    (hsym : DiscreteMinkowski.IsOriginSymmetric P) : yLo P = -yHi P := by
  change -P = P at hsym
  have hneg (x : Fin 2 → ℝ) : x ∈ P ↔ -x ∈ P := by
    constructor
    · intro hx
      have h : -x ∈ -P := Set.neg_mem_neg.mpr hx
      rw [hsym] at h
      exact h
    · intro hx
      have h : -(-x) ∈ -P := Set.neg_mem_neg.mpr hx
      rw [hsym, neg_neg] at h
      exact h
  have hIm : ((fun x : Fin 2 → ℝ => x 1) '' P) =
      -((fun x : Fin 2 → ℝ => x 1) '' P) := by
    ext t
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [Set.mem_neg]
      exact ⟨-x, (hneg x).mp hx, by simp⟩
    · intro ht
      rw [Set.mem_neg] at ht
      obtain ⟨x, hx, hxt⟩ := ht
      refine ⟨-x, (hneg x).mp hx, ?_⟩
      simpa using congrArg Neg.neg hxt
  unfold yLo yHi
  calc
    sInf ((fun x : Fin 2 → ℝ => x 1) '' P) =
        sInf (-((fun x : Fin 2 → ℝ => x 1) '' P)) := congrArg sInf hIm
    _ = -sSup ((fun x : Fin 2 → ℝ => x 1) '' P) := Real.sInf_neg _

/-- Central symmetry identifies the lower extreme horizontal section with the
reflection of the upper one. -/
theorem symmetric_extreme_section_width_eq {P : Set (Fin 2 → ℝ)}
    (hsym : DiscreteMinkowski.IsOriginSymmetric P) :
    rowHi P (yLo P) - rowLo P (yLo P) =
      rowHi P (yHi P) - rowLo P (yHi P) := by
  have hlo := yLo_eq_neg_yHi_of_symmetric hsym
  change -P = P at hsym
  have hneg (x : Fin 2 → ℝ) : x ∈ P ↔ -x ∈ P := by
    constructor
    · intro hx
      have h : -x ∈ -P := Set.neg_mem_neg.mpr hx
      rw [hsym] at h
      exact h
    · intro hx
      have h : -(-x) ∈ -P := Set.neg_mem_neg.mpr hx
      rw [hsym, neg_neg] at h
      exact h
  have hsecEq : hsec P (yLo P) = -(hsec P (yHi P)) := by
    ext s
    rw [Set.mem_neg]
    change pt s (yLo P) ∈ P ↔ pt (-s) (yHi P) ∈ P
    rw [hlo]
    have hpt : -(pt s (-yHi P)) = pt (-s) (yHi P) := by
      ext i; fin_cases i <;> simp [pt]
    rw [← hpt]
    exact hneg _
  unfold rowHi rowLo
  rw [hsecEq, Real.sSup_neg, Real.sInf_neg]
  ring

/-- The symmetric planar case of the section-volume estimate used by
Henk–Schürmann–Wills Lemma 3.1. -/
theorem area_ge_symmetric_extreme_section_rectangle {P : Set (Fin 2 → ℝ)}
    (hc : IsCompact P) (hv : Convex ℝ P) (hne : P.Nonempty)
    (hsym : DiscreteMinkowski.IsOriginSymmetric P) :
    (yHi P - yLo P) * (rowHi P (yLo P) - rowLo P (yLo P)) ≤
      (volume P).toReal :=
  area_ge_extreme_section_rectangle hc hv hne
    (symmetric_extreme_section_width_eq hsym)

/-- The source concavity argument split at the central section. This sharper
form supplies the area allocated to the nonhorizontal boundary rows. -/
theorem area_ge_symmetric_extreme_plus_central_section {P : Set (Fin 2 → ℝ)}
    (hc : IsCompact P) (hv : Convex ℝ P) (hne : P.Nonempty)
    (hsym : DiscreteMinkowski.IsOriginSymmetric P) :
    (yHi P - yLo P) *
      ((rowHi P (yLo P) - rowLo P (yLo P)) +
        (rowHi P 0 - rowLo P 0)) / 2 ≤ (volume P).toReal := by
  have hab := yLo_le_yHi hc hv hne
  have hlo := yLo_eq_neg_yHi_of_symmetric hsym
  have hwidth := symmetric_extreme_section_width_eq hsym
  have hzero : 0 ≤ yHi P := by rw [hlo] at hab; linarith
  have ha : yLo P ≤ 0 := by rw [hlo]; linarith
  have hconc := concaveOn_rowWidth hc hv hne
  have hmid := concave_integral_midpoint_chords ha hzero hconc
  have hintnonneg : 0 ≤ ∫ t in (yLo P)..(yHi P),
      (rowHi P t - rowLo P t) := by
    refine intervalIntegral.integral_nonneg hab fun t ht => ?_
    exact sub_nonneg.2 (rowLo_le_rowHi hc ((hsec_nonempty_iff hc hv hne t).2 ht))
  have hvol := volume_eq_integral_rows hc hv hne
  rw [hvol, ENNReal.toReal_ofReal hintnonneg]
  rw [hlo] at hmid hwidth ⊢
  nlinarith

/-- The final two-dimensional arithmetic step in the Henk–Schürmann–Wills
proof. `A` and `B` are respectively the sums of the origin-triangle areas
over edges whose primitive normals do and do not annihilate a first-minimum
vector. The hypotheses are exactly the polygon-edge decomposition and the
specialized volume estimate that remain to be connected to `P`. -/
theorem boundary_bound_of_pyramid_partition {P : Set (Fin 2 → ℝ)}
    (hPb : DiscreteMinkowski.IsPaperConvexBody P) (A B : ℝ)
    (harea : A + B = (volume P).toReal)
    (hedges : (G2 (frontier P) : ℝ) / 2 ≤ lam2 P 1 * A + lam2 P 2 * B)
    (hparallel : 2 * B ≤ (volume P).toReal) :
    (G2 (frontier P) : ℝ) / 2 ≤
      (volume P).toReal * (lam2 P 1 / 2 + lam2 P 2 / 2) := by
  have hdim : Module.finrank ℝ (Fin 2 → ℝ) = 2 := Module.finrank_fin_fun ℝ
  have hmono : lam2 P 1 ≤ lam2 P 2 :=
    DiscreteMinkowski.successiveMinimum_mono_of_le_finrank hPb (by omega)
      (by rw [hdim])
  have hBA : 0 ≤ A - B := by linarith
  have hgain := mul_nonneg (sub_nonneg.mpr hmono) hBA
  have hidentity : (volume P).toReal * (lam2 P 1 / 2 + lam2 P 2 / 2) -
      (lam2 P 1 * A + lam2 P 2 * B) =
      (lam2 P 2 - lam2 P 1) * (A - B) / 2 := by
    rw [← harea]
    ring
  linarith

/-- The symmetric-body version of the source route. The remaining obligations
are the two lattice-polygon facet identities: the origin-triangle areas sum to
the total area, and primitive normals bound boundary lattice points by their
weighted area sum. -/
theorem boundary_bound_of_symmetric_pyramid_partition {P : Set (Fin 2 → ℝ)}
    (hc : IsCompact P) (hv : Convex ℝ P) (hint : (interior P).Nonempty)
    (hsym : DiscreteMinkowski.IsOriginSymmetric P) (A B : ℝ)
    (harea : A + B = (volume P).toReal)
    (hB : B = (yHi P - yLo P) *
      (rowHi P (yLo P) - rowLo P (yLo P)) / 2)
    (hedges : (G2 (frontier P) : ℝ) / 2 ≤ lam2 P 1 * A + lam2 P 2 * B) :
    (G2 (frontier P) : ℝ) / 2 ≤
      (volume P).toReal * (lam2 P 1 / 2 + lam2 P 2 / 2) := by
  have hparallel : 2 * B ≤ (volume P).toReal := by
    have hsection := area_ge_symmetric_extreme_section_rectangle hc hv
      ⟨hint.some, interior_subset hint.some_mem⟩ hsym
    rw [hB]
    linarith
  exact boundary_bound_of_pyramid_partition ⟨hc.isBounded, hv, hint⟩ A B
    harea hedges hparallel

end

end LatticeVolumeInterpolation
