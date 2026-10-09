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

/-- Central symmetry identifies the lower extreme horizontal section with the
reflection of the upper one. -/
theorem symmetric_extreme_section_width_eq {P : Set (Fin 2 → ℝ)}
    (hsym : DiscreteMinkowski.IsOriginSymmetric P) :
    rowHi P (yLo P) - rowLo P (yLo P) =
      rowHi P (yHi P) - rowLo P (yHi P) := by
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
  have hlo : yLo P = -yHi P := by
    unfold yLo yHi
    calc
      sInf ((fun x : Fin 2 → ℝ => x 1) '' P) =
          sInf (-((fun x : Fin 2 → ℝ => x 1) '' P)) := congrArg sInf hIm
      _ = -sSup ((fun x : Fin 2 → ℝ => x 1) '' P) := Real.sInf_neg _
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

end

end LatticeVolumeInterpolation
