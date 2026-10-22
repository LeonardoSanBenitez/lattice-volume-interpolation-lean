import PlanarRows
import SeparatedIntervals

/-!
# Residue-grouped planar rows

Catalog items `bhw_lattice_conjecture_dimension_two_symmetric` and
`bhw_lattice_conjecture_dimension_three_symmetric`.

Malikiosis's slice decomposition bounds the planar lattice count by `q₁ q₂`
from two exact difference-avoidance conditions in an adapted lattice frame.
The successive-minimum instantiation is a separate geometric obligation.
-/

open Set
open scoped BigOperators

namespace LatticeVolumeInterpolation

noncomputable section

/-- Source Lemma 2.1 at the horizontal level forces every closed row to
have length strictly smaller than `q₁`. -/
theorem row_width_lt_of_horizontal_avoidance
    {P : Set (Fin 2 → ℝ)} (hc : IsCompact P) (hv : Convex ℝ P)
    {q₁ : ℕ} (hq₁ : 0 < q₁)
    (havoid : ∀ x ∈ P, ∀ y ∈ P, x - y ≠ pt (q₁ : ℝ) 0)
    {t : ℝ} (ht : (hsec P t).Nonempty) :
    rowHi P t - rowLo P t < q₁ := by
  by_contra h
  have hlen : (q₁ : ℝ) ≤ rowHi P t - rowLo P t := le_of_not_gt h
  have hqr : (0 : ℝ) ≤ q₁ := by positivity
  have hx : pt (rowLo P t + q₁) t ∈ P := by
    apply pt_mem_iff_mem_hsec.mpr
    rw [hsec_eq_Icc_rows hc hv ht]
    constructor <;> linarith
  have hy := pt_rowLo_mem hc ht
  apply havoid _ hx _ hy
  apply vec2_ext <;> simp [pt]

/-- Equal residue labels for two different heights convert a horizontal
period collision into a forbidden nonhorizontal lattice difference. -/
theorem row_intervals_separated_of_period_avoidance
    {P : Set (Fin 2 → ℝ)} (hc : IsCompact P) (hv : Convex ℝ P)
    {q₂ : ℕ}
    (havoid : ∀ x ∈ P, ∀ y ∈ P, ∀ u v : ℤ, v ≠ 0 →
      x - y ≠ pt ((q₂ : ℝ) * u) ((q₂ : ℝ) * v))
    {s t : ℤ} (hs : (hsec P (s : ℝ)).Nonempty)
    (ht : (hsec P (t : ℝ)).Nonempty)
    (hlabel : (s : ZMod q₂) = (t : ZMod q₂)) (hne : s ≠ t) :
    ∀ x ∈ Icc (rowLo P s) (rowHi P s),
      ∀ y ∈ Icc (rowLo P t) (rowHi P t),
        ∀ k : ℤ, x - y ≠ (q₂ : ℝ) * k := by
  intro x hx y hy k hxy
  have hxP : pt x s ∈ P := by
    apply pt_mem_iff_mem_hsec.mpr
    rwa [hsec_eq_Icc_rows hc hv hs]
  have hyP : pt y t ∈ P := by
    apply pt_mem_iff_mem_hsec.mpr
    rwa [hsec_eq_Icc_rows hc hv ht]
  obtain ⟨l, hl⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub t s q₂).mp hlabel.symm
  have hl0 : l ≠ 0 := by
    intro heq
    apply hne
    simp [heq] at hl
    omega
  have hlr : (s : ℝ) - t = (q₂ : ℝ) * l := by exact_mod_cast hl
  apply havoid _ hxP _ hyP k l hl0
  apply vec2_ext
  · simpa [pt] using hxy
  · simpa [pt] using hlr

/-- The paper's planar slice-counting step. The hypotheses are the exact
coordinate forms of source Lemma 2.1, rather than a product-count premise. -/
theorem planar_lattice_count_le_of_period_avoidance
    {P : Set (Fin 2 → ℝ)} (hc : IsCompact P) (hv : Convex ℝ P)
    (hne : P.Nonempty) {q₁ q₂ : ℕ} (hq₂ : 0 < q₂) (horder : q₂ ≤ q₁)
    (hfirst : ∀ x ∈ P, ∀ y ∈ P, x - y ≠ pt (q₁ : ℝ) 0)
    (hsecond : ∀ x ∈ P, ∀ y ∈ P, ∀ u v : ℤ, v ≠ 0 →
      x - y ≠ pt ((q₂ : ℝ) * u) ((q₂ : ℝ) * v)) :
    (DiscreteMinkowski.latticePoints P (standardIntegerLattice 2)).ncard ≤ q₁ * q₂ := by
  classical
  haveI : NeZero q₂ := ⟨by omega⟩
  let J : Finset ℤ := intervalIntegerPoints (yLo P) (yHi P)
  have hrow : ∀ i : J, (hsec P (i.1 : ℝ)).Nonempty := by
    intro i
    apply (hsec_nonempty_iff hc hv hne _).mpr
    exact mem_intervalIntegerPoints.mp i.2
  have hbound := grouped_separated_intervals_card_sum_le
    (fun i : J => (i.1 : ZMod q₂))
    (a := fun i : J => rowLo P i.1) (b := fun i : J => rowHi P i.1)
    hq₂ horder
    (fun i => row_width_lt_of_horizontal_avoidance hc hv (by omega) hfirst (hrow i))
    (by
      intro i j hlabel hij
      exact row_intervals_separated_of_period_avoidance hc hv hsecond
        (hrow i) (hrow j) hlabel (fun he => hij (Subtype.ext he)))
  rw [ZMod.card] at hbound
  rw [ncard_latticePoints_eq_rows hc hv hne]
  have hsum : (∑ i : J, (intervalIntegerPoints (rowLo P i.1) (rowHi P i.1)).card) =
      ∑ i ∈ J, (intervalIntegerPoints (rowLo P i) (rowHi P i)).card := by
    exact Finset.sum_coe_sort J (fun i : ℤ =>
      (intervalIntegerPoints (rowLo P i) (rowHi P i)).card)
  rw [hsum] at hbound
  simpa only [J, intervalIntegerPoints, mul_comm] using hbound

end
end LatticeVolumeInterpolation
