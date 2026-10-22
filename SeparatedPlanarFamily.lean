import SeparatedRows

/-!
# Residue-slice counting for planar families

Catalog item `bhw_lattice_conjecture_dimension_three_symmetric`.
This is the source's common slice-counting step. It applies both to the
rank-at-most-one period case and to the repaired family consisting of one
convex body and finitely many singleton lattice points.
-/

open Set
open scoped BigOperators

namespace LatticeVolumeInterpolation

theorem integerPt_mem_standardIntegerLattice (u v : ℤ) :
    pt (u : ℝ) (v : ℝ) ∈ standardIntegerLattice 2 := by
  apply (mem_standardIntegerLattice_iff 2 _).mpr
  refine ⟨![u, v], ?_⟩
  intro i; fin_cases i <;> simp [pt]

/-- The source's grouped row count, with all period conditions stated in
lattice-vector form. Lower-dimensional and empty integer-height slices
require no separate full-dimensionality assumption. -/
theorem planar_family_count_le_of_period_avoidance
    {ι : Type*} [Fintype ι] (K : ι → Set (Fin 2 → ℝ))
    (hc : ∀ i, IsCompact (K i)) (hv : ∀ i, Convex ℝ (K i))
    (hne : ∀ i, (K i).Nonempty) {q r : ℕ} (hr : 0 < r) (hrq : r ≤ q)
    (hfirst : ∀ i, ∀ x ∈ K i, ∀ y ∈ K i, ∀ z ∈ standardIntegerLattice 2,
      z ≠ 0 → x - y ≠ (q : ℝ) • z)
    (hwithin : ∀ i, ∀ x ∈ K i, ∀ y ∈ K i, ∀ z ∈ standardIntegerLattice 2,
      z 1 ≠ 0 → x - y ≠ (r : ℝ) • z)
    (hcross : ∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j,
      ∀ z ∈ standardIntegerLattice 2, x - y ≠ (r : ℝ) • z) :
    (∑ i, (DiscreteMinkowski.latticePoints (K i) (standardIntegerLattice 2)).ncard) ≤ q * r := by
  classical
  haveI : NeZero r := ⟨by omega⟩
  let J : ι → Finset ℤ := fun i => intervalIntegerPoints (yLo (K i)) (yHi (K i))
  have hrow : ∀ p : Σ i, J i, (hsec (K p.1) (p.2.1 : ℝ)).Nonempty := by
    intro p
    apply (hsec_nonempty_iff (hc _) (hv _) (hne _) _).mpr
    exact mem_intervalIntegerPoints.mp p.2.2
  have hwidth : ∀ p : Σ i, J i, rowHi (K p.1) p.2.1 - rowLo (K p.1) p.2.1 < q := by
    intro p
    apply row_width_lt_of_horizontal_avoidance (hc _) (hv _) (by omega) ?_ (hrow p)
    intro x hx y hy he
    have hunit : pt 1 0 ≠ (0 : Fin 2 → ℝ) := by
      intro hh
      have := congrFun hh 0
      norm_num [pt] at this
    apply hfirst p.1 x hx y hy (pt 1 0)
      (by simpa using integerPt_mem_standardIntegerLattice 1 0) hunit
    convert he using 1
    ext l; fin_cases l <;> simp [pt]
  have hperiod : ∀ i, ∀ x ∈ K i, ∀ y ∈ K i, ∀ u v : ℤ, v ≠ 0 →
      x - y ≠ pt ((r : ℝ) * u) ((r : ℝ) * v) := by
    intro i x hx y hy u v hv0 he
    apply hwithin i x hx y hy (pt (u : ℝ) (v : ℝ))
      (integerPt_mem_standardIntegerLattice u v) (by simpa [pt] using hv0)
    convert he using 1
    ext l; fin_cases l <;> simp [pt]
  have hbound := grouped_separated_intervals_card_sum_le
    (fun p : Σ i, J i => (p.2.1 : ZMod r))
    (a := fun p : Σ i, J i => rowLo (K p.1) p.2.1)
    (b := fun p : Σ i, J i => rowHi (K p.1) p.2.1) hr hrq hwidth
    (by
      rintro ⟨i, s⟩ ⟨j, t⟩ hlabel hneq x hx y hy k hxy
      by_cases hij : i = j
      · subst j
        have hst : s.1 ≠ t.1 := by
          intro he
          have het : s = t := Subtype.ext he
          subst t
          exact hneq rfl
        exact row_intervals_separated_of_period_avoidance (hc i) (hv i) (hperiod i)
          (hrow ⟨i, s⟩) (hrow ⟨i, t⟩) hlabel hst x hx y hy k hxy
      · have hxP : pt x (s.1 : ℝ) ∈ K i := by
          apply pt_mem_iff_mem_hsec.mpr
          rwa [hsec_eq_Icc_rows (hc i) (hv i) (hrow ⟨i, s⟩)]
        have hyP : pt y (t.1 : ℝ) ∈ K j := by
          apply pt_mem_iff_mem_hsec.mpr
          rwa [hsec_eq_Icc_rows (hc j) (hv j) (hrow ⟨j, t⟩)]
        obtain ⟨l, hl⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub t.1 s.1 r).mp hlabel.symm
        have hldiff : (s.1 : ℝ) - t.1 = (r : ℝ) * l := by exact_mod_cast hl
        apply hcross i j hij _ hxP _ hyP (pt (k : ℝ) (l : ℝ))
          (integerPt_mem_standardIntegerLattice k l)
        apply vec2_ext
        · simpa [pt] using hxy
        · simpa [pt] using hldiff)
  have hcount : ∀ i, (∑ s : J i,
      (intervalIntegerPoints (rowLo (K i) s.1) (rowHi (K i) s.1)).card) =
      (DiscreteMinkowski.latticePoints (K i) (standardIntegerLattice 2)).ncard := by
    intro i
    rw [ncard_latticePoints_eq_rows (hc i) (hv i) (hne i)]
    exact Finset.sum_coe_sort (J i) (fun t : ℤ =>
      (intervalIntegerPoints (rowLo (K i) t) (rowHi (K i) t)).card)
  rw [Fintype.sum_sigma] at hbound
  simp_rw [hcount] at hbound
  simpa only [ZMod.card, mul_comm] using hbound

end LatticeVolumeInterpolation
