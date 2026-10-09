import BoundarySections
import Pick

/-!
# Row counting for a planar lattice polygon's boundary

The row route toward catalog item `henk_schurmann_wills_boundary_bound`.
At an interior integer height, any lattice point of `bd P` must lie at one
of the two section endpoints. The elementary interval-count bound below
expresses that fact independently of whether either endpoint is integral.
-/

open Set MeasureTheory

namespace LatticeVolumeInterpolation

noncomputable section

/-- A closed real interval contains at most two more integers than its open
interior. The two possible extras are its endpoints. -/
theorem card_closed_integer_row_le_open_add_two (l r : ℝ) :
    (Finset.Icc ⌈l⌉ ⌊r⌋).card ≤ (Finset.Ioo ⌊l⌋ ⌈r⌉).card + 2 := by
  classical
  have hsubset : Finset.Icc ⌈l⌉ ⌊r⌋ ⊆
      insert ⌈l⌉ (insert ⌊r⌋ (Finset.Ioo ⌊l⌋ ⌈r⌉)) := by
    intro k hk
    obtain ⟨hkl, hkr⟩ := Finset.mem_Icc.1 hk
    simp only [Finset.mem_insert, Finset.mem_Ioo]
    by_cases hleft : k = ⌈l⌉
    · exact Or.inl hleft
    right
    by_cases hright : k = ⌊r⌋
    · exact Or.inl hright
    right
    have hfl := Int.floor_le_ceil l
    have hfr := Int.floor_le_ceil r
    omega
  calc
    (Finset.Icc ⌈l⌉ ⌊r⌋).card ≤
        (insert ⌈l⌉ (insert ⌊r⌋ (Finset.Ioo ⌊l⌋ ⌈r⌉))).card :=
      Finset.card_le_card hsubset
    _ ≤ (Finset.Ioo ⌊l⌋ ⌈r⌉).card + 2 := by
      have h1 := Finset.card_insert_le ⌈l⌉
        (insert ⌊r⌋ (Finset.Ioo ⌊l⌋ ⌈r⌉))
      have h2 := Finset.card_insert_le ⌊r⌋ (Finset.Ioo ⌊l⌋ ⌈r⌉)
      omega

/-- The endpoint row of a lattice polygon has integer endpoints, so its
integer-point count is exactly its length plus one. -/
theorem card_closed_integer_row_of_integral_ends {l r : ℝ}
    (hl : IsInt l) (hr : IsInt r) (hle : l ≤ r) :
    ((Finset.Icc ⌈l⌉ ⌊r⌋).card : ℝ) = r - l + 1 := by
  obtain ⟨L, rfl⟩ := hl
  obtain ⟨R, rfl⟩ := hr
  have hLR : L ≤ R := by exact_mod_cast hle
  rw [Int.ceil_intCast, Int.floor_intCast]
  have hcard := Int.card_Icc_of_le L R (by omega)
  have hcardR : ((Finset.Icc L R).card : ℝ) = (R : ℝ) + 1 - L := by
    exact_mod_cast hcard
  linarith

/-- Boundary lattice points and interior lattice points partition the lattice
points of a compact set. -/
theorem boundary_count_add_interior_eq_all {P : Set (Fin 2 → ℝ)}
    (hc : IsCompact P) : G2 (frontier P) + G2 (interior P) = G2 P := by
  have hfin : (DiscreteMinkowski.latticePoints P (standardIntegerLattice 2)).Finite :=
    DiscreteMinkowski.finite_inter_lattice hc.isBounded _
  have hsub : DiscreteMinkowski.latticePoints (interior P) (standardIntegerLattice 2) ⊆
      DiscreteMinkowski.latticePoints P (standardIntegerLattice 2) :=
    fun z hz => ⟨interior_subset hz.1, hz.2⟩
  have hbd : DiscreteMinkowski.latticePoints (frontier P) (standardIntegerLattice 2) =
      DiscreteMinkowski.latticePoints P (standardIntegerLattice 2) \
        DiscreteMinkowski.latticePoints (interior P) (standardIntegerLattice 2) := by
    rw [hc.isClosed.frontier_eq]
    ext z
    simp only [DiscreteMinkowski.latticePoints_apply, mem_inter_iff, mem_sdiff, SetLike.mem_coe]
    tauto
  have hcard := Set.ncard_sdiff_add_ncard_of_subset hsub hfin
  rw [← hbd] at hcard
  exact hcard

/-- The boundary count is controlled by the two extreme rows and at most
two points on each intermediate integer row. -/
theorem boundary_count_le_extreme_rows {P : Set (Fin 2 → ℝ)}
    (hP : IsLatticePolygon P) (hint : (interior P).Nonempty)
    {A B : ℤ} (hA : yLo P = A) (hB : yHi P = B) :
    (G2 (frontier P) : ℝ) ≤
      ((Finset.Icc ⌈rowLo P A⌉ ⌊rowHi P A⌋).card : ℝ) +
      ((Finset.Icc ⌈rowLo P B⌉ ⌊rowHi P B⌋).card : ℝ) +
      2 * (Finset.Ioo A B).card := by
  have hc := hP.isCompact
  have hv := hP.convex
  have hne : P.Nonempty := hint.mono interior_subset
  have hAB : A < B := by
    obtain ⟨c, hcI⟩ := hint
    have h := ((mem_interior_iff_rows hc hv hne c).1 hcI).1
    rw [hA, hB] at h
    exact_mod_cast h.1.trans h.2
  have hpart := boundary_count_add_interior_eq_all hc
  have hProws := ncard_latticePoints_eq_rows hc hv hne
  have hIrows := ncard_latticePoints_interior_eq_rows hc hv hne
  rw [hA, hB, Int.ceil_intCast, Int.floor_intCast] at hProws
  rw [hA, hB, Int.floor_intCast, Int.ceil_intCast] at hIrows
  have hsum := sum_Icc_eq_ends_add_Ioo
    (fun k : ℤ => ((Finset.Icc ⌈rowLo P k⌉ ⌊rowHi P k⌋).card : ℝ)) hAB
  have hrow : ∑ k ∈ Finset.Ioo A B,
      ((Finset.Icc ⌈rowLo P k⌉ ⌊rowHi P k⌋).card : ℝ) ≤
      ∑ k ∈ Finset.Ioo A B,
        (((Finset.Ioo ⌊rowLo P k⌋ ⌈rowHi P k⌉).card : ℝ) + 2) := by
    apply Finset.sum_le_sum
    intro k _
    exact_mod_cast card_closed_integer_row_le_open_add_two (rowLo P k) (rowHi P k)
  have htwo : (∑ _k ∈ Finset.Ioo A B, (2 : ℝ)) =
      2 * (Finset.Ioo A B).card := by simp [mul_comm]
  rw [Finset.sum_add_distrib, htwo] at hrow
  have hpartR : (G2 (frontier P) : ℝ) + G2 (interior P) = G2 P := by
    exact_mod_cast hpart
  have hProwsR : (G2 P : ℝ) =
      ∑ k ∈ Finset.Icc A B, ((Finset.Icc ⌈rowLo P k⌉ ⌊rowHi P k⌋).card : ℝ) := by
    exact_mod_cast hProws
  have hIrowsR : (G2 (interior P) : ℝ) =
      ∑ k ∈ Finset.Ioo A B, ((Finset.Ioo ⌊rowLo P k⌋ ⌈rowHi P k⌉).card : ℝ) := by
    exact_mod_cast hIrows
  rw [hProwsR, hIrowsR, hsum] at hpartR
  linarith

/-- For a lattice polygon, the boundary count is at most the sum of the
lengths of its two extreme horizontal sections plus twice its height. -/
theorem boundary_count_le_extreme_widths_plus_height {P : Set (Fin 2 → ℝ)}
    (hP : IsLatticePolygon P) (hint : (interior P).Nonempty)
    {A B : ℤ} (hA : yLo P = A) (hB : yHi P = B) :
    (G2 (frontier P) : ℝ) ≤
      (rowHi P A - rowLo P A) + (rowHi P B - rowLo P B) +
        2 * ((B : ℝ) - A) := by
  have hc := hP.isCompact
  have hv := hP.convex
  have hne : P.Nonempty := hint.mono interior_subset
  have hAB : A < B := by
    obtain ⟨c, hcI⟩ := hint
    have h := ((mem_interior_iff_rows hc hv hne c).1 hcI).1
    rw [hA, hB] at h
    exact_mod_cast h.1.trans h.2
  have hrowA : rowLo P A ≤ rowHi P A :=
    rowLo_le_rowHi hc ((hsec_nonempty_iff hc hv hne A).2 (by rw [hA, hB]; exact ⟨le_rfl, by
      exact_mod_cast hAB.le⟩))
  have hrowB : rowLo P B ≤ rowHi P B :=
    rowLo_le_rowHi hc ((hsec_nonempty_iff hc hv hne B).2 (by rw [hA, hB]; exact ⟨by
      exact_mod_cast hAB.le, le_rfl⟩))
  have hAcount := card_closed_integer_row_of_integral_ends
    (by rw [← hA]; exact hP.isInt_rowLo_yLo hne)
    (by rw [← hA]; exact hP.isInt_rowHi_yLo hne) hrowA
  have hBcount := card_closed_integer_row_of_integral_ends
    (by rw [← hB]; exact hP.isInt_rowLo_yHi hne)
    (by rw [← hB]; exact hP.isInt_rowHi_yHi hne) hrowB
  have hcardZ := Int.card_Ioo_of_lt A B hAB
  have hcardR : ((Finset.Ioo A B).card : ℝ) = (B : ℝ) - A - 1 := by
    exact_mod_cast hcardZ
  have hbound := boundary_count_le_extreme_rows hP hint hA hB
  rw [hAcount, hBcount, hcardR] at hbound
  linarith

/-- For a centrally symmetric lattice polygon, the two extreme row lengths
coincide, giving the exact horizontal-row bound used toward Eq. (5.2). -/
theorem boundary_count_le_symmetric_extreme_width_and_height
    {P : Set (Fin 2 → ℝ)} (hP : IsLatticePolygon P)
    (hint : (interior P).Nonempty)
    (hsym : DiscreteMinkowski.IsOriginSymmetric P) :
    (G2 (frontier P) : ℝ) ≤
      2 * (rowHi P (yLo P) - rowLo P (yLo P)) +
        2 * (yHi P - yLo P) := by
  have hne : P.Nonempty := hint.mono interior_subset
  obtain ⟨A, hA⟩ := hP.isInt_yLo hne
  obtain ⟨B, hB⟩ := hP.isInt_yHi hne
  have hbound := boundary_count_le_extreme_widths_plus_height hP hint hA hB
  have hwidth := symmetric_extreme_section_width_eq hsym
  rw [hA, hB] at hwidth ⊢
  linarith

end

end LatticeVolumeInterpolation
