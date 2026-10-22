import LatticeEmptyTranslate

/-!
# Finite coset translation

Catalog item `bhw_lattice_conjecture_dimension_three_symmetric`.
These are the exact periodic-set and hull-deletion steps in Malikiosis's
Lemma 2.4. All scalar periods here are positive integers in a real vector
space; their lattice preservation is checked through integer scalar action.
-/

open Set
open scoped Pointwise

namespace LatticeVolumeInterpolation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The periodic union `S + r Λ` from the source's finite-set induction. -/
def latticeCosetUnion (S : Finset E) (Λ : Submodule ℤ E) (r : ℕ) : Set E :=
  {x | ∃ s ∈ S, ∃ z ∈ Λ, x = s + (r : ℝ) • z}

theorem latticeCosetUnion_subset_lattice {S : Finset E} {Λ : Submodule ℤ E} {r : ℕ}
    (hS : ∀ s ∈ S, s ∈ Λ) : latticeCosetUnion S Λ r ⊆ (Λ : Set E) := by
  rintro x ⟨s, hs, z, hz, rfl⟩
  apply Λ.add_mem (hS s hs)
  have h := Λ.smul_mem (r : ℤ) hz
  simpa only [Nat.cast_smul_eq_nsmul] using h

/-- The source's minimizing vertex is available for a finite union of
lattice cosets, because that whole periodic union lies in the lattice. -/
theorem exists_coset_union_hull_vertex
    [FiniteDimensional ℝ E] {K : Set E} {Λ : Submodule ℤ E} [DiscreteTopology Λ]
    {S : Finset E} {r : ℕ} (hS : ∀ s ∈ S, s ∈ Λ) (hSne : S.Nonempty)
    (hK : Convex ℝ K) (hb : Bornology.IsBounded K) (hne : K.Nonempty)
    (hfree : Disjoint K (latticeCosetUnion S Λ r)) :
    ∃ v ∈ latticeCosetUnion S Λ r,
      convexHull ℝ (insert v K) ∩ latticeCosetUnion S Λ r = {v} := by
  have hP : (latticeCosetUnion S Λ r).Nonempty := by
    obtain ⟨s, hs⟩ := hSne
    exact ⟨s, s, hs, 0, Λ.zero_mem, by simp⟩
  apply exists_vertex_with_singleton_hull_intersection hK hne hP hfree
  intro v hv
  apply (DiscreteMinkowski.finite_inter_lattice
    (isBounded_convexHull.mpr (hb.insert v)) Λ).subset
  exact inter_subset_inter_right _ (latticeCosetUnion_subset_lattice hS)

/-- Deleting the minimizing vertex's original coset leaves the enlarged
convex hull disjoint from all the remaining periodic cosets. -/
theorem hull_disjoint_remaining_cosets
    [DecidableEq E] {K : Set E} {Λ : Submodule ℤ E} {S : Finset E} {r : ℕ}
    {v s₀ w : E} (hs₀ : s₀ ∈ S) (hw : w ∈ Λ) (hv : v = s₀ + (r : ℝ) • w)
    (hset : convexHull ℝ (insert v K) ∩ latticeCosetUnion S Λ r = {v})
    (hsep : ∀ s ∈ S, ∀ t ∈ S, ∀ z ∈ Λ, s - t = (r : ℝ) • z → s = t) :
    Disjoint (convexHull ℝ (insert v K)) (latticeCosetUnion (S.erase s₀) Λ r) := by
  classical
  apply Set.disjoint_left.mpr
  rintro x hx ⟨s, hs, z, hz, hxeq⟩
  have hsS : s ∈ S := Finset.mem_of_mem_erase hs
  have hxP : x ∈ latticeCosetUnion S Λ r := ⟨s, hsS, z, hz, hxeq⟩
  have hxv : x = v := by
    have hmem : x ∈ convexHull ℝ (insert v K) ∩ latticeCosetUnion S Λ r := ⟨hx, hxP⟩
    rw [hset] at hmem
    exact mem_singleton_iff.mp hmem
  have he : s + (r : ℝ) • z = s₀ + (r : ℝ) • w := hxeq.symm.trans (hxv.trans hv)
  have hdiff : s - s₀ = (r : ℝ) • (w - z) := by
    calc
      _ = (s + (r : ℝ) • z) - (s₀ + (r : ℝ) • z) := by abel
      _ = (s₀ + (r : ℝ) • w) - (s₀ + (r : ℝ) • z) := by rw [he]
      _ = _ := by rw [smul_sub]; abel
  have hss := hsep s hsS s₀ hs₀ (w - z) (Λ.sub_mem hw hz) hdiff
  exact (Finset.mem_erase.mp hs).1 hss

/-- The added vertex still avoids the body modulo the larger period.
The intermediate point at the old period lies in its singleton hull. -/
theorem coset_union_vertex_avoids_larger_scale
    {K : Set E} {Λ : Submodule ℤ E} {S : Finset E}
    {r t : ℕ} (hr : 0 < r) (hrt : r < t) {v : E}
    (hvP : v ∈ latticeCosetUnion S Λ r)
    (hset : convexHull ℝ (insert v K) ∩ latticeCosetUnion S Λ r = {v})
    (hfree : Disjoint K (latticeCosetUnion S Λ r)) :
    ∀ z ∈ Λ, v + (t : ℝ) • z ∉ K := by
  intro z hz hx
  have hrr : (0 : ℝ) < r := by exact_mod_cast hr
  have htr : (r : ℝ) < t := by exact_mod_cast hrt
  have htpos : (0 : ℝ) < t := lt_trans hrr htr
  have hrat : 0 ≤ (r : ℝ) / t := (div_pos hrr htpos).le
  have hrat1 : (r : ℝ) / t ≤ 1 := (div_le_one htpos).mpr htr.le
  have hvHull : v ∈ convexHull ℝ (insert v K) := subset_convexHull ℝ _ (mem_insert _ _)
  have hxHull : v + (t : ℝ) • z ∈ convexHull ℝ (insert v K) :=
    subset_convexHull ℝ _ (mem_insert_of_mem _ hx)
  have hwHull : v + (r : ℝ) • z ∈ convexHull ℝ (insert v K) := by
    have hc := (convex_convexHull ℝ (insert v K)) hvHull hxHull
      (sub_nonneg.mpr hrat1) hrat
      (by ring : (1 - (r : ℝ) / t) + (r : ℝ) / t = 1)
    convert hc using 1
    symm
    calc
      _ = ((1 - (r : ℝ) / t) + (r : ℝ) / t) • v + (((r : ℝ) / t) * t) • z := by
        simp only [smul_add, smul_smul, add_smul]; abel
      _ = v + (r : ℝ) • z := by simp [htpos.ne']
  have hwP : v + (r : ℝ) • z ∈ latticeCosetUnion S Λ r := by
    obtain ⟨s, hs, w, hw, hvw⟩ := hvP
    refine ⟨s, hs, w + z, Λ.add_mem hw hz, ?_⟩
    rw [hvw, smul_add]
    abel
  have heq : v + (r : ℝ) • z = v := by
    have hmem : v + (r : ℝ) • z ∈ convexHull ℝ (insert v K) ∩ latticeCosetUnion S Λ r :=
      ⟨hwHull, hwP⟩
    rw [hset] at hmem
    exact mem_singleton_iff.mp hmem
  have hsmul : (r : ℝ) • z = 0 := by simpa using heq
  have hz0 : z = 0 := (smul_eq_zero.mp hsmul).resolve_left hrr.ne'
  exact (Set.disjoint_left.mp hfree) (by simpa [hz0] using hx) hvP

/-- Malikiosis Lemma 2.4. Each representative may be moved within its old
coset so that the resulting finite set avoids the body modulo the larger
period and occupies distinct cosets of that larger-period lattice. -/
theorem exists_finite_coset_translate
    [FiniteDimensional ℝ E] {Λ : Submodule ℤ E} [DiscreteTopology Λ]
    {r t : ℕ} (hr : 0 < r) (hrt : r < t) (S : Finset E) :
    ∀ {K : Set E}, Convex ℝ K → Bornology.IsBounded K → K.Nonempty →
      (∀ s ∈ S, s ∈ Λ) → Disjoint K (latticeCosetUnion S Λ r) →
      (∀ s ∈ S, ∀ u ∈ S, ∀ z ∈ Λ, s - u = (r : ℝ) • z → s = u) →
      ∃ T : Finset E, T.card = S.card ∧ (∀ y ∈ T, y ∈ Λ) ∧
        (∀ s ∈ S, ∃ y ∈ T, ∃ z ∈ Λ, y = s + (r : ℝ) • z) ∧
        (∀ y ∈ T, ∃ s ∈ S, ∃ z ∈ Λ, y = s + (r : ℝ) • z) ∧
        (∀ y ∈ T, ∀ z ∈ Λ, y + (t : ℝ) • z ∉ K) ∧
        (∀ x ∈ T, ∀ y ∈ T, ∀ z ∈ Λ, x - y = (t : ℝ) • z → x = y) := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    intro K hK hb hne hS hfree hsep
    by_cases hSne : S.Nonempty
    · obtain ⟨v, hvP, hset⟩ := exists_coset_union_hull_vertex hS hSne hK hb hne hfree
      obtain ⟨s₀, hs₀, w, hw, hv⟩ := hvP
      have hvP' : v ∈ latticeCosetUnion S Λ r := ⟨s₀, hs₀, w, hw, hv⟩
      let S₀ := S.erase s₀
      have hlt : S₀ ⊂ S := Finset.erase_ssubset hs₀
      have hS₀ : ∀ s ∈ S₀, s ∈ Λ := fun s hs => hS s (Finset.mem_of_mem_erase hs)
      have hfree₀ : Disjoint (convexHull ℝ (insert v K)) (latticeCosetUnion S₀ Λ r) :=
        hull_disjoint_remaining_cosets hs₀ hw hv hset hsep
      have hsep₀ : ∀ s ∈ S₀, ∀ u ∈ S₀, ∀ z ∈ Λ, s - u = (r : ℝ) • z → s = u :=
        fun s hs u hu z hz he => hsep s (Finset.mem_of_mem_erase hs)
          u (Finset.mem_of_mem_erase hu) z hz he
      have hvHull : v ∈ convexHull ℝ (insert v K) :=
        subset_convexHull ℝ _ (mem_insert _ _)
      obtain ⟨T, hcard, hTL, hfwd, hrev, havoid, hTsep⟩ :=
        ih S₀ hlt (convex_convexHull ℝ _) (isBounded_convexHull.mpr (hb.insert v))
          ⟨v, hvHull⟩ hS₀ hfree₀ hsep₀
      have hvΛ : v ∈ Λ := latticeCosetUnion_subset_lattice hS hvP'
      have hvT : v ∉ T := by
        intro he
        apply havoid v he 0 Λ.zero_mem
        simpa using hvHull
      refine ⟨insert v T, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hvT, hcard]
        dsimp [S₀]
        rw [Finset.card_erase_of_mem hs₀]
        have hpos : 0 < S.card := Finset.card_pos.mpr hSne
        omega
      · intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hvΛ
        · exact hTL y hy
      · intro s hs
        by_cases he : s = s₀
        · exact ⟨v, Finset.mem_insert_self _ _, w, hw, by simpa [he] using hv⟩
        · obtain ⟨y, hy, z, hz, hzy⟩ := hfwd s (Finset.mem_erase.mpr ⟨he, hs⟩)
          exact ⟨y, Finset.mem_insert_of_mem hy, z, hz, hzy⟩
      · intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact ⟨s₀, hs₀, w, hw, hv⟩
        · obtain ⟨s, hs, z, hz, he⟩ := hrev y hy
          exact ⟨s, Finset.mem_of_mem_erase hs, z, hz, he⟩
      · intro y hy z hz hx
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact coset_union_vertex_avoids_larger_scale hr hrt hvP' hset hfree z hz hx
        · exact havoid y hy z hz (subset_convexHull ℝ _ (mem_insert_of_mem _ hx))
      · intro x hx y hy z hz he
        rcases Finset.mem_insert.mp hx with hxe | hxT
        · subst x
          rcases Finset.mem_insert.mp hy with hye | hyT
          · exact hye.symm
          · exfalso
            apply havoid y hyT z hz
            have he' : y + (t : ℝ) • z = v := by rw [← he]; abel
            rw [he']
            exact hvHull
        · rcases Finset.mem_insert.mp hy with hye | hyT
          · subst y
            exfalso
            apply havoid x hxT (-z) (Λ.neg_mem hz)
            have he' : x + (t : ℝ) • (-z) = v := by rw [smul_neg, ← he]; abel
            rw [he']
            exact hvHull
          · exact hTsep x hxT y hyT z hz he
    · have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hSne
      subst S
      exact ⟨∅, by simp⟩

end LatticeVolumeInterpolation
