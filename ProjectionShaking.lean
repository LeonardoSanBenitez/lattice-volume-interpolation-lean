import ShakingIterate

/-!
# Coordinate projections under shaking

Supporting the catalog item `davenport_inequality`, Eq. (1.10). A coordinate
projection discarding the shaking direction is unchanged. A projection retaining
that direction is contained in the shaking of the projection: projecting can
join fibres, so equality is not required. Volume preservation in the projected
space then implies that every coordinate-projection volume is nonincreasing.
-/

open Set MeasureTheory
open scoped ENNReal

namespace LatticeVolumeInterpolation

noncomputable section

variable {n m : ℕ}

/-- Coordinate projection onto the coordinates selected by an embedding. -/
def coordinateImage (e : Fin m ↪ Fin n) (K : Set (Fin n → ℝ)) : Set (Fin m → ℝ) :=
  (fun x => x ∘ e) '' K

theorem isCompact_coordinateImage (e : Fin m ↪ Fin n) {K : Set (Fin n → ℝ)}
    (hK : IsCompact K) : IsCompact (coordinateImage e K) :=
  hK.image (continuous_pi fun i => continuous_apply (e i))

theorem convex_coordinateImage (e : Fin m ↪ Fin n) {K : Set (Fin n → ℝ)}
    (hK : Convex ℝ K) : Convex ℝ (coordinateImage e K) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ a b ha hb hab
  exact ⟨a • x + b • y, hK hx hy ha hb hab, rfl⟩

theorem update_comp_embedding (e : Fin m ↪ Fin n) (x : Fin n → ℝ)
    (k : Fin m) (t : ℝ) :
    (Function.update x (e k) t) ∘ e = Function.update (x ∘ e) k t := by
  ext i
  by_cases h : i = k
  · subst h; simp
  · simp [Function.update_of_ne h, Function.update_of_ne (fun he => h (e.injective he))]

/-- If the shaken coordinate is discarded, the projection is unchanged. -/
theorem coordinateImage_coordShaking_of_not_mem (e : Fin m ↪ Fin n)
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (j : Fin n)
    (hj : ∀ i, e i ≠ j) :
    coordinateImage e (coordShaking K j) = coordinateImage e K := by
  have hu : ∀ x : Fin n → ℝ, ∀ t : ℝ, (Function.update x j t) ∘ e = x ∘ e := by
    intro x t; ext i; exact Function.update_of_ne (hj i) t x
  ext y
  constructor
  · rintro ⟨x, ⟨⟨t, ht⟩, _, _⟩, rfl⟩
    exact ⟨Function.update x j t, ht, hu x t⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨Function.update x j 0, update_zero_mem_coordShaking hK j hx, hu x 0⟩

/-- Projected shaking is contained in shaking the projection, when the direction
is retained. The extremal points of the original fibre project into one fibre. -/
theorem coordinateImage_coordShaking_subset (e : Fin m ↪ Fin n)
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (k : Fin m) :
    coordinateImage e (coordShaking K (e k)) ⊆ coordShaking (coordinateImage e K) k := by
  rintro _ ⟨x, hx, rfl⟩
  rw [coordShaking_eq_image hK] at hx
  obtain ⟨⟨a, b, s⟩, ⟨ha, hb, hab, hs, hsl⟩, rfl⟩ := hx
  change (Function.update a (e k) s) ∘ e ∈ coordShaking (coordinateImage e K) k
  rw [update_comp_embedding]
  rw [coordShaking_eq_image (isCompact_coordinateImage e hK)]
  refine ⟨(a ∘ e, b ∘ e, s), ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩, ?_, hs, hsl⟩, rfl⟩
  intro i hi
  exact hab (e i) (fun he => hi (e.injective he))

/-- Each coordinate-projection volume is nonincreasing under one shaking. -/
theorem volume_coordinateImage_coordShaking_le (e : Fin m ↪ Fin n)
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hKc : Convex ℝ K) (j : Fin n) :
    volume (coordinateImage e (coordShaking K j)) ≤ volume (coordinateImage e K) := by
  classical
  by_cases hj : ∃ k, e k = j
  · obtain ⟨k, rfl⟩ := hj
    calc
      _ ≤ volume (coordShaking (coordinateImage e K) k) :=
        measure_mono (coordinateImage_coordShaking_subset e hK k)
      _ = _ := volume_coordShaking (isCompact_coordinateImage e hK)
        (convex_coordinateImage e hKc) k
  · rw [coordinateImage_coordShaking_of_not_mem e hK j (by simpa using hj)]

/-- The projected volume cannot increase after any number of coordinate shakings. -/
theorem volume_coordinateImage_shakeUpTo_le (e : Fin m ↪ Fin n)
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hKc : Convex ℝ K) :
    ∀ k, volume (coordinateImage e (shakeUpTo K k)) ≤ volume (coordinateImage e K)
  | 0 => le_rfl
  | k + 1 => by
    by_cases h : k < n
    · rw [shakeUpTo_succ_of_lt K h]
      exact (volume_coordinateImage_coordShaking_le e (isCompact_shakeUpTo hK k)
        (convex_shakeUpTo hK hKc k) _).trans
        (volume_coordinateImage_shakeUpTo_le e hK hKc k)
    · rw [shakeUpTo_succ_of_le K (not_lt.1 h)]
      exact volume_coordinateImage_shakeUpTo_le e hK hKc k

/-- Reindexing a coordinate projection by `Fin` preserves its intrinsic volume,
including the zero-dimensional case. -/
theorem volume_coordinateImage_eq_projectionOff (I : Finset (Fin n))
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) :
    volume (coordinateImage
      ((Fintype.equivFin {i // i ∉ I}).symm.toEmbedding.trans
        ⟨Subtype.val, Subtype.val_injective⟩) K) = volume (projectionOff I K) := by
  let e := Fintype.equivFin {i // i ∉ I}
  let T := MeasurableEquiv.piCongrLeft (fun _ : {i // i ∉ I} => ℝ) e.symm
  have hT : MeasurePreserving T volume volume :=
    volume_measurePreserving_piCongrLeft _ e.symm
  have hproj : IsCompact (projectionOff I K) :=
    hK.image (continuous_pi fun i => continuous_apply i.1)
  have hpre : T ⁻¹' projectionOff I K = coordinateImage
      (e.symm.toEmbedding.trans ⟨Subtype.val, Subtype.val_injective⟩) K := by
    ext y
    constructor
    · rintro ⟨x, hx, hxy⟩
      refine ⟨x, hx, ?_⟩
      ext k
      have h := congrFun hxy (e.symm k)
      simpa [T, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft] using h
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x, hx, ?_⟩
      ext i
      simp [T, coordSplit, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
        MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd]
  rw [← hpre]
  exact hT.measure_preimage hproj.isClosed.measurableSet.nullMeasurableSet

/-- The paper's intrinsic coordinate-projection volumes decrease under shaking. -/
theorem volume_projectionOff_shakeUpTo_le (I : Finset (Fin n))
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hKc : Convex ℝ K) (k : ℕ) :
    volume (projectionOff I (shakeUpTo K k)) ≤ volume (projectionOff I K) := by
  rw [← volume_coordinateImage_eq_projectionOff I (isCompact_shakeUpTo hK k),
    ← volume_coordinateImage_eq_projectionOff I hK]
  exact volume_coordinateImage_shakeUpTo_le _ hK hKc k

end

end LatticeVolumeInterpolation
