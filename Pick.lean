import PlanarRows

/-!
# Pick's theorem for convex lattice polygons

Catalog item `pick_theorem_interior` (Sec. 5, Eq. (5.1)): for a lattice polygon `P`,

  `G(int P) = vol(P) - G(bd P)/2 + 1`.

The paper quotes it from Beck and Robins, Theorem 2.8, which states `A = I + B/2 - 1` for an
integral convex polygon. We prove it for every convex lattice polygon, the convex hull of finitely
many points of `ℤ^2` with non-empty interior, by horizontal rows: if the row at height `j` is
`[l(j), r(j)]`, exact row counts give

  `G(P) + G(int P) = Σ_j (⌊r(j)⌋ + ⌈r(j)⌉) - Σ_j (⌊l(j)⌋ + ⌈l(j)⌉) + (end rows)`.

Between consecutive rows at which `r` takes an integer value, `r` is affine (the maximum over the
vertices of `x - chord(y)` would otherwise sit at such a row), and the reflection `j ↦ a + b - j`
shows `Σ (⌊r⌋ + ⌈r⌉ - 2r) = 0` there; `r` is also affine on every unit interval, so
`∫ r = Σ_j r(j) - (r(y_min) + r(y_max))/2`. With the same for `l`, `G + G(int) = 2 vol + 2`, which
is Pick's formula.
-/

open Set MeasureTheory

namespace LatticeVolumeInterpolation

noncomputable section

/-- **A lattice polygon**: the convex hull of finitely many points of `ℤ^2`. -/
def IsLatticePolygon (P : Set (Fin 2 → ℝ)) : Prop :=
  ∃ S : Finset (Fin 2 → ℝ), (∀ s ∈ S, s ∈ standardIntegerLattice 2) ∧
    P = convexHull ℝ (S : Set (Fin 2 → ℝ))

variable {P : Set (Fin 2 → ℝ)}

theorem IsLatticePolygon.isCompact (hP : IsLatticePolygon P) : IsCompact P := by
  obtain ⟨S, -, rfl⟩ := hP
  exact S.finite_toSet.isCompact_convexHull (𝕜 := ℝ)

theorem IsLatticePolygon.convex (hP : IsLatticePolygon P) : Convex ℝ P := by
  obtain ⟨S, -, rfl⟩ := hP
  exact convex_convexHull ℝ _

/-- The linear functional `p ↦ α p_1 + β p_2`. -/
def lin2 (α β : ℝ) : (Fin 2 → ℝ) →ₗ[ℝ] ℝ where
  toFun p := α * p 0 + β * p 1
  map_add' x y := by simp only [Pi.add_apply]; ring
  map_smul' r x := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

@[simp] theorem lin2_apply (α β : ℝ) (p : Fin 2 → ℝ) : lin2 α β p = α * p 0 + β * p 1 := rfl

/-- **Half-plane principle**: every point of `conv S` satisfies every linear inequality that all
of `S` satisfies. -/
theorem le_of_mem_convexHull {S : Finset (Fin 2 → ℝ)} (f : (Fin 2 → ℝ) →ₗ[ℝ] ℝ) {M : ℝ}
    (hS : ∀ s ∈ S, f s ≤ M) {p : Fin 2 → ℝ} (hp : p ∈ convexHull ℝ (S : Set (Fin 2 → ℝ))) :
    f p ≤ M :=
  convexHull_min (fun s hs => hS s hs) (convex_halfSpace_le f.isLinear M) hp

theorem int_coords {s : Fin 2 → ℝ} (h : s ∈ standardIntegerLattice 2) :
    ∃ a b : ℤ, s 0 = a ∧ s 1 = b := by
  obtain ⟨w, hw⟩ := (mem_standardIntegerLattice_iff 2 s).1 h
  exact ⟨w 0, w 1, hw 0, hw 1⟩

/-- `x ∈ ℝ` is an integer. -/
def IsInt (x : ℝ) : Prop := ∃ n : ℤ, x = n

theorem isInt_intCast (n : ℤ) : IsInt n := ⟨n, rfl⟩

theorem IsInt.add {x y : ℝ} (hx : IsInt x) (hy : IsInt y) : IsInt (x + y) := by
  obtain ⟨m, rfl⟩ := hx; obtain ⟨n, rfl⟩ := hy; exact ⟨m + n, by push_cast; ring⟩

theorem IsInt.neg {x : ℝ} (hx : IsInt x) : IsInt (-x) := by
  obtain ⟨m, rfl⟩ := hx; exact ⟨-m, by push_cast; ring⟩

/-- Two integers that differ are at least `1` apart. -/
theorem IsInt.add_one_le_of_lt {x y : ℝ} (hx : IsInt x) (hy : IsInt y) (h : x < y) :
    x + 1 ≤ y := by
  obtain ⟨m, rfl⟩ := hx; obtain ⟨n, rfl⟩ := hy
  have : m < n := by exact_mod_cast h
  have : m + 1 ≤ n := this
  exact_mod_cast this

/-! ### Reflections -/

/-- The reflection `(x_1, x_2) ↦ (-x_1, x_2)`. -/
def reflX : (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ) where
  toFun x := ![-x 0, x 1]
  invFun x := ![-x 0, x 1]
  map_add' x y := by refine vec2_ext ?_ ?_ <;> simp; ring
  map_smul' r x := by refine vec2_ext ?_ ?_ <;> simp
  left_inv x := by refine vec2_ext ?_ ?_ <;> simp
  right_inv x := by refine vec2_ext ?_ ?_ <;> simp

/-- The reflection `(x_1, x_2) ↦ (x_1, -x_2)`. -/
def reflY : (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ) where
  toFun x := ![x 0, -x 1]
  invFun x := ![x 0, -x 1]
  map_add' x y := by refine vec2_ext ?_ ?_ <;> simp; ring
  map_smul' r x := by refine vec2_ext ?_ ?_ <;> simp
  left_inv x := by refine vec2_ext ?_ ?_ <;> simp
  right_inv x := by refine vec2_ext ?_ ?_ <;> simp

theorem reflX_apply (x : Fin 2 → ℝ) : reflX x = ![-x 0, x 1] := rfl

theorem reflY_apply (x : Fin 2 → ℝ) : reflY x = ![x 0, -x 1] := rfl

theorem reflX_mem_lattice {x : Fin 2 → ℝ} (h : x ∈ standardIntegerLattice 2) :
    reflX x ∈ standardIntegerLattice 2 := by
  obtain ⟨a, b, ha, hb⟩ := int_coords h
  refine (mem_standardIntegerLattice_iff 2 _).2 ⟨![-a, b], fun i => ?_⟩
  fin_cases i <;> simp [reflX_apply, ha, hb]

theorem reflY_mem_lattice {x : Fin 2 → ℝ} (h : x ∈ standardIntegerLattice 2) :
    reflY x ∈ standardIntegerLattice 2 := by
  obtain ⟨a, b, ha, hb⟩ := int_coords h
  refine (mem_standardIntegerLattice_iff 2 _).2 ⟨![a, -b], fun i => ?_⟩
  fin_cases i <;> simp [reflY_apply, ha, hb]

theorem IsLatticePolygon.image_reflX (hP : IsLatticePolygon P) :
    IsLatticePolygon (reflX '' P) := by
  classical
  obtain ⟨S, hS, rfl⟩ := hP
  refine ⟨S.image reflX, fun s hs => ?_, ?_⟩
  · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hs
    exact reflX_mem_lattice (hS t ht)
  · rw [Finset.coe_image]
    exact (reflX.toLinearMap.image_convexHull _)

theorem IsLatticePolygon.image_reflY (hP : IsLatticePolygon P) :
    IsLatticePolygon (reflY '' P) := by
  classical
  obtain ⟨S, hS, rfl⟩ := hP
  refine ⟨S.image reflY, fun s hs => ?_, ?_⟩
  · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hs
    exact reflY_mem_lattice (hS t ht)
  · rw [Finset.coe_image]
    exact (reflY.toLinearMap.image_convexHull _)

theorem pt_mem_reflX_iff {s t : ℝ} : pt s t ∈ reflX '' P ↔ pt (-s) t ∈ P := by
  constructor
  · rintro ⟨x, hx, hxe⟩
    have : x = pt (-s) t := by
      have h0 := congrFun hxe 0; have h1 := congrFun hxe 1
      simp [reflX_apply] at h0 h1
      refine vec2_ext ?_ ?_ <;> simp [← h0, h1]
    rwa [this] at hx
  · intro h
    refine ⟨_, h, ?_⟩
    refine vec2_ext ?_ ?_ <;> simp [reflX_apply]

theorem pt_mem_reflY_iff {s t : ℝ} : pt s t ∈ reflY '' P ↔ pt s (-t) ∈ P := by
  constructor
  · rintro ⟨x, hx, hxe⟩
    have : x = pt s (-t) := by
      have h0 := congrFun hxe 0; have h1 := congrFun hxe 1
      simp [reflY_apply] at h0 h1
      refine vec2_ext ?_ ?_ <;> simp [h0, ← h1]
    rwa [this] at hx
  · intro h
    refine ⟨_, h, ?_⟩
    refine vec2_ext ?_ ?_ <;> simp [reflY_apply]

theorem hsec_reflX (t : ℝ) : hsec (reflX '' P) t = -hsec P t := by
  ext s; simp only [Set.mem_neg]; exact pt_mem_reflX_iff

theorem hsec_reflY (t : ℝ) : hsec (reflY '' P) t = hsec P (-t) := by
  ext s; exact pt_mem_reflY_iff

theorem rowHi_reflX (t : ℝ) : rowHi (reflX '' P) t = -rowLo P t := by
  rw [rowHi, hsec_reflX, Real.sSup_neg, rowLo]

theorem rowLo_reflX (t : ℝ) : rowLo (reflX '' P) t = -rowHi P t := by
  rw [rowLo, hsec_reflX, Real.sInf_neg, rowHi]

theorem rowHi_reflY (t : ℝ) : rowHi (reflY '' P) t = rowHi P (-t) := by
  rw [rowHi, hsec_reflY, rowHi]

theorem rowLo_reflY (t : ℝ) : rowLo (reflY '' P) t = rowLo P (-t) := by
  rw [rowLo, hsec_reflY, rowLo]

theorem image_snd_reflX :
    (fun x : Fin 2 → ℝ => x 1) '' (reflX '' P) = (fun x : Fin 2 → ℝ => x 1) '' P := by
  rw [Set.image_image]; rfl

theorem image_snd_reflY :
    (fun x : Fin 2 → ℝ => x 1) '' (reflY '' P) = -((fun x : Fin 2 → ℝ => x 1) '' P) := by
  ext t
  simp only [Set.image_image, mem_image, Set.mem_neg, reflY_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, by simp⟩
  · rintro ⟨x, hx, hxt⟩; exact ⟨x, hx, by simp [hxt]⟩

theorem yLo_reflX : yLo (reflX '' P) = yLo P := by rw [yLo, image_snd_reflX, yLo]

theorem yHi_reflX : yHi (reflX '' P) = yHi P := by rw [yHi, image_snd_reflX, yHi]

theorem yLo_reflY : yLo (reflY '' P) = -yHi P := by rw [yLo, image_snd_reflY, Real.sInf_neg, yHi]

theorem yHi_reflY : yHi (reflY '' P) = -yLo P := by rw [yHi, image_snd_reflY, Real.sSup_neg, yLo]

/-! ### The extreme rows of a lattice polygon are integral -/

/-- The bottom height `y_min` is an integer, attained at a vertex. -/
theorem IsLatticePolygon.isInt_yLo (hP : IsLatticePolygon P) (hne : P.Nonempty) :
    IsInt (yLo P) := by
  obtain ⟨S, hS, rfl⟩ := hP
  have hSne : S.Nonempty := by
    rw [← Finset.coe_nonempty, ← convexHull_nonempty_iff (𝕜 := ℝ)]; exact hne
  obtain ⟨s₀, hs₀, hmin⟩ := S.exists_min_image (fun s => s 1) hSne
  have hle : ∀ p ∈ convexHull ℝ (S : Set (Fin 2 → ℝ)), s₀ 1 ≤ p 1 := by
    intro p hp
    have := le_of_mem_convexHull (lin2 0 (-1)) (M := -s₀ 1) (fun s hs => by
      simp only [lin2_apply, zero_mul, zero_add, neg_mul, one_mul, neg_le_neg_iff]
      exact hmin s hs) hp
    simp at this; linarith
  have hy : yLo (convexHull ℝ (S : Set (Fin 2 → ℝ))) = s₀ 1 := by
    refine IsLeast.csInf_eq ⟨⟨s₀, subset_convexHull ℝ _ hs₀, rfl⟩, ?_⟩
    rintro _ ⟨p, hp, rfl⟩; exact hle p hp
  obtain ⟨a, b, -, hb⟩ := int_coords (hS s₀ hs₀)
  exact ⟨b, by rw [hy, hb]⟩

theorem IsLatticePolygon.isInt_yHi (hP : IsLatticePolygon P) (hne : P.Nonempty) :
    IsInt (yHi P) := by
  have := hP.image_reflY.isInt_yLo (hne.image _)
  rw [yLo_reflY] at this
  simpa using this.neg

/-- The right end of the bottom row is an integer. -/
theorem IsLatticePolygon.isInt_rowHi_yLo (hP : IsLatticePolygon P) (hne : P.Nonempty) :
    IsInt (rowHi P (yLo P)) := by
  have hc := hP.isCompact
  have hv := hP.convex
  have hy := hP.isInt_yLo hne
  obtain ⟨S, hS, rfl⟩ := hP
  set y₀ := yLo (convexHull ℝ (S : Set (Fin 2 → ℝ)))
  have hSne : S.Nonempty := by
    rw [← Finset.coe_nonempty, ← convexHull_nonempty_iff (𝕜 := ℝ)]; exact hne
  -- the vertices on the bottom row
  have hbot : ∃ s ∈ S, s 1 = y₀ := by
    obtain ⟨s₀, hs₀, hmin⟩ := S.exists_min_image (fun s => s 1) hSne
    refine ⟨s₀, hs₀, le_antisymm ?_ ?_⟩
    · have := (hsec_nonempty_iff hc hv hne y₀).1
      have hmem : y₀ ∈ (fun x : Fin 2 → ℝ => x 1) '' convexHull ℝ (S : Set (Fin 2 → ℝ)) := by
        rw [image_snd_eq_Icc hc hv hne]; exact ⟨le_rfl, yLo_le_yHi hc hv hne⟩
      obtain ⟨p, hp, hp1⟩ := hmem
      have := le_of_mem_convexHull (lin2 0 (-1)) (M := -s₀ 1) (fun s hs => by
        simp only [lin2_apply, zero_mul, zero_add, neg_mul, one_mul, neg_le_neg_iff]
        exact hmin s hs) hp
      simp at this; rw [← hp1]; linarith
    · exact (mem_Icc_of_mem hc hv (subset_convexHull ℝ _ hs₀)).1
  classical
  set T := S.filter (fun s => s 1 = y₀)
  have hTne : T.Nonempty := by
    obtain ⟨s, hs, hs1⟩ := hbot; exact ⟨s, Finset.mem_filter.2 ⟨hs, hs1⟩⟩
  obtain ⟨s₁, hs₁T, hmax⟩ := T.exists_max_image (fun s => s 0) hTne
  obtain ⟨hs₁, hs₁y⟩ := Finset.mem_filter.1 hs₁T
  obtain ⟨M₀s, hM₀s, hM₀⟩ := S.exists_max_image (fun s => s 0) hSne
  set K := M₀s 0 - s₁ 0 with hK
  have hK0 : 0 ≤ K := by have := hM₀ s₁ hs₁; simp only [hK]; linarith
  have hall : ∀ p ∈ convexHull ℝ (S : Set (Fin 2 → ℝ)), p 0 - K * p 1 ≤ s₁ 0 - K * y₀ := by
    intro p hp
    have := le_of_mem_convexHull (lin2 1 (-K)) (M := s₁ 0 - K * y₀) (fun s hs => by
      simp only [lin2_apply, one_mul, neg_mul]
      by_cases hsy : s 1 = y₀
      · have := hmax s (Finset.mem_filter.2 ⟨hs, hsy⟩)
        rw [hsy]; linarith
      · have hge : y₀ ≤ s 1 := (mem_Icc_of_mem hc hv (subset_convexHull ℝ _ hs)).1
        have hlt : y₀ < s 1 := lt_of_le_of_ne hge (Ne.symm hsy)
        obtain ⟨a, b, -, hb⟩ := int_coords (hS s hs)
        have h1 := hy.add_one_le_of_lt ⟨b, hb⟩ hlt
        have := hM₀ s hs
        nlinarith) hp
    simpa using this
  have hrow : rowHi (convexHull ℝ (S : Set (Fin 2 → ℝ))) y₀ = s₁ 0 := by
    refine le_antisymm ?_ ?_
    · have hne' := (hsec_nonempty_iff hc hv hne y₀).2 ⟨le_rfl, yLo_le_yHi hc hv hne⟩
      have := hall _ (pt_rowHi_mem hc hne')
      simp at this; linarith
    · refine le_rowHi hc ?_
      have : pt (s₁ 0) y₀ = s₁ := by rw [← hs₁y, pt_eta]
      rw [this]; exact subset_convexHull ℝ _ hs₁
  obtain ⟨a, b, ha, -⟩ := int_coords (hS s₁ hs₁)
  exact ⟨a, by rw [hrow, ha]⟩

theorem IsLatticePolygon.isInt_rowLo_yLo (hP : IsLatticePolygon P) (hne : P.Nonempty) :
    IsInt (rowLo P (yLo P)) := by
  have := hP.image_reflX.isInt_rowHi_yLo (hne.image _)
  rw [yLo_reflX, rowHi_reflX] at this
  simpa using this.neg

theorem IsLatticePolygon.isInt_rowHi_yHi (hP : IsLatticePolygon P) (hne : P.Nonempty) :
    IsInt (rowHi P (yHi P)) := by
  have := hP.image_reflY.isInt_rowHi_yLo (hne.image _)
  rwa [yLo_reflY, rowHi_reflY, neg_neg] at this

theorem IsLatticePolygon.isInt_rowLo_yHi (hP : IsLatticePolygon P) (hne : P.Nonempty) :
    IsInt (rowLo P (yHi P)) := by
  have := hP.image_reflY.isInt_rowLo_yLo (hne.image _)
  rwa [yLo_reflY, rowLo_reflY, neg_neg] at this

/-! ### Between integral rows the right end is affine -/

/-- The chord of `f` through `a` and `b`, evaluated at `x`. -/
def chord (f : ℝ → ℝ) (a b x : ℝ) : ℝ := f a + (f b - f a) * (x - a) / (b - a)

/-- A concave function lies below its chord to the left of the chord. -/
theorem concave_le_chord_left {f : ℝ → ℝ} {s : Set ℝ} (hf : ConcaveOn ℝ s f) {x a b : ℝ}
    (hx : x ∈ s) (hb : b ∈ s) (hxa : x ≤ a) (hab : a < b) : f x ≤ chord f a b x := by
  have hba : 0 < b - a := sub_pos.2 hab
  rcases hxa.eq_or_lt with rfl | hxa
  · simp [chord]
  have h := hf.slope_anti_adjacent hx hb hxa hab
  rw [div_le_div_iff₀ hba (sub_pos.2 hxa)] at h
  unfold chord
  rw [show f a + (f b - f a) * (x - a) / (b - a) =
      (f a * (b - a) + (f b - f a) * (x - a)) / (b - a) by field_simp, le_div_iff₀ hba]
  nlinarith

/-- A concave function lies below its chord to the right of the chord. -/
theorem concave_le_chord_right {f : ℝ → ℝ} {s : Set ℝ} (hf : ConcaveOn ℝ s f) {x a b : ℝ}
    (ha : a ∈ s) (hx : x ∈ s) (hbx : b ≤ x) (hab : a < b) : f x ≤ chord f a b x := by
  have hba : 0 < b - a := sub_pos.2 hab
  rcases hbx.eq_or_lt with rfl | hbx
  · unfold chord; field_simp; ring_nf; rfl
  have h := hf.slope_anti_adjacent ha hx hab hbx
  rw [div_le_div_iff₀ (sub_pos.2 hbx) hba] at h
  unfold chord
  rw [show f a + (f b - f a) * (x - a) / (b - a) =
      (f a * (b - a) + (f b - f a) * (x - a)) / (b - a) by field_simp, le_div_iff₀ hba]
  nlinarith

/-- A concave function lies above its chord between the chord's ends. -/
theorem chord_le_concave {f : ℝ → ℝ} {s : Set ℝ} (hf : ConcaveOn ℝ s f) {x a b : ℝ}
    (ha : a ∈ s) (hb : b ∈ s) (hab : a < b) (hx : x ∈ Icc a b) : chord f a b x ≤ f x := by
  have hba : 0 < b - a := sub_pos.2 hab
  set θ := (b - x) / (b - a)
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith [hx.2]) hba.le
  have hθ1 : 0 ≤ 1 - θ := by
    rw [sub_nonneg, div_le_one hba]; linarith [hx.1]
  have hxe : θ • a + (1 - θ) • b = x := by
    simp only [smul_eq_mul, θ]; field_simp; ring
  have h := hf.2 ha hb hθ0 hθ1 (by ring)
  rw [hxe] at h
  simp only [smul_eq_mul, θ] at h
  unfold chord
  rw [show f a + (f b - f a) * (x - a) / (b - a) =
      (b - x) / (b - a) * f a + (1 - (b - x) / (b - a)) * f b by field_simp; ring]
  exact h

/-- **Between consecutive integral rows the right end is affine.** For integer heights `a < b` in
the height range of a lattice polygon such that no row strictly between them has an integral
right end, `r` agrees with its chord on `[a, b]`. -/
theorem IsLatticePolygon.rowHi_eq_chord (hP : IsLatticePolygon P) (hne : P.Nonempty) {a b : ℤ}
    (hab : (a : ℝ) < b) (ha : yLo P ≤ a) (hb : (b : ℝ) ≤ yHi P)
    (hgap : ∀ k : ℤ, (a : ℝ) < k → (k : ℝ) < b → ¬ IsInt (rowHi P k)) {t : ℝ}
    (ht : t ∈ Icc (a : ℝ) b) : rowHi P t = chord (rowHi P) a b t := by
  have hc := hP.isCompact
  have hv := hP.convex
  have hconc := concaveOn_rowHi hc hv hne
  have haI : (a : ℝ) ∈ Icc (yLo P) (yHi P) := ⟨ha, hab.le.trans hb⟩
  have hbI : (b : ℝ) ∈ Icc (yLo P) (yHi P) := ⟨ha.trans hab.le, hb⟩
  have htI : t ∈ Icc (yLo P) (yHi P) := ⟨ha.trans ht.1, ht.2.trans hb⟩
  refine le_antisymm ?_ (chord_le_concave hconc haI hbI hab ht)
  -- the chord as a linear inequality `x - σ y ≤ c₀`
  set σ := (rowHi P b - rowHi P a) / ((b : ℝ) - a) with hσ
  set c₀ := rowHi P a - σ * a with hc₀
  have hchord : ∀ y, chord (rowHi P) a b y = σ * y + c₀ := by
    intro y; simp only [chord, hσ, hc₀]; ring
  obtain ⟨S, hS, hPS⟩ := hP
  have hSne : S.Nonempty := by
    rw [← Finset.coe_nonempty, ← convexHull_nonempty_iff (𝕜 := ℝ), ← hPS]; exact hne
  obtain ⟨s', hs', hmax⟩ := S.exists_max_image (fun s => s 0 - σ * s 1) hSne
  have hall : ∀ p ∈ P, p 0 - σ * p 1 ≤ s' 0 - σ * s' 1 := by
    intro p hp
    rw [hPS] at hp
    have := le_of_mem_convexHull (lin2 1 (-σ)) (M := s' 0 - σ * s' 1)
      (fun s hs => by simpa [lin2_apply] using (by linarith [hmax s hs] :
        s 0 - σ * s 1 ≤ s' 0 - σ * s' 1)) hp
    simpa [lin2_apply] using this
  have hs'P : s' ∈ P := by rw [hPS]; exact subset_convexHull ℝ _ hs'
  have hs'I := mem_Icc_of_mem hc hv hs'P
  have hs'r : s' 0 ≤ rowHi P (s' 1) := le_rowHi hc (by rw [pt_eta]; exact hs'P)
  have hbound : s' 0 - σ * s' 1 ≤ c₀ := by
    by_contra hgt
    push Not at hgt
    rcases le_or_gt (s' 1) a with h1 | h1
    · have := concave_le_chord_left hconc hs'I hbI h1 hab
      rw [hchord] at this; linarith
    rcases le_or_gt (b : ℝ) (s' 1) with h2 | h2
    · have := concave_le_chord_right hconc haI hs'I h2 hab
      rw [hchord] at this; linarith
    obtain ⟨u, k, -, hk⟩ := int_coords (hS s' hs')
    have hrk := hall _ (pt_rowHi_mem hc ((hsec_nonempty_iff hc hv hne _).2 hs'I))
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hrk
    have heq : rowHi P (s' 1) = s' 0 := le_antisymm (by linarith) hs'r
    rw [hk] at h1 h2 heq
    obtain ⟨u', -, hu', -⟩ := int_coords (hS s' hs')
    exact hgap k h1 h2 ⟨u', by rw [heq, hu']⟩
  have := hall _ (pt_rowHi_mem hc ((hsec_nonempty_iff hc hv hne t).2 htI))
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
  rw [hchord]
  linarith

/-! ### Sums over integer rows -/

/-- The defect `⌊x⌋ + ⌈x⌉ - 2x`, zero exactly at integers. -/
def fcDefect (x : ℝ) : ℝ := (⌊x⌋ : ℝ) + ⌈x⌉ - 2 * x

theorem fcDefect_of_isInt {x : ℝ} (hx : IsInt x) : fcDefect x = 0 := by
  obtain ⟨n, rfl⟩ := hx
  simp [fcDefect]; ring

/-- `fcDefect (m - x) = -fcDefect x` for an integer `m`. -/
theorem fcDefect_int_sub {m x : ℝ} (hm : IsInt m) : fcDefect (m - x) = -fcDefect x := by
  obtain ⟨n, rfl⟩ := hm
  rw [sub_eq_add_neg, fcDefect, fcDefect, Int.floor_intCast_add, Int.ceil_intCast_add,
    Int.floor_neg, Int.ceil_neg]
  push_cast; ring

/-- **The reflection `k ↦ a + b - k`.** If `u` is affine on `[a, b]` with integer values at both
ends, the defects of `u` at the integer points of `[a, b]` cancel. -/
theorem sum_fcDefect_affine {u : ℝ → ℝ} {a b : ℤ} (hab : (a : ℝ) < b)
    (haff : ∀ t ∈ Icc (a : ℝ) b, u t = chord u a b t) (hua : IsInt (u a)) (hub : IsInt (u b)) :
    ∑ k ∈ Finset.Icc a b, fcDefect (u k) = 0 := by
  have hrefl : ∀ k ∈ Finset.Icc a b, fcDefect (u ((a + b - k : ℤ) : ℝ)) = -fcDefect (u k) := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.1 hk
    have hk1' : (a : ℝ) ≤ k := by exact_mod_cast hk1
    have hk2' : (k : ℝ) ≤ b := by exact_mod_cast hk2
    have h1 := haff k ⟨hk1', hk2'⟩
    have h2 := haff ((a + b - k : ℤ) : ℝ) ⟨by push_cast; linarith, by push_cast; linarith⟩
    have hsum : u ((a + b - k : ℤ) : ℝ) = (u a + u b) - u k := by
      have hba : (b : ℝ) - a ≠ 0 := sub_ne_zero.2 hab.ne'
      rw [h1, h2]; simp only [chord]; push_cast
      field_simp; ring
    rw [hsum]
    exact fcDefect_int_sub (hua.add hub)
  have hre : ∑ k ∈ Finset.Icc a b, fcDefect (u k) =
      ∑ k ∈ Finset.Icc a b, fcDefect (u ((a + b - k : ℤ) : ℝ)) := by
    refine Finset.sum_nbij' (fun k => a + b - k) (fun k => a + b - k) ?_ ?_ ?_ ?_ ?_
    · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
    · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
    · intro k _; omega
    · intro k _; omega
    · intro k _; rw [show a + b - (a + b - k) = k by ring]
  rw [Finset.sum_congr rfl hrefl, Finset.sum_neg_distrib] at hre
  linarith

/-- **The defects cancel over the whole height range**, when `u` has integer values at both ends
and is affine between consecutive integer points where it takes integer values. -/
theorem sum_fcDefect_eq_zero {u : ℝ → ℝ} {A B : ℤ} (huA : IsInt (u A))
    (haff : ∀ a b : ℤ, A ≤ a → (a : ℝ) < b → b ≤ B → IsInt (u a) → IsInt (u b) →
      (∀ k : ℤ, (a : ℝ) < k → (k : ℝ) < b → ¬ IsInt (u k)) →
      ∀ t ∈ Icc (a : ℝ) b, u t = chord u a b t) :
    ∀ b : ℤ, A ≤ b → b ≤ B → IsInt (u b) → ∑ k ∈ Finset.Icc A b, fcDefect (u k) = 0 := by
  classical
  intro b hAb hbB hub
  obtain ⟨n, hn⟩ : ∃ n : ℕ, b = A + n := ⟨(b - A).toNat, by omega⟩
  induction n using Nat.strong_induction_on generalizing b with
  | _ n ih => ?_
  rcases hAb.eq_or_lt with rfl | hlt
  · simp [fcDefect_of_isInt huA]
  set T := (Finset.Ico A b).filter (fun k : ℤ => IsInt (u (k : ℝ))) with hT
  have hTne : T.Nonempty := ⟨A, Finset.mem_filter.2 ⟨Finset.mem_Ico.2 ⟨le_rfl, hlt⟩, huA⟩⟩
  set a := T.max' hTne with ha
  have haT := T.max'_mem hTne
  obtain ⟨haIco, hua⟩ := Finset.mem_filter.1 haT
  obtain ⟨hAa, hab⟩ := Finset.mem_Ico.1 haIco
  have hgap : ∀ k : ℤ, (a : ℝ) < k → (k : ℝ) < b → ¬ IsInt (u k) := by
    intro k hak hkb hk
    have hak' : a < k := by exact_mod_cast hak
    have hkb' : k < b := by exact_mod_cast hkb
    have hkT : k ∈ T := Finset.mem_filter.2 ⟨Finset.mem_Ico.2 ⟨by omega, hkb'⟩, hk⟩
    have := T.le_max' k hkT
    omega
  have habR : (a : ℝ) < b := by exact_mod_cast hab
  have hpiece := sum_fcDefect_affine habR (haff a b hAa habR hbB hua hub hgap) hua hub
  have hIH := ih (a - A).toNat (by omega) a hAa (by omega) hua (by omega)
  rw [Finset.Icc_eq_cons_Ioc hab.le, Finset.sum_cons, fcDefect_of_isInt hua, zero_add]
    at hpiece
  have hsplit : Finset.Icc A b = Finset.Icc A a ∪ Finset.Ioc a b := by
    ext k; simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hdisj : Disjoint (Finset.Icc A a) (Finset.Ioc a b) := by
    rw [Finset.disjoint_left]; intro k hk1 hk2
    simp only [Finset.mem_Icc, Finset.mem_Ioc] at hk1 hk2; omega
  rw [hsplit, Finset.sum_union hdisj, hIH, hpiece, add_zero]

/-- **The trapezoid rule is exact** for a function that is affine on every unit interval:
`∫_A^B u = Σ_{A ≤ k ≤ B} u(k) - (u(A) + u(B))/2`. -/
theorem integral_eq_trapezoid {u : ℝ → ℝ} {A B₀ : ℤ}
    (hconc : ConcaveOn ℝ (Icc (A : ℝ) B₀) u)
    (haff : ∀ k : ℤ, A ≤ k → k < B₀ → ∀ t ∈ Icc (k : ℝ) ((k + 1 : ℤ) : ℝ),
      u t = chord u k (k + 1 : ℤ) t) :
    ∀ B : ℤ, A ≤ B → B ≤ B₀ →
      ∫ t in (A : ℝ)..B, u t = ∑ k ∈ Finset.Icc A B, u k - (u A + u B) / 2 := by
  intro B hAB
  induction B, hAB using Int.leInduction with
  | base => intro _; simp
  | succ B hAB ih =>
    intro hB
    have hBB : B < B₀ := by omega
    have hB' : (B : ℝ) ≤ B + 1 := by linarith
    have hcB : ConcaveOn ℝ (Icc (A : ℝ) B) u :=
      hconc.subset (Icc_subset_Icc le_rfl (by exact_mod_cast hBB.le)) (convex_Icc _ _)
    have hcB1 : ConcaveOn ℝ (Icc (B : ℝ) (B + 1)) u :=
      hconc.subset (Icc_subset_Icc (by exact_mod_cast hAB) (by exact_mod_cast hBB)) (convex_Icc _ _)
    have hi1 : IntervalIntegrable u volume (A : ℝ) B :=
      concave_intervalIntegrable (by exact_mod_cast hAB) hcB
    have hi2 : IntervalIntegrable u volume (B : ℝ) (B + 1) := concave_intervalIntegrable hB' hcB1
    have hpiece : ∫ t in (B : ℝ)..(B + 1), u t = (u B + u (B + 1)) / 2 := by
      have heq : Set.EqOn u (fun t => u B + (u (B + 1) - u B) * (t - B)) (uIcc (B : ℝ) (B + 1)) := by
        intro t ht
        rw [uIcc_of_le hB'] at ht
        have := haff B hAB hBB t (by push_cast; exact ht)
        rw [this]; simp only [chord]; push_cast; ring
      rw [intervalIntegral.integral_congr heq, integral_affine_from_left]
      ring
    have hins : Finset.Icc A (B + 1) = insert (B + 1) (Finset.Icc A B) := by
      ext k; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
    have hnot : B + 1 ∉ Finset.Icc A B := by simp
    push_cast
    rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2, ih hBB.le, hpiece, hins,
      Finset.sum_insert hnot]
    push_cast
    ring

/-! ### Assembling Pick's theorem -/

theorem sum_Icc_eq_ends_add_Ioo (f : ℤ → ℝ) {A B : ℤ} (h : A < B) :
    ∑ k ∈ Finset.Icc A B, f k = f A + f B + ∑ k ∈ Finset.Ioo A B, f k := by
  have hset : Finset.Icc A B = insert A (insert B (Finset.Ioo A B)) := by
    ext k; simp only [Finset.mem_insert, Finset.mem_Icc, Finset.mem_Ioo]; omega
  have h1 : B ∉ Finset.Ioo A B := by simp
  have h2 : A ∉ insert B (Finset.Ioo A B) := by
    simp only [Finset.mem_insert, Finset.mem_Ioo]; omega
  rw [hset, Finset.sum_insert h2, Finset.sum_insert h1]; ring

/-- For a lattice polygon with integral height range `[A, B]`, the defects of `r` cancel. -/
theorem IsLatticePolygon.sum_fcDefect_rowHi (hP : IsLatticePolygon P) (hne : P.Nonempty)
    {A B : ℤ} (hA : yLo P = A) (hB : yHi P = B) :
    ∑ k ∈ Finset.Icc A B, fcDefect (rowHi P k) = 0 := by
  have hc := hP.isCompact
  have hv := hP.convex
  have hAB : A ≤ B := by
    have := yLo_le_yHi hc hv hne; rw [hA, hB] at this; exact_mod_cast this
  have huA : IsInt (rowHi P A) := by rw [← hA]; exact hP.isInt_rowHi_yLo hne
  have huB : IsInt (rowHi P B) := by rw [← hB]; exact hP.isInt_rowHi_yHi hne
  refine sum_fcDefect_eq_zero huA (fun a b hAa hab hbB _ _ hgap t ht => ?_) B hAB le_rfl huB
  exact hP.rowHi_eq_chord hne hab (by rw [hA]; exact_mod_cast hAa)
    (by rw [hB]; exact_mod_cast hbB) hgap ht

/-- For a lattice polygon with integral height range `[A, B]`, `∫_A^B r` is the trapezoid sum. -/
theorem IsLatticePolygon.integral_rowHi (hP : IsLatticePolygon P) (hne : P.Nonempty)
    {A B : ℤ} (hA : yLo P = A) (hB : yHi P = B) :
    ∫ t in (A : ℝ)..B, rowHi P t =
      ∑ k ∈ Finset.Icc A B, rowHi P k - (rowHi P A + rowHi P B) / 2 := by
  have hc := hP.isCompact
  have hv := hP.convex
  have hAB : A ≤ B := by
    have := yLo_le_yHi hc hv hne; rw [hA, hB] at this; exact_mod_cast this
  have hconc := concaveOn_rowHi hc hv hne
  rw [hA, hB] at hconc
  refine integral_eq_trapezoid hconc (fun k hAk hkB t ht => ?_) B hAB le_rfl
  have hk1 : (k : ℝ) < ((k + 1 : ℤ) : ℝ) := by push_cast; linarith
  refine hP.rowHi_eq_chord hne hk1 (by rw [hA]; exact_mod_cast hAk)
    (by rw [hB]; exact_mod_cast (show k + 1 ≤ B by omega)) (fun j hj1 hj2 => ?_) ht
  exfalso
  have : k < j := by exact_mod_cast hj1
  have : j < k + 1 := by exact_mod_cast hj2
  omega

theorem fcDefect_neg (x : ℝ) : fcDefect (-x) = -fcDefect x := by
  have := fcDefect_int_sub (m := 0) (x := x) ⟨0, by simp⟩
  simpa using this

/-- **Pick's theorem, sum form**: `G(P) + G(int P) = 2 vol(P) + 2` for a lattice polygon with
non-empty interior. -/
theorem IsLatticePolygon.ncard_add_ncard_interior (hP : IsLatticePolygon P)
    (hint : (interior P).Nonempty) :
    (G2 P : ℝ) + G2 (interior P) = 2 * (volume P).toReal + 2 := by
  have hne : P.Nonempty := hint.mono interior_subset
  have hc := hP.isCompact
  have hv := hP.convex
  obtain ⟨A, hA⟩ := hP.isInt_yLo hne
  obtain ⟨B, hB⟩ := hP.isInt_yHi hne
  have hlt : (A : ℝ) < B := by
    obtain ⟨c, hcI⟩ := hint
    have := ((mem_interior_iff_rows hc hv hne c).1 hcI).1
    rw [hA, hB] at this; exact this.1.trans this.2
  have hltZ : A < B := by exact_mod_cast hlt
  set r := rowHi P with hr
  set l := rowLo P with hl
  -- the reflected polygon carries `l`
  have hQ := hP.image_reflX
  have hQne : (reflX '' P).Nonempty := hne.image _
  have hQA : yLo (reflX '' P) = A := by rw [yLo_reflX, hA]
  have hQB : yHi (reflX '' P) = B := by rw [yHi_reflX, hB]
  have hlr : ∀ t, rowHi (reflX '' P) t = -l t := fun t => rowHi_reflX t
  -- defect sums
  have hdr := hP.sum_fcDefect_rowHi hne hA hB
  have hdl : ∑ k ∈ Finset.Icc A B, fcDefect (l k) = 0 := by
    have := hQ.sum_fcDefect_rowHi hQne hQA hQB
    simp only [hlr, fcDefect_neg, Finset.sum_neg_distrib, neg_eq_zero] at this
    exact this
  -- trapezoid sums
  have hir := hP.integral_rowHi hne hA hB
  have hil : ∫ t in (A : ℝ)..B, -l t = ∑ k ∈ Finset.Icc A B, -l k - (-l A + -l B) / 2 := by
    have := hQ.integral_rowHi hQne hQA hQB
    simp only [hlr] at this
    exact this
  -- the volume
  have hvol := volume_eq_integral_rows hc hv hne
  rw [hA, hB] at hvol
  have hconcR := concaveOn_rowHi hc hv hne
  have hconvL := convexOn_rowLo hc hv hne
  rw [hA, hB] at hconcR hconvL
  have hiR : IntervalIntegrable r volume (A : ℝ) B := concave_intervalIntegrable hlt.le hconcR
  have hiL : IntervalIntegrable (fun t => -l t) volume (A : ℝ) B :=
    concave_intervalIntegrable hlt.le hconvL.neg
  have hwidth : ∫ t in (A : ℝ)..B, (r t - l t) =
      (∫ t in (A : ℝ)..B, r t) + ∫ t in (A : ℝ)..B, -l t := by
    rw [← intervalIntegral.integral_add hiR hiL]; congr 1
  have hwpos : 0 ≤ ∫ t in (A : ℝ)..B, (r t - l t) := by
    refine intervalIntegral.integral_nonneg hlt.le fun t ht => ?_
    have := rowLo_le_rowHi hc ((hsec_nonempty_iff hc hv hne t).2 (by rw [hA, hB]; exact ht))
    simp only [hr, hl]; linarith
  have hV : (volume P).toReal = ∫ t in (A : ℝ)..B, (r t - l t) := by
    rw [hvol, ENNReal.toReal_ofReal hwpos]
  -- the row counts
  have hG := ncard_latticePoints_eq_rows hc hv hne
  have hGi := ncard_latticePoints_interior_eq_rows hc hv hne
  rw [hA, hB, Int.ceil_intCast, Int.floor_intCast] at hG
  rw [hA, hB, Int.floor_intCast, Int.ceil_intCast] at hGi
  have hGr : (G2 P : ℝ) = ∑ k ∈ Finset.Icc A B, ((⌊r k⌋ : ℝ) + 1 - ⌈l k⌉) := by
    show ((DiscreteMinkowski.latticePoints P (standardIntegerLattice 2)).ncard : ℝ) = _
    rw [hG]; push_cast
    refine Finset.sum_congr rfl fun k hk => ?_
    obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.1 hk
    have hkI : (k : ℝ) ∈ Icc (yLo P) (yHi P) := by
      rw [hA, hB]; exact ⟨by exact_mod_cast hk1, by exact_mod_cast hk2⟩
    have hle := rowLo_le_rowHi hc ((hsec_nonempty_iff hc hv hne k).2 hkI)
    have h1 : ⌈l k⌉ ≤ ⌊r k⌋ + 1 :=
      (Int.ceil_le_ceil hle).trans (Int.ceil_le_floor_add_one _)
    have := Int.card_Icc_of_le _ _ h1
    exact_mod_cast this
  have hGir : (G2 (interior P) : ℝ) = ∑ k ∈ Finset.Ioo A B, ((⌈r k⌉ : ℝ) - ⌊l k⌋ - 1) := by
    show ((DiscreteMinkowski.latticePoints (interior P) (standardIntegerLattice 2)).ncard : ℝ) = _
    rw [hGi]; push_cast
    refine Finset.sum_congr rfl fun k hk => ?_
    obtain ⟨hk1, hk2⟩ := Finset.mem_Ioo.1 hk
    have hkI : (k : ℝ) ∈ Ioo (yLo P) (yHi P) := by
      rw [hA, hB]; exact ⟨by exact_mod_cast hk1, by exact_mod_cast hk2⟩
    have hlt' := rowLo_lt_rowHi hc hv hint hkI
    have h1 : ⌊l k⌋ < ⌈r k⌉ := by
      have : (⌊l k⌋ : ℝ) < ⌈r k⌉ := (Int.floor_le _).trans_lt (hlt'.trans_le (Int.le_ceil _))
      exact_mod_cast this
    have := Int.card_Ioo_of_lt _ _ h1
    exact_mod_cast this
  -- integral end values
  obtain ⟨rA, hrA⟩ := (show IsInt (r A) by rw [hr, ← hA]; exact hP.isInt_rowHi_yLo hne)
  obtain ⟨rB, hrB⟩ := (show IsInt (r B) by rw [hr, ← hB]; exact hP.isInt_rowHi_yHi hne)
  obtain ⟨lA, hlA⟩ := (show IsInt (l A) by rw [hl, ← hA]; exact hP.isInt_rowLo_yLo hne)
  obtain ⟨lB, hlB⟩ := (show IsInt (l B) by rw [hl, ← hB]; exact hP.isInt_rowLo_yHi hne)
  -- the interior sum over `[A, B]` with its two end rows removed
  have hends := sum_Icc_eq_ends_add_Ioo (fun k : ℤ => (⌈r k⌉ : ℝ) - ⌊l k⌋ - 1) hltZ
  rw [hrA, hrB, hlA, hlB] at hends
  simp only [Int.ceil_intCast, Int.floor_intCast] at hends
  -- defects to sums
  have hsr : ∑ k ∈ Finset.Icc A B, ((⌊r k⌋ : ℝ) + ⌈r k⌉) = 2 * ∑ k ∈ Finset.Icc A B, r k := by
    have : ∑ k ∈ Finset.Icc A B, ((⌊r k⌋ : ℝ) + ⌈r k⌉) =
        ∑ k ∈ Finset.Icc A B, fcDefect (r k) + ∑ k ∈ Finset.Icc A B, 2 * r k := by
      rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun k _ => ?_
      simp only [fcDefect]; ring
    rw [this, hdr, zero_add, Finset.mul_sum]
  have hsl : ∑ k ∈ Finset.Icc A B, ((⌊l k⌋ : ℝ) + ⌈l k⌉) = 2 * ∑ k ∈ Finset.Icc A B, l k := by
    have : ∑ k ∈ Finset.Icc A B, ((⌊l k⌋ : ℝ) + ⌈l k⌉) =
        ∑ k ∈ Finset.Icc A B, fcDefect (l k) + ∑ k ∈ Finset.Icc A B, 2 * l k := by
      rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun k _ => ?_
      simp only [fcDefect]; ring
    rw [this, hdl, zero_add, Finset.mul_sum]
  have hcomb : (G2 P : ℝ) + G2 (interior P) =
      ∑ k ∈ Finset.Icc A B, ((⌊r k⌋ : ℝ) + ⌈r k⌉) - ∑ k ∈ Finset.Icc A B, ((⌊l k⌋ : ℝ) + ⌈l k⌉)
        - ((rA : ℝ) - lA - 1) - ((rB : ℝ) - lB - 1) := by
    rw [hGr, hGir]
    have h3 : ∑ k ∈ Finset.Ioo A B, ((⌈r k⌉ : ℝ) - ⌊l k⌋ - 1) =
        ∑ k ∈ Finset.Icc A B, ((⌈r k⌉ : ℝ) - ⌊l k⌋ - 1) - ((rA : ℝ) - lA - 1) -
          ((rB : ℝ) - lB - 1) := by rw [hends]; ring
    rw [h3]
    have h4 : ∑ k ∈ Finset.Icc A B, ((⌊r k⌋ : ℝ) + 1 - ⌈l k⌉) +
        ∑ k ∈ Finset.Icc A B, ((⌈r k⌉ : ℝ) - ⌊l k⌋ - 1) =
        ∑ k ∈ Finset.Icc A B, ((⌊r k⌋ : ℝ) + ⌈r k⌉) -
          ∑ k ∈ Finset.Icc A B, ((⌊l k⌋ : ℝ) + ⌈l k⌉) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_; ring
    linarith
  have hsumL : ∑ k ∈ Finset.Icc A B, -l k = -∑ k ∈ Finset.Icc A B, l k := by
    rw [Finset.sum_neg_distrib]
  have hir' : ∫ t in (A : ℝ)..B, r t = ∑ k ∈ Finset.Icc A B, r k - (r A + r B) / 2 := hir
  rw [hcomb, hsr, hsl, hV, hwidth, hir', hil, hsumL, hrA, hrB, hlA, hlB]
  ring

/-- **Pick's theorem, Eq. (5.1)**: `G(int P) = vol(P) - G(bd P)/2 + 1` for a lattice polygon `P`
with non-empty interior, `bd P` its boundary. -/
theorem pick_theorem_interior (hP : IsLatticePolygon P) (hint : (interior P).Nonempty) :
    (G2 (interior P) : ℝ) = (volume P).toReal - (G2 (frontier P) : ℝ) / 2 + 1 := by
  have hc := hP.isCompact
  have hsum := hP.ncard_add_ncard_interior hint
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
  have hcardR : (G2 (frontier P) : ℝ) + G2 (interior P) = G2 P := by
    show ((DiscreteMinkowski.latticePoints (frontier P) (standardIntegerLattice 2)).ncard : ℝ) +
      ((DiscreteMinkowski.latticePoints (interior P) (standardIntegerLattice 2)).ncard : ℝ) =
      ((DiscreteMinkowski.latticePoints P (standardIntegerLattice 2)).ncard : ℝ)
    exact_mod_cast hcard
  linarith

end

end LatticeVolumeInterpolation
