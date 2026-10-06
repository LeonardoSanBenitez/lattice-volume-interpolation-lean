import GeneralShaking
import PlanarSections

/-!
# Lemma 5.1: the planar reduction under the lattice diagonal

Catalog item `lemma_5_1_properties_of_the_planar_reduction`.

For `K ∈ K^2` anti-blocking with `|e_i|_{cs(K)} = λ_i(K)`, the paper shakes `K` first vertically
and then horizontally against a lattice diagonal `D = {x_1 + x_2 = m}`, and finally back down
onto the axis:

  `A = T(K)`, `T = sh_{e_2} ∘ sh_{-e_1,D} ∘ sh_{-e_2,D}`.

We take `m = 0`. The paper notes that `m` is arbitrary because lattice translations change
none of the quantities involved.

In coordinates, with `D = {x_1 + x_2 = 0}`: the projection along `-e_2` onto `D` is
`(x_1, x_2) ↦ (x_1, -x_1)`, so `sh_{-e_2,D}` hangs each vertical chord from `D`; the
projection along `-e_1` is `(x_1, x_2) ↦ (-x_2, x_2)`, so `sh_{-e_1,D}` hangs each horizontal
chord to the left of `D`.
-/

open Set MeasureTheory
open scoped Pointwise

namespace LatticeVolumeInterpolation

noncomputable section

/-! ### Coordinates of the two diagonal shakings -/

theorem obliqueProj_diag_one (x : Fin 2 → ℝ) :
    obliqueProj diagNormal 0 (negAxis 1) x = pt (x 0) (-x 0) := by
  refine vec2_ext ?_ ?_ <;> simp [obliqueProj, dot2, diagNormal, negAxis]
  ring

theorem obliqueProj_diag_zero (x : Fin 2 → ℝ) :
    obliqueProj diagNormal 0 (negAxis 0) x = pt (-x 1) (x 1) := by
  refine vec2_ext ?_ ?_ <;> simp [obliqueProj, dot2, diagNormal, negAxis]
  ring

theorem add_smul_unitDir_negAxis_one (s d t : ℝ) :
    pt s d + t • unitDir (negAxis 1) = pt s (d - t) := by
  rw [unitDir_negAxis]
  refine vec2_ext ?_ ?_ <;> simp [negAxis]; ring

theorem add_smul_unitDir_negAxis_zero (s d t : ℝ) :
    pt s d + t • unitDir (negAxis 0) = pt (s - t) d := by
  rw [unitDir_negAxis]
  refine vec2_ext ?_ ?_ <;> simp [negAxis]; ring

theorem dirFibre_negAxis_one (S : Set (Fin 2 → ℝ)) (s d : ℝ) :
    dirFibre S (negAxis 1) (pt s d) = {t | pt s (d - t) ∈ S} := by
  ext t; simp only [dirFibre, mem_setOf_eq]; rw [add_smul_unitDir_negAxis_one]

theorem dirFibre_negAxis_zero (S : Set (Fin 2 → ℝ)) (s d : ℝ) :
    dirFibre S (negAxis 0) (pt s d) = {t | pt (s - t) d ∈ S} := by
  ext t; simp only [dirFibre, mem_setOf_eq]; rw [add_smul_unitDir_negAxis_zero]

/-- A set of reals inside an interval of length `β` has `sup - inf ≤ β`. -/
theorem sSup_sub_sInf_le {T : Set ℝ} {m β : ℝ} (hβ : 0 ≤ β) (hT : T ⊆ Icc m (m + β)) :
    sSup T - sInf T ≤ β := by
  rcases T.eq_empty_or_nonempty with rfl | hne
  · simp [hβ]
  · have h1 : sSup T ≤ m + β := csSup_le hne fun t ht => (hT ht).2
    have h2 : m ≤ sInf T := le_csInf hne fun t ht => (hT ht).1
    linarith

/-- Two points of a chord bound its length from below. -/
theorem le_sSup_sub_sInf {T : Set ℝ} (hA : BddAbove T) (hB : BddBelow T) {t₁ t₂ : ℝ}
    (h₁ : t₁ ∈ T) (h₂ : t₂ ∈ T) : t₂ - t₁ ≤ sSup T - sInf T := by
  have := le_csSup hA h₂
  have := csInf_le hB h₁
  linarith

/-- Elimination for `sh_{-e_2,D}`. -/
theorem mem_diagShaking_one {S : Set (Fin 2 → ℝ)} {y : Fin 2 → ℝ} (hy : y ∈ diagShaking 1 S) :
    ∃ x ∈ S, ∃ s, 0 ≤ s ∧ s ≤ dirLength S (negAxis 1) (pt (x 0) (-x 0)) ∧
      y = pt (x 0) (-x 0 - s) := by
  obtain ⟨p, ⟨x, hx, rfl⟩, s, ⟨hs0, hs1⟩, rfl⟩ := hy
  rw [obliqueProj_diag_one] at hs1 ⊢
  exact ⟨x, hx, s, hs0, hs1, add_smul_unitDir_negAxis_one _ _ _⟩

/-- Elimination for `sh_{-e_1,D}`. -/
theorem mem_diagShaking_zero {S : Set (Fin 2 → ℝ)} {y : Fin 2 → ℝ} (hy : y ∈ diagShaking 0 S) :
    ∃ x ∈ S, ∃ s, 0 ≤ s ∧ s ≤ dirLength S (negAxis 0) (pt (-x 1) (x 1)) ∧
      y = pt (-x 1 - s) (x 1) := by
  obtain ⟨p, ⟨x, hx, rfl⟩, s, ⟨hs0, hs1⟩, rfl⟩ := hy
  rw [obliqueProj_diag_zero] at hs1 ⊢
  exact ⟨x, hx, s, hs0, hs1, add_smul_unitDir_negAxis_zero _ _ _⟩

/-- Introduction for `sh_{-e_2,D}`: two points on the vertical line over `c`, at depths `t₁ ≤ t₂`
below `D`, put the point at depth `s ≤ t₂ - t₁` into the shaking. -/
theorem pt_mem_diagShaking_one {S : Set (Fin 2 → ℝ)} (hS : Bornology.IsBounded S) {c t₁ t₂ s : ℝ}
    (h₁ : pt c (-c - t₁) ∈ S) (h₂ : pt c (-c - t₂) ∈ S) (hs0 : 0 ≤ s) (hs : s ≤ t₂ - t₁) :
    pt c (-c - s) ∈ diagShaking 1 S := by
  have hp : obliqueProj diagNormal 0 (negAxis 1) (pt c (-c - t₁)) = pt c (-c) := by
    rw [obliqueProj_diag_one]; simp
  refine ⟨pt c (-c), ⟨_, h₁, hp⟩, s, ⟨hs0, ?_⟩, (add_smul_unitDir_negAxis_one _ _ _).symm⟩
  obtain ⟨hA, hB⟩ := dirFibre_bdd hS (ne_zero_of_dot2_ne_zero (dot2_diagNormal_negAxis_ne 1))
    (pt c (-c))
  rw [dirFibre_negAxis_one] at hA hB
  unfold dirLength
  rw [dirFibre_negAxis_one]
  exact hs.trans (le_sSup_sub_sInf hA hB (t₁ := t₁) (by simpa using h₁) (by simpa using h₂))

/-- Introduction for `sh_{-e_1,D}`. -/
theorem pt_mem_diagShaking_zero {S : Set (Fin 2 → ℝ)} (hS : Bornology.IsBounded S) {c t₁ t₂ s : ℝ}
    (h₁ : pt (-c - t₁) c ∈ S) (h₂ : pt (-c - t₂) c ∈ S) (hs0 : 0 ≤ s) (hs : s ≤ t₂ - t₁) :
    pt (-c - s) c ∈ diagShaking 0 S := by
  have hp : obliqueProj diagNormal 0 (negAxis 0) (pt (-c - t₁) c) = pt (-c) c := by
    rw [obliqueProj_diag_zero]; simp
  refine ⟨pt (-c) c, ⟨_, h₁, hp⟩, s, ⟨hs0, ?_⟩, (add_smul_unitDir_negAxis_zero _ _ _).symm⟩
  obtain ⟨hA, hB⟩ := dirFibre_bdd hS (ne_zero_of_dot2_ne_zero (dot2_diagNormal_negAxis_ne 0))
    (pt (-c) c)
  rw [dirFibre_negAxis_zero] at hA hB
  unfold dirLength
  rw [dirFibre_negAxis_zero]
  exact hs.trans (le_sSup_sub_sInf hA hB (t₁ := t₁) (by simpa using h₁) (by simpa using h₂))

/-- Every point of `sh_{-e_i,D}(S)` lies on or below `D`. -/
theorem diagShaking_one_sum_le {S : Set (Fin 2 → ℝ)} {y : Fin 2 → ℝ} (hy : y ∈ diagShaking 1 S) :
    y 0 + y 1 ≤ 0 := by
  obtain ⟨x, -, s, hs0, -, rfl⟩ := mem_diagShaking_one hy
  simp; linarith

theorem diagShaking_zero_sum_le {S : Set (Fin 2 → ℝ)} {y : Fin 2 → ℝ} (hy : y ∈ diagShaking 0 S) :
    y 0 + y 1 ≤ 0 := by
  obtain ⟨x, -, s, hs0, -, rfl⟩ := mem_diagShaking_zero hy
  simp; linarith

/-! ### The strip argument behind the paper's Figure 3

If all vertical (resp. horizontal) chords of `S` have length at most `β`, then the shaking
against `D` lies in the strip `{-β ≤ x_1 + x_2 ≤ 0}`, and every chord of a set in that strip, in
either axis direction, has length at most `β`. -/

theorem diagShaking_one_sum_ge {S : Set (Fin 2 → ℝ)} {β : ℝ}
    (hβ : ∀ c, dirLength S (negAxis 1) (pt c (-c)) ≤ β) {y : Fin 2 → ℝ}
    (hy : y ∈ diagShaking 1 S) : -β ≤ y 0 + y 1 := by
  obtain ⟨x, -, s, -, hs, rfl⟩ := mem_diagShaking_one hy
  have := hβ (x 0)
  simp; linarith

theorem diagShaking_zero_sum_ge {S : Set (Fin 2 → ℝ)} {β : ℝ}
    (hβ : ∀ c, dirLength S (negAxis 0) (pt (-c) c) ≤ β) {y : Fin 2 → ℝ}
    (hy : y ∈ diagShaking 0 S) : -β ≤ y 0 + y 1 := by
  obtain ⟨x, -, s, -, hs, rfl⟩ := mem_diagShaking_zero hy
  have := hβ (x 1)
  simp; linarith

theorem dirLength_zero_le_of_strip {S : Set (Fin 2 → ℝ)} {β : ℝ} (hβ0 : 0 ≤ β)
    (hS : ∀ y ∈ S, -β ≤ y 0 + y 1 ∧ y 0 + y 1 ≤ 0) (c : ℝ) :
    dirLength S (negAxis 0) (pt (-c) c) ≤ β := by
  unfold dirLength
  rw [dirFibre_negAxis_zero]
  refine sSup_sub_sInf_le (m := 0) hβ0 fun t ht => ?_
  have := hS _ ht
  simp at this
  constructor <;> linarith

theorem fibreLength_one_le_of_strip {S : Set (Fin 2 → ℝ)} {β : ℝ} (hβ0 : 0 ≤ β)
    (hS : ∀ y ∈ S, -β ≤ y 0 + y 1 ∧ y 0 + y 1 ≤ 0) (z : Fin 2 → ℝ) :
    fibreLength S 1 z ≤ β := by
  unfold fibreLength
  refine sSup_sub_sInf_le (m := -z 0 - β) hβ0 fun t ht => ?_
  have := hS _ ht
  simp at this
  constructor <;> linarith

/-! ### Axis gauges of anti-blocking bodies, and monotonicity of the coordinate shaking -/

section Axis

variable {n : ℕ}

theorem single_ne_zero' (j : Fin n) : (Pi.single j (1 : ℝ) : Fin n → ℝ) ≠ 0 := by
  intro h; have := congrFun h j; simp at this

/-- In an anti-blocking body every `j`-th coordinate is at most `2/|e_j|_{cs(K)}`. -/
theorem coord_le_two_div_axisGauge {K : Set (Fin n → ℝ)}
    (hKb : DiscreteMinkowski.IsPaperConvexBody K) (hK : IsAntiBlocking K) {z : Fin n → ℝ}
    (hz : z ∈ K) (j : Fin n) : z j ≤ 2 / axisGauge K j := by
  have hpos : 0 < axisGauge K j := DiscreteMinkowski.gauge_pos_of_ne_zero hKb (single_ne_zero' j)
  rcases (hK.1 z hz j).eq_or_lt with h0 | h0
  · rw [← h0]; positivity
  have hzj : z j • (Pi.single j (1 : ℝ) : Fin n → ℝ) ∈ K := by
    refine hK.2 z hz _ (fun i => ?_) (fun i => ?_) <;> by_cases h : i = j
    · subst h; simp [h0.le]
    · simp [Pi.single_eq_of_ne h]
    · subst h; simp
    · simp [Pi.single_eq_of_ne h, hK.1 z hz i]
  have h0K : (0 : Fin n → ℝ) ∈ K := hK.2 z hz 0 (fun _ => le_rfl) (fun i => hK.1 z hz i)
  have hmem : (Pi.single j (1 : ℝ) : Fin n → ℝ) ∈
      (2 / z j) • DiscreteMinkowski.halfDifferenceBody K := by
    rw [DiscreteMinkowski.halfDifferenceBody_apply, smul_smul]
    refine ⟨z j • Pi.single j 1 - 0, Set.sub_mem_sub hzj h0K, ?_⟩
    show (2 / z j * 2⁻¹) • (z j • Pi.single j 1 - 0) = Pi.single j 1
    rw [sub_zero, smul_smul]
    have : 2 / z j * 2⁻¹ * z j = 1 := by field_simp
    rw [this, one_smul]
  have hg := gauge_le_of_mem (by positivity) hmem
  rw [le_div_iff₀ hpos]
  rw [le_div_iff₀ h0] at hg
  linarith

/-- The axis gauge of an anti-blocking body is `2/t` when `t e_j` is its farthest point along
`e_j`. -/
theorem axisGauge_eq_of_extent {K : Set (Fin n → ℝ)} (hKc : IsCompact K)
    (hKb : DiscreteMinkowski.IsPaperConvexBody K) (hK : IsAntiBlocking K) {j : Fin n} {t : ℝ}
    (hmem : t • (Pi.single j (1 : ℝ) : Fin n → ℝ) ∈ K)
    (hmax : ∀ z ∈ K, z j ≤ t) : axisGauge K j = 2 / t := by
  have hpos : 0 < axisGauge K j := DiscreteMinkowski.gauge_pos_of_ne_zero hKb (single_ne_zero' j)
  have h1 := coord_le_two_div_axisGauge hKb hK hmem j
  have h2 := hmax _ (axis_point_mem hKc hKb hK j)
  simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h1 h2
  have : t = 2 / axisGauge K j := le_antisymm h1 h2
  rw [this]; field_simp

/-- **The coordinate shaking is monotone** (Lemma 5.3 for `sh_{e_j}`). -/
theorem coordShaking_mono {S S' : Set (Fin n → ℝ)} (hS' : IsCompact S') (h : S ⊆ S')
    (j : Fin n) : coordShaking S j ⊆ coordShaking S' j := by
  rintro z ⟨hne, h0, h1⟩
  refine ⟨hne.mono fun t ht => h ht, h0, h1.trans ?_⟩
  have hsub : fibre S j z ⊆ fibre S' j z := fun t ht => h ht
  obtain ⟨hA, hB⟩ := fibre_bdd hS' j z
  unfold fibreLength
  linarith [csSup_le_csSup hA hne hsub, csInf_le_csInf hB hne hsub]

theorem volume_pos_of_isPaperConvexBody {K : Set (Fin n → ℝ)}
    (hKb : DiscreteMinkowski.IsPaperConvexBody K) : 0 < volume K :=
  Measure.measure_pos_of_nonempty_interior _ hKb.2.2

theorem isPaperConvexBody_of {S : Set (Fin n → ℝ)} (hS : IsCompact S) (hSc : Convex ℝ S)
    (hvol : 0 < volume S) : DiscreteMinkowski.IsPaperConvexBody S :=
  ⟨hS.isBounded, hSc, interior_nonempty_of_volume_pos hSc hvol⟩

end Axis

/-! ### The reduction `T` and Lemma 5.1 -/

theorem smul_single_zero' (t : ℝ) : t • (Pi.single 0 (1 : ℝ) : Fin 2 → ℝ) = pt t 0 := by
  refine vec2_ext ?_ ?_ <;> simp

theorem smul_single_one' (t : ℝ) : t • (Pi.single 1 (1 : ℝ) : Fin 2 → ℝ) = pt 0 t := by
  refine vec2_ext ?_ ?_ <;> simp

theorem update_pt_one (s t r : ℝ) : Function.update (pt s t) 1 r = pt s r := by
  refine vec2_ext ?_ ?_ <;> simp

theorem update_pt_zero (s t r : ℝ) : Function.update (pt s t) 0 r = pt r t := by
  refine vec2_ext ?_ ?_ <;> simp

/-- `T(K) = sh_{e_2}(sh_{-e_1,D}(sh_{-e_2,D}(K)))`, with `D = {x_1 + x_2 = 0}`. -/
def planarReduction (K : Set (Fin 2 → ℝ)) : Set (Fin 2 → ℝ) :=
  coordShaking (diagShaking 0 (diagShaking 1 K)) 1

/-- The paper's successive minima `λ_i` in the plane, for `ℤ^2`. -/
abbrev lam2 (S : Set (Fin 2 → ℝ)) (i : ℕ) : ℝ :=
  DiscreteMinkowski.successiveMinimum S (standardIntegerLattice 2) i

/-- The paper's lattice point enumerator `G` in the plane. -/
abbrev G2 (S : Set (Fin 2 → ℝ)) : ℕ :=
  (DiscreteMinkowski.latticePoints S (standardIntegerLattice 2)).ncard

theorem lam2_one_le_two {S : Set (Fin 2 → ℝ)} (hS : DiscreteMinkowski.IsPaperConvexBody S) :
    lam2 S 1 ≤ lam2 S 2 :=
  DiscreteMinkowski.successiveMinimum_mono_of_le_finrank hS (by norm_num)
    (by rw [Module.finrank_fin_fun])

/-- For a planar anti-blocking body whose axis gauges satisfy `g_0 ≤ g_1`, these are `λ_1` and
`λ_2` (Lemma 3.3 in the plane). -/
theorem lam2_eq_axisGauge {S : Set (Fin 2 → ℝ)} (hSc : IsCompact S)
    (hSb : DiscreteMinkowski.IsPaperConvexBody S) (hS : IsAntiBlocking S)
    (hle : axisGauge S 0 ≤ axisGauge S 1) :
    lam2 S 1 = axisGauge S 0 ∧ lam2 S 2 = axisGauge S 1 := by
  obtain ⟨σ, hσ⟩ := lemma_3_3 hSc hSb hS
  have e0 := (hσ 0).1
  have e1 := (hσ 1).1
  simp only [Fin.isValue, Fin.val_zero, zero_add, Fin.val_one, Nat.reduceAdd] at e0 e1
  have h12 := lam2_one_le_two hSb
  have hne : σ 1 ≠ σ 0 := fun h' => absurd (σ.injective h') (by decide)
  rcases Fin.exists_fin_two.mp ⟨σ 0, rfl⟩ with h | h
  · have h' : σ 1 = 1 := by rw [h] at hne; omega
    rw [h] at e0; rw [h'] at e1
    exact ⟨e0.symm, e1.symm⟩
  · have h' : σ 1 = 0 := by rw [h] at hne; omega
    rw [h] at e0; rw [h'] at e1
    constructor <;> linarith

/-- **Lemma 5.1.** For a planar anti-blocking body `K` with `|e_i|_{cs(K)} = λ_i(K)`, the body
`A = T(K)` is i) convex (and a compact convex body), ii) anti-blocking, iii) of volume `vol(K)`,
iv) `G(A) ≥ G(K)`, v) `G(int A) ≤ G(int K)`, vi) `λ_1(A) ≤ λ_1(K)`, vii) `λ_2(A) = λ_2(K)`, and
viii) `A ⊆ {x_1 + x_2 ≤ 2/λ_1(A)}`. The last two conclusions, `|e_i|_{cs(A)} = λ_i(A)`, are
established inside the paper's proof (it shows `|e_2|_{cs(A)} = λ_2(K)` and the triangle bound) and
are what the proof of Theorem 1.4 uses when it assumes them of the reduced body. -/
theorem lemma_5_1 {K : Set (Fin 2 → ℝ)} (hKc : IsCompact K)
    (hKb : DiscreteMinkowski.IsPaperConvexBody K) (hK : IsAntiBlocking K)
    (h1 : axisGauge K 0 = lam2 K 1) (h2 : axisGauge K 1 = lam2 K 2) :
    IsCompact (planarReduction K) ∧ DiscreteMinkowski.IsPaperConvexBody (planarReduction K) ∧
      IsAntiBlocking (planarReduction K) ∧ volume (planarReduction K) = volume K ∧
      G2 K ≤ G2 (planarReduction K) ∧ G2 (interior (planarReduction K)) ≤ G2 (interior K) ∧
      lam2 (planarReduction K) 1 ≤ lam2 K 1 ∧ lam2 (planarReduction K) 2 = lam2 K 2 ∧
      (∀ x ∈ planarReduction K, x 0 + x 1 ≤ 2 / lam2 (planarReduction K) 1) ∧
      axisGauge (planarReduction K) 0 = lam2 (planarReduction K) 1 ∧
      axisGauge (planarReduction K) 1 = lam2 (planarReduction K) 2 := by
  classical
  -- the body `K` and its box `[0, a] × [0, b]`
  set g0 := axisGauge K 0 with hg0def
  set g1 := axisGauge K 1 with hg1def
  have hg0 : 0 < g0 := DiscreteMinkowski.gauge_pos_of_ne_zero hKb (single_ne_zero' 0)
  have hg1 : 0 < g1 := DiscreteMinkowski.gauge_pos_of_ne_zero hKb (single_ne_zero' 1)
  have hg01 : g0 ≤ g1 := by rw [h1, h2]; exact lam2_one_le_two hKb
  set a := 2 / g0 with hadef
  set b := 2 / g1 with hbdef
  have ha : 0 < a := by positivity
  have hb : 0 < b := by positivity
  have hba : b ≤ a := div_le_div_of_nonneg_left (by norm_num) hg0 hg01
  have hKbd : Bornology.IsBounded K := hKc.isBounded
  have hKa : pt a 0 ∈ K := by
    have := axis_point_mem hKc hKb hK 0; rwa [smul_single_zero'] at this
  have hKb' : pt 0 b ∈ K := by
    have := axis_point_mem hKc hKb hK 1; rwa [smul_single_one'] at this
  have hKle : ∀ {s t}, 0 ≤ s → s ≤ a → 0 ≤ t → t ≤ 0 → pt s t ∈ K := by
    intro s t hs0 hsa ht0 ht
    refine hK.2 _ hKa _ (fun i => ?_) (fun i => ?_) <;> fin_cases i <;> simp <;> linarith
  have hK0 : pt 0 0 ∈ K := hKle le_rfl ha.le le_rfl le_rfl
  have hbox : ∀ x ∈ K, 0 ≤ x 0 ∧ x 0 ≤ a ∧ 0 ≤ x 1 ∧ x 1 ≤ b := fun x hx =>
    ⟨hK.1 x hx 0, coord_le_two_div_axisGauge hKb hK hx 0, hK.1 x hx 1,
      coord_le_two_div_axisGauge hKb hK hx 1⟩
  -- `B_1 = sh_{-e_2,D}(K)`
  set B1 := diagShaking 1 K with hB1def
  have hB1c : IsCompact B1 := isCompact_diagShaking 1 hKc
  have hB1v : Convex ℝ B1 := convex_diagShaking 1 hKc hKb.2.1
  have hB1vol : volume B1 = volume K := volume_diagShaking 1 hKc hKb.2.1
  have hB1b : DiscreteMinkowski.IsPaperConvexBody B1 :=
    isPaperConvexBody_of hB1c hB1v (hB1vol ▸ volume_pos_of_isPaperConvexBody hKb)
  have hB1pos : ∀ y ∈ B1, 0 ≤ y 0 := by
    intro y hy
    obtain ⟨x, hx, s, -, -, rfl⟩ := mem_diagShaking_one hy
    simpa using (hbox x hx).1
  have hB1sum : ∀ y ∈ B1, y 0 + y 1 ≤ 0 := fun y hy => diagShaking_one_sum_le hy
  have hB1axis : ∀ c, 0 ≤ c → c ≤ b → pt 0 (-c) ∈ B1 := by
    intro c hc0 hcb
    have := pt_mem_diagShaking_one (S := K) hKbd (c := 0) (t₁ := -b) (t₂ := 0) (s := c)
      (by simpa using hKb') (by simpa using hK0) hc0 (by linarith)
    simpa using this
  have hB1diag : ∀ c, 0 ≤ c → c ≤ a → pt c (-c) ∈ B1 := by
    intro c hc0 hca
    have hc : pt c 0 ∈ K := hKle hc0 hca le_rfl le_rfl
    have := pt_mem_diagShaking_one (S := K) hKbd (c := c) (t₁ := -c) (t₂ := -c) (s := 0)
      (by simpa using hc) (by simpa using hc) le_rfl (by simp)
    simpa using this
  -- `B_2 = sh_{-e_1,D}(B_1)`
  set B2 := diagShaking 0 B1 with hB2def
  have hB2c : IsCompact B2 := isCompact_diagShaking 0 hB1c
  have hB2v : Convex ℝ B2 := convex_diagShaking 0 hB1c hB1v
  have hB2vol : volume B2 = volume K := (volume_diagShaking 0 hB1c hB1v).trans hB1vol
  have hB2b : DiscreteMinkowski.IsPaperConvexBody B2 :=
    isPaperConvexBody_of hB2c hB2v (hB2vol ▸ volume_pos_of_isPaperConvexBody hKb)
  have hB2pos : ∀ w ∈ B2, 0 ≤ w 0 := by
    intro w hw
    obtain ⟨x, hx, s, hs0, hs, rfl⟩ := mem_diagShaking_zero hw
    have hx0 := hB1pos x hx
    have hxs := hB1sum x hx
    have hlen : dirLength B1 (negAxis 0) (pt (-x 1) (x 1)) ≤ -x 1 := by
      unfold dirLength
      rw [dirFibre_negAxis_zero]
      refine sSup_sub_sInf_le (m := 0) (by linarith) fun t ht => ?_
      have h1' := hB1pos _ ht
      have h2' := hB1sum _ ht
      simp at h1' h2'
      constructor <;> linarith
    simp; linarith
  have hB2sum : ∀ w ∈ B2, w 0 + w 1 ≤ 0 := fun w hw => diagShaking_zero_sum_le hw
  have hB2axis : ∀ c, 0 ≤ c → c ≤ b → pt 0 (-c) ∈ B2 := by
    intro c hc0 hcb
    have := pt_mem_diagShaking_zero hB1c.isBounded (c := -c) (t₁ := 0) (t₂ := c) (s := c)
      (by simpa using hB1diag c hc0 (hcb.trans hba)) (by simpa using hB1axis c hc0 hcb) hc0
      (by linarith)
    simpa using this
  have hB2corner : pt a (-a) ∈ B2 := by
    have := pt_mem_diagShaking_zero hB1c.isBounded (c := -a) (t₁ := 0) (t₂ := 0) (s := 0)
      (by simpa using hB1diag a ha.le le_rfl) (by simpa using hB1diag a ha.le le_rfl) le_rfl
      (by simp)
    simpa using this
  -- the lowest point of `B_2`, at height `-Y`
  obtain ⟨wst, hwst, hmin⟩ :=
    hB2c.exists_isMinOn ⟨_, hB2corner⟩ (continuous_apply 1).continuousOn
  set Y := -wst 1 with hYdef
  have hY : ∀ w ∈ B2, -Y ≤ w 1 := fun w hw => by
    have := hmin hw; simp only [mem_setOf_eq] at this; rw [hYdef, neg_neg]; exact this
  have hYa : a ≤ Y := by have := hY _ hB2corner; simp at this; linarith
  have hYpos : 0 < Y := ha.trans_le hYa
  have hB2low : pt Y (-Y) ∈ B2 := by
    obtain ⟨x, hx, s, -, -, hw⟩ := mem_diagShaking_zero hwst
    have hx1 : x 1 = -Y := by
      have := congrFun hw 1; simp at this; rw [hYdef, this, neg_neg]
    have hxe : pt (-x 1 - (-x 1 - x 0)) (x 1) = x := by
      rw [show -x 1 - (-x 1 - x 0) = x 0 by ring]; exact pt_eta x
    have := pt_mem_diagShaking_zero hB1c.isBounded (c := x 1) (t₁ := -x 1 - x 0)
      (t₂ := -x 1 - x 0) (s := 0) (by rw [hxe]; exact hx) (by rw [hxe]; exact hx) le_rfl (by simp)
    rw [hx1] at this; simpa using this
  -- `A = sh_{e_2}(B_2)`
  set A := coordShaking B2 1 with hAdef
  have hAeq : planarReduction K = A := rfl
  rw [hAeq]
  have hAc : IsCompact A := isCompact_coordShaking hB2c 1
  have hAv : Convex ℝ A := convex_coordShaking hB2c hB2v 1
  have hAvol : volume A = volume K := (volume_coordShaking hB2c hB2v 1).trans hB2vol
  have hAb : DiscreteMinkowski.IsPaperConvexBody A :=
    isPaperConvexBody_of hAc hAv (hAvol ▸ volume_pos_of_isPaperConvexBody hKb)
  have hApos : ∀ z ∈ A, 0 ≤ z 0 := by
    rintro z ⟨⟨t, ht⟩, -, -⟩
    have := hB2pos _ ht
    simpa [Function.update_apply] using this
  have hAsum : ∀ z ∈ A, z 0 + z 1 ≤ Y := by
    rintro z ⟨⟨t, ht⟩, -, hz1⟩
    have hsub : fibre B2 1 z ⊆ Icc (-Y) (-Y + (Y - z 0)) := by
      intro r hr
      have h1' := hY _ hr
      have h2' := hB2sum _ hr
      simp at h1' h2'
      constructor <;> linarith
    have hβ : 0 ≤ Y - z 0 := by
      have := hsub ht; simp at this; linarith
    have := sSup_sub_sInf_le hβ hsub
    unfold fibreLength at hz1
    linarith
  have hAcorner : pt Y 0 ∈ A := by
    have := update_zero_mem_coordShaking hB2c 1 hB2low
    rwa [update_pt_one] at this
  have hAaxis : ∀ y, 0 ≤ y → y ≤ b → pt 0 y ∈ A := by
    intro y hy0 hyb
    have hf0 : (0 : ℝ) ∈ fibre B2 1 (pt 0 y) := by
      show Function.update (pt 0 y) 1 0 ∈ B2
      rw [update_pt_one]; simpa using hB2axis 0 le_rfl hb.le
    have hfb : (-b) ∈ fibre B2 1 (pt 0 y) := by
      show Function.update (pt 0 y) 1 (-b) ∈ B2
      rw [update_pt_one]; exact hB2axis b hb.le le_rfl
    refine ⟨⟨0, hf0⟩, by simpa using hy0, ?_⟩
    have := sub_le_fibreLength hB2c hfb hf0
    simp; linarith
  -- the paper's box `B` and `A ⊆ T(B)`: every vertical chord of `A` is at most `b` long
  have hAtop : ∀ z ∈ A, z 1 ≤ b := by
    set Bx : Set (Fin 2 → ℝ) := Icc (pt 0 0) (pt a b) with hBxdef
    have hBxc : IsCompact Bx := isCompact_Icc
    have hKB : K ⊆ Bx := by
      intro x hx
      obtain ⟨h0', h1', h2', h3'⟩ := hbox x hx
      refine ⟨fun i => ?_, fun i => ?_⟩ <;> fin_cases i <;> simpa
    have hBxchord : ∀ c, dirLength Bx (negAxis 1) (pt c (-c)) ≤ b := by
      intro c
      unfold dirLength
      rw [dirFibre_negAxis_one]
      refine sSup_sub_sInf_le (m := -c - b) hb.le fun t ht => ?_
      have h0' := ht.1 1
      have h1' := ht.2 1
      simp at h0' h1'
      constructor <;> linarith
    set C1 := diagShaking 1 Bx
    have hC1c : IsCompact C1 := isCompact_diagShaking 1 hBxc
    have hC1 : ∀ y ∈ C1, -b ≤ y 0 + y 1 ∧ y 0 + y 1 ≤ 0 := fun y hy =>
      ⟨diagShaking_one_sum_ge hBxchord hy, diagShaking_one_sum_le hy⟩
    set C2 := diagShaking 0 C1
    have hC2c : IsCompact C2 := isCompact_diagShaking 0 hC1c
    have hC2 : ∀ y ∈ C2, -b ≤ y 0 + y 1 ∧ y 0 + y 1 ≤ 0 := fun y hy =>
      ⟨diagShaking_zero_sum_ge (dirLength_zero_le_of_strip hb.le hC1) hy,
        diagShaking_zero_sum_le hy⟩
    have hB1C1 : B1 ⊆ C1 := lemma_5_3 hBxc.isBounded hKB (dot2_diagNormal_negAxis_ne 1)
    have hB2C2 : B2 ⊆ C2 := lemma_5_3 hC1c.isBounded hB1C1 (dot2_diagNormal_negAxis_ne 0)
    have hAT : A ⊆ coordShaking C2 1 := coordShaking_mono hC2c hB2C2 1
    intro z hz
    obtain ⟨-, -, hz1⟩ := hAT hz
    exact hz1.trans (fibreLength_one_le_of_strip hb.le hC2 z)
  -- ii) anti-blocking
  have hAab : IsAntiBlocking A := by
    refine ⟨fun z hz i => ?_, fun z hz w hw0 hwz => ?_⟩
    · fin_cases i
      · exact hApos z hz
      · exact hz.2.1
    · have hzA := hz
      obtain ⟨hne, hz0, hz1⟩ := hz
      have hq : pt (z 0) (w 1) ∈ A := by
        refine ⟨?_, by simpa using hw0 1, ?_⟩
        · rw [← update_pt_one (z 0) (z 1) (w 1), pt_eta, fibre_update]; exact hne
        · rw [← update_pt_one (z 0) (z 1) (w 1), pt_eta, fibreLength_update]
          simpa using (hwz 1).trans hz1
      have hq0 : Function.update (pt (z 0) (w 1)) 0 0 ∈ A := by
        rw [update_pt_zero]
        exact hAaxis _ (hw0 1) ((hwz 1).trans (hAtop z hzA))
      have := update_mem_of_le hAv hq hq0 (hw0 0) (by simpa using hwz 0)
      rwa [update_pt_zero, pt_eta] at this
  -- the axis gauges and minima of `A`
  have hgA0 : axisGauge A 0 = 2 / Y :=
    axisGauge_eq_of_extent hAc hAb hAab (by rw [smul_single_zero']; exact hAcorner)
      fun z hz => by linarith [hAsum z hz, hz.2.1]
  have hgA1 : axisGauge A 1 = 2 / b :=
    axisGauge_eq_of_extent hAc hAb hAab (by rw [smul_single_one']; exact hAaxis b hb.le le_rfl)
      hAtop
  have hgle : axisGauge A 0 ≤ axisGauge A 1 := by
    rw [hgA0, hgA1]; exact div_le_div_of_nonneg_left (by norm_num) hb (hba.trans hYa)
  obtain ⟨hlA1, hlA2⟩ := lam2_eq_axisGauge hAc hAb hAab hgle
  refine ⟨hAc, hAb, hAab, hAvol, ?_, ?_, ?_, ?_, ?_, hlA1.symm, hlA2.symm⟩
  · exact (ncard_latticePoints_le_diagShaking 1 hKc).trans
      ((ncard_latticePoints_le_diagShaking 0 hB1c).trans
        (ncard_latticePoints_le_coordShaking hB2c 1))
  · exact (ncard_latticePoints_interior_coordShaking_le hB2c hB2v hB2b.2.2 1).trans
      ((ncard_latticePoints_interior_diagShaking_le 0 hB1c hB1v hB1b.2.2).trans
        (ncard_latticePoints_interior_diagShaking_le 1 hKc hKb.2.1 hKb.2.2))
  · rw [hlA1, hgA0, ← h1]
    rw [div_le_iff₀ hYpos]
    have : g0 * a = 2 := by rw [hadef]; field_simp
    nlinarith
  · rw [hlA2, hgA1, ← h2]
    rw [hbdef]; field_simp
  · intro x hx
    rw [hlA1, hgA0, div_div_cancel₀ two_ne_zero]
    exact hAsum x hx

end

end LatticeVolumeInterpolation
