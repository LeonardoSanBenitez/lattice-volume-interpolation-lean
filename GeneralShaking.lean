import TheoremThreeOne

/-!
# The general planar shaking `sh_{u,ℓ}` and Lemma 5.3

Catalog items `general_blaschke_shaking` (Sec. 5, the display defining `sh_{u,ℓ}`) and
`lemma_5_3_shaking_is_monotone` (Lemma 5.3).

For an affine line `ℓ = {x ∈ ℝ^2 : ⟨ν, x⟩ = c}` and a direction `u` not parallel to it
(`⟨ν, u⟩ ≠ 0`), `π_{u,ℓ}` is the projection onto `ℓ` along `u`,

  `π_{u,ℓ}(x) = x - ((⟨ν, x⟩ - c) / ⟨ν, u⟩) u`,

and the paper defines

  `sh_{u,ℓ}(K) = ⋃_{x ∈ π_{u,ℓ}(K)} [x, x + vol_1(K ∩ (x + ℝu)) u/|u|]`.

Here `|u|` is the Euclidean length, and `vol_1(K ∩ (x + ℝu))` is the length of the chord of `K`
on the line `x + ℝu`, written as `sup - inf` of the parameters `t` with `x + t u/|u| ∈ K`, the
same convention as the coordinate shaking of Sec. 3 (`fibreLength`). For a compact convex `K`
the chord is the segment between those two parameters, so this is its Euclidean length.
-/

open Set Module MeasureTheory
open scoped Pointwise

namespace LatticeVolumeInterpolation

noncomputable section

/-- The inner product `⟨ν, x⟩` in the plane. -/
def dot2 (ν x : Fin 2 → ℝ) : ℝ := ν 0 * x 0 + ν 1 * x 1

/-- The Euclidean length `|u|`. -/
def eucLen (u : Fin 2 → ℝ) : ℝ := Real.sqrt (u 0 ^ 2 + u 1 ^ 2)

/-- The unit vector `u/|u|`. -/
def unitDir (u : Fin 2 → ℝ) : Fin 2 → ℝ := (eucLen u)⁻¹ • u

/-- The projection `π_{u,ℓ}` onto `ℓ = {⟨ν, ·⟩ = c}` along `u`. -/
def obliqueProj (ν : Fin 2 → ℝ) (c : ℝ) (u x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  x - ((dot2 ν x - c) / dot2 ν u) • u

/-- The parameters of the chord of `K` on the line through `x` in direction `u/|u|`. -/
def dirFibre (K : Set (Fin 2 → ℝ)) (u x : Fin 2 → ℝ) : Set ℝ :=
  {t | x + t • unitDir u ∈ K}

/-- `vol_1(K ∩ (x + ℝu))`. -/
def dirLength (K : Set (Fin 2 → ℝ)) (u x : Fin 2 → ℝ) : ℝ :=
  sSup (dirFibre K u x) - sInf (dirFibre K u x)

/-- **The Blaschke shaking `sh_{u,ℓ}(K)` of Sec. 5**, for `ℓ = {⟨ν, ·⟩ = c}`. -/
def generalShaking (K : Set (Fin 2 → ℝ)) (ν : Fin 2 → ℝ) (c : ℝ) (u : Fin 2 → ℝ) :
    Set (Fin 2 → ℝ) :=
  {y | ∃ p ∈ obliqueProj ν c u '' K, ∃ s ∈ Icc 0 (dirLength K u p), y = p + s • unitDir u}

theorem dot2_add (ν x y : Fin 2 → ℝ) : dot2 ν (x + y) = dot2 ν x + dot2 ν y := by
  simp only [dot2, Pi.add_apply]; ring

theorem dot2_smul (ν x : Fin 2 → ℝ) (r : ℝ) : dot2 ν (r • x) = r * dot2 ν x := by
  simp only [dot2, Pi.smul_apply, smul_eq_mul]; ring

theorem dot2_sub (ν x y : Fin 2 → ℝ) : dot2 ν (x - y) = dot2 ν x - dot2 ν y := by
  simp only [dot2, Pi.sub_apply]; ring

theorem ne_zero_of_dot2_ne_zero {ν u : Fin 2 → ℝ} (h : dot2 ν u ≠ 0) : u ≠ 0 := by
  rintro rfl; simp [dot2] at h

theorem eucLen_pos {u : Fin 2 → ℝ} (hu : u ≠ 0) : 0 < eucLen u := by
  unfold eucLen
  apply Real.sqrt_pos.2
  by_contra h
  push Not at h
  have h0 : u 0 = 0 := by nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
  have h1 : u 1 = 0 := by nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
  apply hu
  funext i; fin_cases i <;> simp [h0, h1]

/-- The projection lands on `ℓ`. -/
theorem dot2_obliqueProj {ν : Fin 2 → ℝ} {c : ℝ} {u : Fin 2 → ℝ} (h : dot2 ν u ≠ 0)
    (x : Fin 2 → ℝ) : dot2 ν (obliqueProj ν c u x) = c := by
  unfold obliqueProj
  rw [dot2_sub, dot2_smul]
  field_simp
  ring

/-- Every point is its projection moved along `u/|u|`. -/
theorem obliqueProj_add_smul_unitDir {ν : Fin 2 → ℝ} {c : ℝ} {u : Fin 2 → ℝ}
    (h : dot2 ν u ≠ 0) (x : Fin 2 → ℝ) :
    obliqueProj ν c u x + ((dot2 ν x - c) / dot2 ν u * eucLen u) • unitDir u = x := by
  have hl : eucLen u ≠ 0 := (eucLen_pos (ne_zero_of_dot2_ne_zero h)).ne'
  unfold obliqueProj unitDir
  rw [smul_smul, mul_assoc, mul_inv_cancel₀ hl, mul_one]
  abel

/-- Moving along `u` does not change the projection. -/
theorem obliqueProj_add_smul {ν : Fin 2 → ℝ} {c : ℝ} {u : Fin 2 → ℝ} (h : dot2 ν u ≠ 0)
    (x : Fin 2 → ℝ) (t : ℝ) : obliqueProj ν c u (x + t • u) = obliqueProj ν c u x := by
  unfold obliqueProj
  rw [dot2_add, dot2_smul]
  have : (dot2 ν x + t * dot2 ν u - c) / dot2 ν u = (dot2 ν x - c) / dot2 ν u + t := by
    field_simp; ring
  rw [this, add_smul]
  abel

/-- A chord of a bounded set has bounded parameters. -/
theorem dirFibre_bdd {L : Set (Fin 2 → ℝ)} (hL : Bornology.IsBounded L) {u : Fin 2 → ℝ}
    (hu : u ≠ 0) (x : Fin 2 → ℝ) :
    BddAbove (dirFibre L u x) ∧ BddBelow (dirFibre L u x) := by
  obtain ⟨R, hR⟩ := hL.exists_norm_le
  have hw : unitDir u ≠ 0 := by
    unfold unitDir
    exact smul_ne_zero (inv_ne_zero (eucLen_pos hu).ne') hu
  have hwpos : 0 < ‖unitDir u‖ := norm_pos_iff.2 hw
  have key : ∀ t ∈ dirFibre L u x, |t| ≤ (R + ‖x‖) / ‖unitDir u‖ := by
    intro t ht
    rw [le_div_iff₀ hwpos]
    have h1 := hR _ ht
    have h2 : ‖t • unitDir u‖ ≤ ‖x + t • unitDir u‖ + ‖x‖ := by
      have := norm_sub_le (x + t • unitDir u) x
      simpa using this
    rw [norm_smul, Real.norm_eq_abs] at h2
    linarith
  refine ⟨⟨(R + ‖x‖) / ‖unitDir u‖, fun t ht => (le_abs_self t).trans (key t ht)⟩,
    ⟨-((R + ‖x‖) / ‖unitDir u‖), fun t ht => ?_⟩⟩
  have := key t ht
  rw [abs_le] at this
  exact this.1

/-- The general planar shaking contains its projection onto the anchor line.
This is Lemma 3.2(i) in dimension two, stated for the later general shaking. -/
theorem obliqueProj_image_subset_generalShaking
    {K : Set (Fin 2 → ℝ)} (hK : IsCompact K)
    {ν : Fin 2 → ℝ} {c : ℝ} {u : Fin 2 → ℝ}
    (h : dot2 ν u ≠ 0) :
    obliqueProj ν c u '' K ⊆ generalShaking K ν c u := by
  rintro p ⟨x, hx, rfl⟩
  have hu := ne_zero_of_dot2_ne_zero h
  have hne : (dirFibre K u (obliqueProj ν c u x)).Nonempty := by
    refine ⟨(dot2 ν x - c) / dot2 ν u * eucLen u, ?_⟩
    show _ ∈ K
    rw [obliqueProj_add_smul_unitDir h]
    exact hx
  obtain ⟨habove, hbelow⟩ := dirFibre_bdd hK.isBounded hu (obliqueProj ν c u x)
  obtain ⟨t, ht⟩ := hne
  have hlen : 0 ≤ dirLength K u (obliqueProj ν c u x) := by
    unfold dirLength
    have hlo := csInf_le hbelow ht
    have hhi := le_csSup habove ht
    linarith
  exact ⟨_, ⟨x, hx, rfl⟩, 0, ⟨le_rfl, hlen⟩, by simp⟩

/-- Orthogonal shaking in a nonzero direction, with anchor `u⊥` through the origin. -/
def orthShaking (K : Set (Fin 2 → ℝ)) (u : Fin 2 → ℝ) : Set (Fin 2 → ℝ) :=
  generalShaking K u 0 u

/-- The orthogonal projection to `u⊥`, written in the paper's direction notation. -/
def orthProj (u x : Fin 2 → ℝ) : Fin 2 → ℝ := obliqueProj u 0 u x

/-- The orthogonal projection is linear in the point being projected. -/
def orthProjLin (u : Fin 2 → ℝ) : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun := orthProj u
  map_add' x y := by
    funext i; fin_cases i <;> simp [orthProj, obliqueProj, dot2, Pi.add_apply,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul] <;> ring
  map_smul' r x := by
    funext i; fin_cases i <;> simp [orthProj, obliqueProj, dot2, Pi.smul_apply,
      Pi.sub_apply, smul_eq_mul] <;> ring

theorem dot2_self_pos {u : Fin 2 → ℝ} (hu : u ≠ 0) : 0 < dot2 u u := by
  unfold dot2
  by_contra h
  push Not at h
  have h0 : u 0 = 0 := by nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
  have h1 : u 1 = 0 := by nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
  apply hu
  funext i; fin_cases i <;> simp [h0, h1]

/-- **Lemma 3.2(i), planar general direction:** `K|u⊥ ⊆ sh_u(K)`. -/
theorem orthProj_image_subset_orthShaking {K : Set (Fin 2 → ℝ)}
    (hK : IsCompact K) {u : Fin 2 → ℝ} (hu : u ≠ 0) :
    orthProj u '' K ⊆ orthShaking K u :=
  obliqueProj_image_subset_generalShaking hK (dot2_self_pos hu).ne'

/-- **Lemma 5.3.** The general planar shaking is monotone under inclusion. -/
theorem lemma_5_3 {K L : Set (Fin 2 → ℝ)} (hL : Bornology.IsBounded L) (hKL : K ⊆ L)
    {ν : Fin 2 → ℝ} {c : ℝ} {u : Fin 2 → ℝ} (h : dot2 ν u ≠ 0) :
    generalShaking K ν c u ⊆ generalShaking L ν c u := by
  rintro y ⟨p, ⟨k, hk, rfl⟩, s, ⟨hs0, hs1⟩, rfl⟩
  refine ⟨_, ⟨k, hKL hk, rfl⟩, s, ⟨hs0, hs1.trans ?_⟩, rfl⟩
  have hu := ne_zero_of_dot2_ne_zero h
  have hne : (dirFibre K u (obliqueProj ν c u k)).Nonempty := by
    refine ⟨(dot2 ν k - c) / dot2 ν u * eucLen u, ?_⟩
    show _ ∈ K
    rw [obliqueProj_add_smul_unitDir h]
    exact hk
  have hsub : dirFibre K u (obliqueProj ν c u k) ⊆ dirFibre L u (obliqueProj ν c u k) :=
    fun t ht => hKL ht
  obtain ⟨hA, hB⟩ := dirFibre_bdd hL hu (obliqueProj ν c u k)
  unfold dirLength
  have := csSup_le_csSup hA hne hsub
  have := csInf_le_csInf hB hne hsub
  linarith

theorem vec2_ext {x y : Fin 2 → ℝ} (h0 : x 0 = y 0) (h1 : x 1 = y 1) : x = y := by
  funext i; fin_cases i <;> assumption

/-! ### A unimodular chart turning `sh_{u,ℓ}` into the shaking along `e_2`

With `w = u/|u|` and `d = ⟨ν, w⟩ ≠ 0`, the affine map
`Φ(x) = (w_1 x_0 - w_0 x_1, (⟨ν, x⟩ - c)/d)` has determinant `1`, sends `x + t w` to
`Φ(x) + t e_2` and `ℓ` onto the axis `x_1 = 0`. Hence `Φ(sh_{u,ℓ}(K)) = sh_{e_2}(Φ(K))`. -/

section Chart

variable (ν : Fin 2 → ℝ) (c : ℝ) (u : Fin 2 → ℝ)

/-- The linear part of the chart. -/
def chartLin (hd : dot2 ν (unitDir u) ≠ 0) : (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ) where
  toFun x := ![unitDir u 1 * x 0 - unitDir u 0 * x 1, dot2 ν x / dot2 ν (unitDir u)]
  invFun z := ![ν 1 * z 0 / dot2 ν (unitDir u) + unitDir u 0 * z 1,
    -(ν 0 * z 0) / dot2 ν (unitDir u) + unitDir u 1 * z 1]
  map_add' x y := by
    funext i; fin_cases i <;> simp [dot2] <;> ring
  map_smul' r x := by
    funext i; fin_cases i <;> simp [dot2] <;> ring
  left_inv x := by
    simp only [dot2] at hd
    refine vec2_ext ?_ ?_ <;> simp only [dot2, Matrix.cons_val_zero, Matrix.cons_val_one]
    · linear_combination x 0 * mul_inv_cancel₀ hd
    · linear_combination x 1 * mul_inv_cancel₀ hd
  right_inv z := by
    simp only [dot2] at hd
    refine vec2_ext ?_ ?_ <;> simp only [dot2, Matrix.cons_val_zero, Matrix.cons_val_one]
    · linear_combination z 0 * mul_inv_cancel₀ hd
    · linear_combination z 1 * mul_inv_cancel₀ hd

/-- The chart `Φ`. -/
def shakeChart (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![unitDir u 1 * x 0 - unitDir u 0 * x 1, (dot2 ν x - c) / dot2 ν (unitDir u)]

/-- Its inverse. -/
def shakeChartInv (z : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![ν 1 * z 0 / dot2 ν (unitDir u) + unitDir u 0 * (z 1 + c / dot2 ν (unitDir u)),
    -(ν 0 * z 0) / dot2 ν (unitDir u) + unitDir u 1 * (z 1 + c / dot2 ν (unitDir u))]

variable {ν c u}

theorem shakeChart_eq (hd : dot2 ν (unitDir u) ≠ 0) (x : Fin 2 → ℝ) :
    shakeChart ν c u x = chartLin ν u hd x + ![0, -(c / dot2 ν (unitDir u))] := by
  funext i
  fin_cases i <;> simp [shakeChart, chartLin]; ring

theorem shakeChartInv_shakeChart (hd : dot2 ν (unitDir u) ≠ 0) (x : Fin 2 → ℝ) :
    shakeChartInv ν c u (shakeChart ν c u x) = x := by
  simp only [dot2] at hd
  refine vec2_ext ?_ ?_ <;> simp only [shakeChartInv, shakeChart, dot2, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  · linear_combination x 0 * mul_inv_cancel₀ hd
  · linear_combination x 1 * mul_inv_cancel₀ hd

theorem shakeChart_shakeChartInv (hd : dot2 ν (unitDir u) ≠ 0) (z : Fin 2 → ℝ) :
    shakeChart ν c u (shakeChartInv ν c u z) = z := by
  simp only [dot2] at hd
  refine vec2_ext ?_ ?_ <;> simp only [shakeChartInv, shakeChart, dot2, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  · linear_combination z 0 * mul_inv_cancel₀ hd
  · linear_combination (z 1 + c * (ν 0 * unitDir u 0 + ν 1 * unitDir u 1)⁻¹) *
      mul_inv_cancel₀ hd

theorem shakeChart_injective (hd : dot2 ν (unitDir u) ≠ 0) :
    Function.Injective (shakeChart ν c u) := fun x y h => by
  rw [← shakeChartInv_shakeChart hd x, h, shakeChartInv_shakeChart hd y]

/-- `Φ(x + t w) = Φ(x) + t e_2`. -/
theorem shakeChart_add_smul (hd : dot2 ν (unitDir u) ≠ 0) (x : Fin 2 → ℝ) (t : ℝ) :
    shakeChart ν c u (x + t • unitDir u) =
      Function.update (shakeChart ν c u x) 1 (shakeChart ν c u x 1 + t) := by
  funext i
  fin_cases i
  · simp [shakeChart]; ring
  · simp only [shakeChart, dot2] at hd ⊢
    simp
    field_simp
    ring

theorem dot2_unitDir (u ν : Fin 2 → ℝ) : dot2 ν (unitDir u) = (eucLen u)⁻¹ * dot2 ν u := by
  unfold unitDir; rw [dot2_smul]

theorem dot2_unitDir_ne_zero (h : dot2 ν u ≠ 0) : dot2 ν (unitDir u) ≠ 0 := by
  rw [dot2_unitDir]
  exact mul_ne_zero (inv_ne_zero (eucLen_pos (ne_zero_of_dot2_ne_zero h)).ne') h

theorem shakeChart_one_eq_zero_iff (hd : dot2 ν (unitDir u) ≠ 0) (x : Fin 2 → ℝ) :
    shakeChart ν c u x 1 = 0 ↔ dot2 ν x = c := by
  simp only [shakeChart, Matrix.cons_val_one, Matrix.cons_val_zero]
  rw [div_eq_zero_iff, sub_eq_zero]
  simp [hd]

/-- On `ℓ`, the fibre of `Φ(K)` along `e_2` is the chord of `K` along `u`. -/
theorem fibre_image_shakeChart (hd : dot2 ν (unitDir u) ≠ 0) (K : Set (Fin 2 → ℝ))
    {p : Fin 2 → ℝ} (hp : dot2 ν p = c) :
    fibre (shakeChart ν c u '' K) 1 (shakeChart ν c u p) = dirFibre K u p := by
  have h0 : shakeChart ν c u p 1 = 0 := (shakeChart_one_eq_zero_iff hd p).2 hp
  ext t
  simp only [fibre, dirFibre, mem_setOf_eq]
  have : Function.update (shakeChart ν c u p) 1 t = shakeChart ν c u (p + t • unitDir u) := by
    rw [shakeChart_add_smul hd, h0, zero_add]
  rw [this, (shakeChart_injective hd).mem_set_image]

theorem obliqueProj_of_dot2 {p : Fin 2 → ℝ} (hp : dot2 ν p = c) :
    obliqueProj ν c u p = p := by
  simp [obliqueProj, hp]

theorem obliqueProj_add_smul_unitDir' (h : dot2 ν u ≠ 0) (x : Fin 2 → ℝ) (t : ℝ) :
    obliqueProj ν c u (x + t • unitDir u) = obliqueProj ν c u x := by
  rw [unitDir, smul_smul]
  exact obliqueProj_add_smul h x _

/-- **`Φ(sh_{u,ℓ}(K)) = sh_{e_2}(Φ(K))`.** -/
theorem image_generalShaking (h : dot2 ν u ≠ 0) (K : Set (Fin 2 → ℝ)) :
    shakeChart ν c u '' generalShaking K ν c u = coordShaking (shakeChart ν c u '' K) 1 := by
  have hd := dot2_unitDir_ne_zero h
  ext z
  constructor
  · rintro ⟨_, ⟨_, ⟨k, hk, rfl⟩, s, ⟨hs0, hs1⟩, rfl⟩, rfl⟩
    set p := obliqueProj ν c u k
    have hp : dot2 ν p = c := dot2_obliqueProj h k
    have h0 : shakeChart ν c u p 1 = 0 := (shakeChart_one_eq_zero_iff hd p).2 hp
    rw [shakeChart_add_smul hd, h0, zero_add]
    have hfib := fibre_image_shakeChart hd K hp
    refine ⟨?_, ?_, ?_⟩
    · rw [fibre_update, hfib]
      refine ⟨(dot2 ν k - c) / dot2 ν u * eucLen u, ?_⟩
      show _ ∈ K
      rw [obliqueProj_add_smul_unitDir h]
      exact hk
    · simpa using hs0
    · rw [fibreLength_update]
      simp only [Function.update_self]
      unfold fibreLength
      rw [hfib]
      exact hs1
  · rintro ⟨⟨t, ht⟩, hz0, hz1⟩
    set p := shakeChartInv ν c u (Function.update z 1 0)
    have hΦp : shakeChart ν c u p = Function.update z 1 0 := shakeChart_shakeChartInv hd _
    have hp : dot2 ν p = c := by
      rw [← shakeChart_one_eq_zero_iff hd p, hΦp]; simp
    have hfib : fibre (shakeChart ν c u '' K) 1 z = dirFibre K u p := by
      rw [← fibre_update _ 1 z 0, ← hΦp, fibre_image_shakeChart hd K hp]
    refine ⟨p + z 1 • unitDir u, ⟨p, ⟨p + t • unitDir u, ?_, ?_⟩, z 1, ⟨hz0, ?_⟩, rfl⟩, ?_⟩
    · rw [hfib] at ht; exact ht
    · rw [obliqueProj_add_smul_unitDir' h, obliqueProj_of_dot2 hp]
    · have : fibreLength (shakeChart ν c u '' K) 1 z = dirLength K u p := by
        unfold fibreLength dirLength; rw [hfib]
      rw [← this]; exact hz1
    · rw [shakeChart_add_smul hd, hΦp]
      funext i
      fin_cases i <;> simp

/-- `sh_{u,ℓ}(K) = Φ⁻¹(sh_{e_2}(Φ(K)))`. -/
theorem generalShaking_eq (h : dot2 ν u ≠ 0) (K : Set (Fin 2 → ℝ)) :
    generalShaking K ν c u =
      shakeChartInv ν c u '' coordShaking (shakeChart ν c u '' K) 1 := by
  have hd := dot2_unitDir_ne_zero h
  rw [← image_generalShaking h K, Set.image_image]
  simp [shakeChartInv_shakeChart hd]

end Chart

/-! ### Consequences: compactness, convexity and volume of `sh_{u,ℓ}(K)` -/

section Consequences

variable {ν : Fin 2 → ℝ} {c : ℝ} {u : Fin 2 → ℝ}

/-- The translation part of the chart. -/
def chartShift (ν : Fin 2 → ℝ) (c : ℝ) (u : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![0, -(c / dot2 ν (unitDir u))]

theorem shakeChartInv_eq (hd : dot2 ν (unitDir u) ≠ 0) (z : Fin 2 → ℝ) :
    shakeChartInv ν c u z = (chartLin ν u hd).symm (z - chartShift ν c u) := by
  refine vec2_ext ?_ ?_ <;>
    simp [shakeChartInv, chartLin, chartShift, Matrix.vecHead, Matrix.vecTail]

theorem image_shakeChart (hd : dot2 ν (unitDir u) ≠ 0) (S : Set (Fin 2 → ℝ)) :
    shakeChart ν c u '' S = (fun z => z + chartShift ν c u) '' (chartLin ν u hd '' S) := by
  rw [Set.image_image]
  congr 1
  funext x
  rw [shakeChart_eq hd]
  rfl

theorem image_shakeChartInv (hd : dot2 ν (unitDir u) ≠ 0) (S : Set (Fin 2 → ℝ)) :
    shakeChartInv ν c u '' S =
      (chartLin ν u hd).symm '' ((fun z => z + -chartShift ν c u) '' S) := by
  rw [Set.image_image]
  congr 1
  funext z
  rw [shakeChartInv_eq hd, sub_eq_add_neg]

theorem chartShift_zero (ν u : Fin 2 → ℝ) : chartShift ν 0 u = 0 := by
  refine vec2_ext ?_ ?_ <;> simp [chartShift]

theorem generalShaking_eq_of_zero (h : dot2 ν u ≠ 0) (K : Set (Fin 2 → ℝ)) :
    generalShaking K ν 0 u =
      (chartLin ν u (dot2_unitDir_ne_zero h)).symm ''
        coordShaking (chartLin ν u (dot2_unitDir_ne_zero h) '' K) 1 := by
  have hd := dot2_unitDir_ne_zero h
  rw [generalShaking_eq h, image_shakeChartInv hd, image_shakeChart hd, chartShift_zero]
  simp

theorem det_chartLin (hd : dot2 ν (unitDir u) ≠ 0) :
    LinearMap.det (chartLin ν u hd : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) = 1 := by
  rw [← LinearMap.det_toMatrix', Matrix.det_fin_two]
  simp only [LinearMap.toMatrix'_apply]
  simp only [dot2] at hd
  simp [chartLin, dot2]
  linear_combination mul_inv_cancel₀ hd

theorem abs_det_chartLin_symm (hd : dot2 ν (unitDir u) ≠ 0) :
    |LinearMap.det ((chartLin ν u hd).symm : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ))| = 1 := by
  rw [LinearEquiv.det_coe_symm, det_chartLin hd]; simp

theorem volume_image_add_right (S : Set (Fin 2 → ℝ)) (b : Fin 2 → ℝ) :
    volume ((fun z => z + b) '' S) = volume S := by
  rw [Set.image_add_right, measure_preimage_add_right]

theorem volume_image_shakeChart (hd : dot2 ν (unitDir u) ≠ 0) (S : Set (Fin 2 → ℝ)) :
    volume (shakeChart ν c u '' S) = volume S := by
  rw [image_shakeChart hd, volume_image_add_right,
    volume_image_of_det (chartLin ν u hd) (by rw [det_chartLin hd]; simp)]

theorem volume_image_shakeChartInv (hd : dot2 ν (unitDir u) ≠ 0) (S : Set (Fin 2 → ℝ)) :
    volume (shakeChartInv ν c u '' S) = volume S := by
  rw [image_shakeChartInv hd,
    volume_image_of_det (chartLin ν u hd).symm (abs_det_chartLin_symm hd),
    volume_image_add_right]

theorem continuous_chartLin (hd : dot2 ν (unitDir u) ≠ 0) : Continuous (chartLin ν u hd) :=
  (chartLin ν u hd).toLinearMap.continuous_of_finiteDimensional

theorem continuous_chartLin_symm (hd : dot2 ν (unitDir u) ≠ 0) :
    Continuous (chartLin ν u hd).symm :=
  (chartLin ν u hd).symm.toLinearMap.continuous_of_finiteDimensional

theorem isCompact_image_shakeChart (hd : dot2 ν (unitDir u) ≠ 0) {S : Set (Fin 2 → ℝ)}
    (hS : IsCompact S) : IsCompact (shakeChart ν c u '' S) := by
  rw [image_shakeChart hd]
  exact (hS.image (continuous_chartLin hd)).image (continuous_id.add continuous_const)

theorem isCompact_image_shakeChartInv (hd : dot2 ν (unitDir u) ≠ 0) {S : Set (Fin 2 → ℝ)}
    (hS : IsCompact S) : IsCompact (shakeChartInv ν c u '' S) := by
  rw [image_shakeChartInv hd]
  exact (hS.image (continuous_id.add continuous_const)).image (continuous_chartLin_symm hd)

theorem convex_image_add_right {S : Set (Fin 2 → ℝ)} (hS : Convex ℝ S) (b : Fin 2 → ℝ) :
    Convex ℝ ((fun z => z + b) '' S) := by
  have : (fun z => z + b) '' S = (fun z => b + z) '' S := by simp_rw [add_comm]
  rw [this]; exact hS.translate b

theorem convex_image_shakeChart (hd : dot2 ν (unitDir u) ≠ 0) {S : Set (Fin 2 → ℝ)}
    (hS : Convex ℝ S) : Convex ℝ (shakeChart ν c u '' S) := by
  rw [image_shakeChart hd]
  exact convex_image_add_right (hS.linear_image (chartLin ν u hd).toLinearMap) _

theorem convex_image_shakeChartInv (hd : dot2 ν (unitDir u) ≠ 0) {S : Set (Fin 2 → ℝ)}
    (hS : Convex ℝ S) : Convex ℝ (shakeChartInv ν c u '' S) := by
  rw [image_shakeChartInv hd]
  exact (convex_image_add_right hS _).linear_image (chartLin ν u hd).symm.toLinearMap

/-- `sh_{u,ℓ}(K)` is compact. -/
theorem isCompact_generalShaking (h : dot2 ν u ≠ 0) {K : Set (Fin 2 → ℝ)} (hK : IsCompact K) :
    IsCompact (generalShaking K ν c u) := by
  have hd := dot2_unitDir_ne_zero h
  rw [generalShaking_eq h]
  exact isCompact_image_shakeChartInv hd
    (isCompact_coordShaking (isCompact_image_shakeChart hd hK) 1)

/-- **`sh_{u,ℓ}(K)` is convex** (the general statement inside the proof of Lemma 5.1 i)). -/
theorem convex_generalShaking (h : dot2 ν u ≠ 0) {K : Set (Fin 2 → ℝ)} (hK : IsCompact K)
    (hKc : Convex ℝ K) : Convex ℝ (generalShaking K ν c u) := by
  have hd := dot2_unitDir_ne_zero h
  rw [generalShaking_eq h]
  exact convex_image_shakeChartInv hd
    (convex_coordShaking (isCompact_image_shakeChart hd hK) (convex_image_shakeChart hd hKc) 1)

/-- **`vol(sh_{u,ℓ}(K)) = vol(K)`** (the general statement behind Lemma 5.1 iii)). -/
theorem volume_generalShaking (h : dot2 ν u ≠ 0) {K : Set (Fin 2 → ℝ)} (hK : IsCompact K)
    (hKc : Convex ℝ K) : volume (generalShaking K ν c u) = volume K := by
  have hd := dot2_unitDir_ne_zero h
  rw [generalShaking_eq h, volume_image_shakeChartInv hd,
    volume_coordShaking (isCompact_image_shakeChart hd hK) (convex_image_shakeChart hd hKc) 1,
    volume_image_shakeChart hd]

/-- **Lemma 3.2(ii), planar general direction:** orthogonal shaking preserves volume. -/
theorem volume_orthShaking {K : Set (Fin 2 → ℝ)} (hK : IsCompact K)
    (hKc : Convex ℝ K) {u : Fin 2 → ℝ} (hu : u ≠ 0) :
    volume (orthShaking K u) = volume K :=
  volume_generalShaking (dot2_self_pos hu).ne' hK hKc

/-- The orthogonal chart carries `u` to a multiple of the second coordinate vector. -/
theorem chartLin_self_eq_single {u : Fin 2 → ℝ} (hu : u ≠ 0) :
    chartLin u u (dot2_unitDir_ne_zero (dot2_self_pos hu).ne') u =
      (dot2 u u / dot2 u (unitDir u)) • (Pi.single 1 (1 : ℝ) : Fin 2 → ℝ) := by
  funext i
  fin_cases i
  · simp [chartLin, unitDir, Pi.smul_apply, smul_eq_mul]; ring
  · simp [chartLin]

/-- The chart sends orthogonal shaking to ordinary coordinate shaking. -/
theorem image_orthShaking_chart {K : Set (Fin 2 → ℝ)} {u : Fin 2 → ℝ}
    (hu : u ≠ 0) :
    let V := chartLin u u (dot2_unitDir_ne_zero (dot2_self_pos hu).ne')
    V '' orthShaking K u = coordShaking (V '' K) 1 := by
  dsimp
  rw [orthShaking, generalShaking_eq_of_zero (dot2_self_pos hu).ne', Set.image_image]
  simp

/-- A coordinate shaking of a compact convex body is again a body in the paper's sense. -/
theorem paperConvexBody_coordShaking {n : ℕ} {K : Set (Fin n → ℝ)}
    (hK : IsCompact K) (hKb : DiscreteMinkowski.IsPaperConvexBody K) (j : Fin n) :
    DiscreteMinkowski.IsPaperConvexBody (coordShaking K j) := by
  have hconv := convex_coordShaking hK hKb.2.1 j
  refine ⟨(isCompact_coordShaking hK j).isBounded, hconv, ?_⟩
  apply interior_nonempty_of_volume_pos hconv
  rw [volume_coordShaking hK hKb.2.1 j]
  obtain ⟨x, hx⟩ := hKb.2.2
  exact lt_of_lt_of_le (isOpen_interior.measure_pos volume ⟨x, hx⟩)
    (measure_mono interior_subset)

/-- The reverse direction along a coordinate axis: a shaken fibre has its old length. -/
theorem gauge_coordShaking_single_ge {n : ℕ} {K : Set (Fin n → ℝ)}
    (hK : IsCompact K) (hKb : DiscreteMinkowski.IsPaperConvexBody K) (j : Fin n) :
    gauge (DiscreteMinkowski.halfDifferenceBody K) (Pi.single j (1 : ℝ)) ≤
      gauge (DiscreteMinkowski.halfDifferenceBody (coordShaking K j))
        (Pi.single j (1 : ℝ)) := by
  refine le_of_forall_gt_imp_ge_of_dense fun r hr => ?_
  have hr0 : 0 < r := lt_of_le_of_lt (gauge_nonneg _) hr
  have hx : (Pi.single j (1 : ℝ) : Fin n → ℝ) ∈
      r • DiscreteMinkowski.halfDifferenceBody (coordShaking K j) :=
    DiscreteMinkowski.mem_smul_of_gauge_lt (paperConvexBody_coordShaking hK hKb j) hr
  obtain ⟨d, hd, hdx⟩ := mem_smul_set.1 hx
  rw [DiscreteMinkowski.halfDifferenceBody_apply] at hd
  obtain ⟨w, ⟨a, ha, b, hb, rfl⟩, rfl⟩ := mem_smul_set.1 hd
  have hcoord : ∀ i, (Pi.single j (1 : ℝ) : Fin n → ℝ) i =
      r * (2⁻¹ * (a i - b i)) := by
    intro i; rw [← hdx]; simp [smul_eq_mul]
  have hoff : ∀ i, i ≠ j → b i = a i := by
    intro i hi
    have hc := hcoord i
    rw [Pi.single_eq_of_ne hi] at hc
    have hr2 : r * 2⁻¹ ≠ 0 := by positivity
    have : r * 2⁻¹ * (a i - b i) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hr2
    · linarith
  have hon : a j - b j = 2 / r := by
    have hc := hcoord j
    rw [Pi.single_eq_same] at hc
    field_simp at hc ⊢
    linarith
  have hlen : 2 / r ≤ fibreLength K j a := by
    have := ha.2.2
    have := hb.2.1
    linarith
  have hne : (fibre K j a).Nonempty := ha.1
  have hcompact := isCompact_fibre hK j a
  have hlo : sInf (fibre K j a) ∈ fibre K j a := hcompact.sInf_mem hne
  have hhi : sInf (fibre K j a) + 2 / r ∈ fibre K j a := by
    have hmemIcc : sInf (fibre K j a) + 2 / r ∈
        Icc (sInf (fibre K j a)) (sSup (fibre K j a)) := by
      have hdiv : 0 ≤ 2 / r := by positivity
      refine ⟨by linarith, ?_⟩
      unfold fibreLength at hlen
      linarith
    exact (congrArg (fun S : Set ℝ => sInf (fibre K j a) + 2 / r ∈ S)
      (fibre_eq_Icc hK hKb.2.1 hne).symm).mp hmemIcc
  have hq : Function.update a j (sInf (fibre K j a)) ∈ K := hlo
  have hp : Function.update a j (sInf (fibre K j a) + 2 / r) ∈ K := hhi
  have hrep : (Pi.single j (1 : ℝ) : Fin n → ℝ) =
      r • ((2 : ℝ)⁻¹ • (Function.update a j (sInf (fibre K j a) + 2 / r) -
        Function.update a j (sInf (fibre K j a)))) := by
    funext i
    by_cases h : i = j
    · subst h; simp; field_simp
    · simp [Function.update_of_ne h, Pi.single_eq_of_ne h]
  have hmem : (Pi.single j (1 : ℝ) : Fin n → ℝ) ∈
      r • DiscreteMinkowski.halfDifferenceBody K := by
    rw [hrep, DiscreteMinkowski.halfDifferenceBody_apply]
    exact smul_mem_smul_set (smul_mem_smul_set (sub_mem_sub hp hq))
  exact DiscreteMinkowski.gauge_le_of_mem_smul hr0.le hmem

theorem gauge_coordShaking_smul_single_ge {n : ℕ} {K : Set (Fin n → ℝ)}
    (hK : IsCompact K) (hKb : DiscreteMinkowski.IsPaperConvexBody K)
    (j : Fin n) (c : ℝ) :
    gauge (DiscreteMinkowski.halfDifferenceBody K)
        (c • (Pi.single j (1 : ℝ) : Fin n → ℝ)) ≤
      gauge (DiscreteMinkowski.halfDifferenceBody (coordShaking K j))
        (c • (Pi.single j (1 : ℝ) : Fin n → ℝ)) := by
  rw [gauge_halfDifferenceBody_smul, gauge_halfDifferenceBody_smul]
  exact mul_le_mul_of_nonneg_left (gauge_coordShaking_single_ge hK hKb j) (abs_nonneg c)

/-- **Lemma 3.2(iii)** on a coordinate axis: shaking preserves its gauge exactly. -/
theorem gauge_coordShaking_smul_single_eq {n : ℕ} {K : Set (Fin n → ℝ)}
    (hK : IsCompact K) (hKb : DiscreteMinkowski.IsPaperConvexBody K)
    (j : Fin n) (c : ℝ) :
    gauge (DiscreteMinkowski.halfDifferenceBody (coordShaking K j))
        (c • (Pi.single j (1 : ℝ) : Fin n → ℝ)) =
      gauge (DiscreteMinkowski.halfDifferenceBody K)
        (c • (Pi.single j (1 : ℝ) : Fin n → ℝ)) :=
  le_antisymm (gauge_coordShaking_smul_single_le hK hKb j c)
    (gauge_coordShaking_smul_single_ge hK hKb j c)

/-- The `≤` direction of Lemma 3.2(iii), transferred from the fibre argument for `e₂`. -/
theorem gauge_orthShaking_direction_le {K : Set (Fin 2 → ℝ)}
    (hK : IsCompact K) (hKb : DiscreteMinkowski.IsPaperConvexBody K)
    {u : Fin 2 → ℝ} (hu : u ≠ 0) :
    gauge (DiscreteMinkowski.halfDifferenceBody (orthShaking K u)) u ≤
      gauge (DiscreteMinkowski.halfDifferenceBody K) u := by
  let V := chartLin u u (dot2_unitDir_ne_zero (dot2_self_pos hu).ne')
  let c := dot2 u u / dot2 u (unitDir u)
  have hVu : V u = c • (Pi.single 1 (1 : ℝ) : Fin 2 → ℝ) :=
    chartLin_self_eq_single hu
  have hVsh : V '' orthShaking K u = coordShaking (V '' K) 1 :=
    image_orthShaking_chart hu
  have hVc : IsCompact (V '' K) := hK.image V.toLinearMap.continuous_of_finiteDimensional
  have hVb := isPaperConvexBody_image V hKb
  have hcore := gauge_coordShaking_smul_single_le hVc hVb 1 c
  rw [← hVsh, ← hVu, halfDifferenceBody_image V,
    gauge_image_apply V, halfDifferenceBody_image V, gauge_image_apply V] at hcore
  exact hcore

/-- **Lemma 3.2(iii), planar general direction:** `|u|` is unchanged by shaking along `u`. -/
theorem gauge_orthShaking_direction_eq {K : Set (Fin 2 → ℝ)}
    (hK : IsCompact K) (hKb : DiscreteMinkowski.IsPaperConvexBody K)
    {u : Fin 2 → ℝ} (hu : u ≠ 0) :
    gauge (DiscreteMinkowski.halfDifferenceBody (orthShaking K u)) u =
      gauge (DiscreteMinkowski.halfDifferenceBody K) u := by
  let V := chartLin u u (dot2_unitDir_ne_zero (dot2_self_pos hu).ne')
  let c := dot2 u u / dot2 u (unitDir u)
  have hVu : V u = c • (Pi.single 1 (1 : ℝ) : Fin 2 → ℝ) :=
    chartLin_self_eq_single hu
  have hVsh : V '' orthShaking K u = coordShaking (V '' K) 1 :=
    image_orthShaking_chart hu
  have hVc : IsCompact (V '' K) := hK.image V.toLinearMap.continuous_of_finiteDimensional
  have hVb := isPaperConvexBody_image V hKb
  have hcore := gauge_coordShaking_smul_single_eq hVc hVb 1 c
  rw [← hVsh, ← hVu, halfDifferenceBody_image V,
    gauge_image_apply V, halfDifferenceBody_image V, gauge_image_apply V] at hcore
  exact hcore

/-- **Lemma 3.2(iv), planar general direction:** the projected gauge does not increase. -/
theorem gauge_orthShaking_proj_le {K : Set (Fin 2 → ℝ)}
    (hK : IsCompact K) (hKb : DiscreteMinkowski.IsPaperConvexBody K)
    {u : Fin 2 → ℝ} (hu : u ≠ 0) (x : Fin 2 → ℝ) :
    gauge (DiscreteMinkowski.halfDifferenceBody (orthShaking K u)) (orthProj u x) ≤
      gauge (DiscreteMinkowski.halfDifferenceBody K) x := by
  refine le_of_forall_gt_imp_ge_of_dense fun r hr => ?_
  have hr0 : 0 < r := lt_of_le_of_lt (gauge_nonneg _) hr
  have hx : x ∈ r • DiscreteMinkowski.halfDifferenceBody K :=
    DiscreteMinkowski.mem_smul_of_gauge_lt hKb hr
  obtain ⟨d, hd, hdx⟩ := mem_smul_set.1 hx
  rw [DiscreteMinkowski.halfDifferenceBody_apply] at hd
  obtain ⟨w, ⟨a, ha, b, hb, rfl⟩, rfl⟩ := mem_smul_set.1 hd
  have hpa : orthProj u a ∈ orthShaking K u :=
    orthProj_image_subset_orthShaking hK hu ⟨a, ha, rfl⟩
  have hpb : orthProj u b ∈ orthShaking K u :=
    orthProj_image_subset_orthShaking hK hu ⟨b, hb, rfl⟩
  have hrep : orthProj u x =
      r • ((2 : ℝ)⁻¹ • (orthProj u a - orthProj u b)) := by
    rw [← hdx]
    exact (orthProjLin u).map_smul r ((2 : ℝ)⁻¹ • (a - b)) |>.trans (by
      rw [map_smul, map_sub]; rfl)
  have hmem : orthProj u x ∈
      r • DiscreteMinkowski.halfDifferenceBody (orthShaking K u) := by
    rw [hrep, DiscreteMinkowski.halfDifferenceBody_apply]
    exact smul_mem_smul_set (smul_mem_smul_set (sub_mem_sub hpa hpb))
  exact DiscreteMinkowski.gauge_le_of_mem_smul hr0.le hmem

end Consequences

/-! ### Lattice points, for a line through the origin with an integral chart -/

section Lattice

variable {ν u : Fin 2 → ℝ}

variable (hΛ : ∀ (hd : dot2 ν (unitDir u) ≠ 0) (x : Fin 2 → ℝ),
  chartLin ν u hd x ∈ standardIntegerLattice 2 ↔ x ∈ standardIntegerLattice 2)
include hΛ

theorem symm_mem_lattice_iff (hd : dot2 ν (unitDir u) ≠ 0) (x : Fin 2 → ℝ) :
    (chartLin ν u hd).symm x ∈ standardIntegerLattice 2 ↔ x ∈ standardIntegerLattice 2 := by
  rw [← hΛ hd, LinearEquiv.apply_symm_apply]

/-- The shaking does not decrease `G` (the transfer of Lemma 3.2 v)). -/
theorem ncard_latticePoints_le_generalShaking (h : dot2 ν u ≠ 0) {K : Set (Fin 2 → ℝ)}
    (hK : IsCompact K) :
    (DiscreteMinkowski.latticePoints K (standardIntegerLattice 2)).ncard ≤
      (DiscreteMinkowski.latticePoints (generalShaking K ν 0 u)
        (standardIntegerLattice 2)).ncard := by
  have hd := dot2_unitDir_ne_zero h
  set V := chartLin ν u hd
  rw [generalShaking_eq_of_zero h, ncard_latticePoints_image V.symm (symm_mem_lattice_iff hΛ hd),
    ← ncard_latticePoints_image V (hΛ hd) K]
  exact ncard_latticePoints_le_coordShaking (isCompact_image V hK) 1

/-- The shaking does not increase `G(int ·)` (the transfer of Lemma 3.2 vi)). -/
theorem ncard_latticePoints_interior_generalShaking_le (h : dot2 ν u ≠ 0) {K : Set (Fin 2 → ℝ)}
    (hK : IsCompact K) (hKc : Convex ℝ K) (hKi : (interior K).Nonempty) :
    (DiscreteMinkowski.latticePoints (interior (generalShaking K ν 0 u))
        (standardIntegerLattice 2)).ncard ≤
      (DiscreteMinkowski.latticePoints (interior K) (standardIntegerLattice 2)).ncard := by
  have hd := dot2_unitDir_ne_zero h
  set V := chartLin ν u hd
  rw [generalShaking_eq_of_zero h, interior_image_linearEquiv,
    ncard_latticePoints_image V.symm (symm_mem_lattice_iff hΛ hd),
    ← ncard_latticePoints_image V (hΛ hd) (interior K), ← interior_image_linearEquiv]
  refine ncard_latticePoints_interior_coordShaking_le (isCompact_image V hK)
    (hKc.linear_image V.toLinearMap) ?_ 1
  rw [interior_image_linearEquiv]
  exact hKi.image _

end Lattice

/-! ### The two shakings against the lattice diagonal `D = {x_1 + x_2 = 0}` -/

/-- The normal `(1, 1)` of the lattice diagonal `D = {x : x_1 + x_2 = 0}`. -/
def diagNormal : Fin 2 → ℝ := ![1, 1]

/-- `-e_i`. -/
def negAxis (i : Fin 2) : Fin 2 → ℝ := -Pi.single i 1

theorem eucLen_negAxis (i : Fin 2) : eucLen (negAxis i) = 1 := by
  fin_cases i <;> simp [eucLen, negAxis]

theorem unitDir_negAxis (i : Fin 2) : unitDir (negAxis i) = negAxis i := by
  simp [unitDir, eucLen_negAxis]

theorem dot2_diagNormal_negAxis (i : Fin 2) : dot2 diagNormal (negAxis i) = -1 := by
  fin_cases i <;> simp [dot2, diagNormal, negAxis]

theorem dot2_diagNormal_negAxis_ne (i : Fin 2) : dot2 diagNormal (negAxis i) ≠ 0 := by
  rw [dot2_diagNormal_negAxis]; norm_num

/-- `sh_{-e_i, D}`. -/
def diagShaking (i : Fin 2) (K : Set (Fin 2 → ℝ)) : Set (Fin 2 → ℝ) :=
  generalShaking K diagNormal 0 (negAxis i)

theorem chartLin_diag_apply (i : Fin 2) (hd : dot2 diagNormal (unitDir (negAxis i)) ≠ 0)
    (x : Fin 2 → ℝ) :
    chartLin diagNormal (negAxis i) hd x =
      if i = 0 then ![x 1, -(x 0 + x 1)] else ![-x 0, -(x 0 + x 1)] := by
  simp only [chartLin, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, unitDir_negAxis,
    dot2_diagNormal_negAxis]
  fin_cases i <;> refine vec2_ext ?_ ?_ <;> simp [negAxis, dot2, diagNormal] <;> ring

theorem chartLin_diag_mem_iff (i : Fin 2) (hd : dot2 diagNormal (unitDir (negAxis i)) ≠ 0)
    (x : Fin 2 → ℝ) :
    chartLin diagNormal (negAxis i) hd x ∈ standardIntegerLattice 2 ↔
      x ∈ standardIntegerLattice 2 := by
  rw [chartLin_diag_apply, mem_standardIntegerLattice_iff, mem_standardIntegerLattice_iff]
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte]
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨![-(z 1) - z 0, z 0], fun j => ?_⟩
      have h0 := hz 0; have h1 := hz 1
      simp at h0 h1
      fin_cases j <;> simp <;> linarith
    · rintro ⟨z, hz⟩
      refine ⟨![z 1, -(z 0 + z 1)], fun j => ?_⟩
      fin_cases j <;> simp [hz 0, hz 1]
  · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte]
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨![-(z 0), z 0 - z 1], fun j => ?_⟩
      have h0 := hz 0; have h1 := hz 1
      simp at h0 h1
      fin_cases j <;> simp <;> linarith
    · rintro ⟨z, hz⟩
      refine ⟨![-(z 0), -(z 0 + z 1)], fun j => ?_⟩
      fin_cases j <;> simp [hz 0, hz 1]

theorem isCompact_diagShaking (i : Fin 2) {K : Set (Fin 2 → ℝ)} (hK : IsCompact K) :
    IsCompact (diagShaking i K) :=
  isCompact_generalShaking (dot2_diagNormal_negAxis_ne i) hK

theorem convex_diagShaking (i : Fin 2) {K : Set (Fin 2 → ℝ)} (hK : IsCompact K)
    (hKc : Convex ℝ K) : Convex ℝ (diagShaking i K) :=
  convex_generalShaking (dot2_diagNormal_negAxis_ne i) hK hKc

theorem volume_diagShaking (i : Fin 2) {K : Set (Fin 2 → ℝ)} (hK : IsCompact K)
    (hKc : Convex ℝ K) : volume (diagShaking i K) = volume K :=
  volume_generalShaking (dot2_diagNormal_negAxis_ne i) hK hKc

theorem ncard_latticePoints_le_diagShaking (i : Fin 2) {K : Set (Fin 2 → ℝ)}
    (hK : IsCompact K) :
    (DiscreteMinkowski.latticePoints K (standardIntegerLattice 2)).ncard ≤
      (DiscreteMinkowski.latticePoints (diagShaking i K) (standardIntegerLattice 2)).ncard :=
  ncard_latticePoints_le_generalShaking (chartLin_diag_mem_iff i)
    (dot2_diagNormal_negAxis_ne i) hK

theorem ncard_latticePoints_interior_diagShaking_le (i : Fin 2) {K : Set (Fin 2 → ℝ)}
    (hK : IsCompact K) (hKc : Convex ℝ K) (hKi : (interior K).Nonempty) :
    (DiscreteMinkowski.latticePoints (interior (diagShaking i K))
        (standardIntegerLattice 2)).ncard ≤
      (DiscreteMinkowski.latticePoints (interior K) (standardIntegerLattice 2)).ncard :=
  ncard_latticePoints_interior_generalShaking_le (chartLin_diag_mem_iff i)
    (dot2_diagNormal_negAxis_ne i) hK hKc hKi

end

end LatticeVolumeInterpolation
