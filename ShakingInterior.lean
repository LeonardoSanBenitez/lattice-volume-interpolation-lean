import CoordShaking

/-!
# Lemma 3.2 vi): shaking does not increase the interior lattice point count

Catalog item `lemma_3_2_shaking_properties`, item vi), for `u = e_j`:
`G(int K) ≥ G(int sh_{e_j}(K))`.

The paper: "vi) is proved with the same argument [as v)], but since the intervals involved are
open, translating them such that they start at a lattice point will potentially reduce, but
never increase, their lattice point count." Here: a lattice point `z` of `int sh(K)` has
`0 < z_j < l(z)`, and moving it up its line by the integer `⌊inf F(z)⌋` lands strictly inside
the fibre `(inf F, sup F)` of `K`. That such a point is interior to `K` is the one step the
paper leaves implicit; it is proved by finding one interior point of `K` on the line
(`exists_interior_on_line`) and using that an open segment from an interior point to a point
of `K` stays in the interior.
-/

open Set Module Metric
open scoped Pointwise

namespace LatticeVolumeInterpolation

noncomputable section

variable {n : ℕ}

theorem norm_smul_single (j : Fin n) (c : ℝ) : ‖c • (Pi.single j (1 : ℝ) : Fin n → ℝ)‖ = |c| := by
  rw [norm_smul, Real.norm_eq_abs]
  have : ‖(Pi.single j (1 : ℝ) : Fin n → ℝ)‖ = 1 := by
    rw [Pi.norm_single, norm_one]
  rw [this, mul_one]

theorem update_eq_add_smul_single (z : Fin n → ℝ) (j : Fin n) (s : ℝ) :
    Function.update z j s = z + (s - z j) • (Pi.single j (1 : ℝ) : Fin n → ℝ) := by
  funext i
  by_cases h : i = j
  · subst h; simp
  · simp [Function.update_of_ne h, Pi.single_eq_of_ne h]

/-- A point interior to the shaking lies strictly inside its fibre: `0 < z_j < l(z)`. -/
theorem lt_of_mem_interior_coordShaking {K : Set (Fin n → ℝ)} {j : Fin n} {z : Fin n → ℝ}
    (hz : z ∈ interior (coordShaking K j)) :
    0 < z j ∧ z j < fibreLength K j z := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hz)
  have hmem : ∀ c : ℝ, |c| < δ →
      z + c • (Pi.single j (1 : ℝ) : Fin n → ℝ) ∈ coordShaking K j := by
    intro c hc
    apply hball
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul_single]
    exact hc
  have hj : ∀ c : ℝ, (z + c • (Pi.single j (1 : ℝ) : Fin n → ℝ)) j = z j + c := by
    intro c; simp
  have hupd : ∀ c : ℝ, Function.update (z + c • (Pi.single j (1 : ℝ) : Fin n → ℝ)) j 0 =
      Function.update z j 0 := by
    intro c; funext i
    by_cases h : i = j
    · subst h; simp
    · simp [Function.update_of_ne h, Pi.single_eq_of_ne h]
  have hlen : ∀ c : ℝ, fibreLength K j (z + c • (Pi.single j (1 : ℝ) : Fin n → ℝ)) =
      fibreLength K j z := by
    intro c
    rw [← fibreLength_update K j _ 0, hupd, fibreLength_update]
  have h1 := (hmem (-(δ / 2)) (by rw [abs_neg, abs_of_pos (by positivity)]; linarith)).2.1
  have h2 := (hmem (δ / 2) (by rw [abs_of_pos (by positivity)]; linarith)).2.2
  rw [hj] at h1 h2
  rw [hlen] at h2
  constructor <;> linarith

/-- **An interior point of `K` on the line of `z`**, for `z` interior to the shaking. -/
theorem exists_interior_on_line {K : Set (Fin n → ℝ)} (hKconv : Convex ℝ K)
    {c : Fin n → ℝ} (hc : c ∈ interior K) {j : Fin n} {z : Fin n → ℝ}
    (hz : z ∈ interior (coordShaking K j)) :
    ∃ s : ℝ, Function.update z j s ∈ interior K := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hz)
  -- a slightly pushed point `z + ε (z - c)` is still in the shaking
  set ε : ℝ := δ / (2 * (‖z - c‖ + 1)) with hε
  have hεpos : 0 < ε := by positivity
  set z₂ := z + ε • (z - c) with hz₂
  have hz₂mem : z₂ ∈ coordShaking K j := by
    apply hball
    rw [mem_ball, dist_eq_norm, hz₂, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos hεpos, hε]
    have h1 : ‖z - c‖ < ‖z - c‖ + 1 := lt_add_one _
    have h2 : 0 < ‖z - c‖ + 1 := by positivity
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg (z - c)]
  obtain ⟨t, ht⟩ := hz₂mem.1
  set q := Function.update z₂ j t with hq
  -- the point of the segment `[c, q]` over `z` is interior
  set θ : ℝ := ε / (1 + ε) with hθ
  have hθ0 : 0 < θ := by positivity
  have hθ1 : θ < 1 := by rw [hθ, div_lt_one (by positivity)]; linarith
  set p := θ • c + (1 - θ) • q with hp
  have hpint : p ∈ interior K := by
    have hseg := hKconv.openSegment_interior_closure_subset_interior hc (subset_closure ht)
    refine hseg ⟨θ, 1 - θ, hθ0, by linarith, by ring, ?_⟩
    rfl
  refine ⟨p j, ?_⟩
  have hpz : Function.update z j (p j) = p := by
    funext i
    by_cases h : i = j
    · subst h; simp
    · rw [Function.update_of_ne h, hp]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hq, Function.update_of_ne h, hz₂,
        Pi.sub_apply]
      have h1 : 1 - θ = 1 / (1 + ε) := by
        rw [hθ]; field_simp; ring
      rw [h1, hθ]
      field_simp
      ring
  rw [hpz]
  exact hpint

/-- **Points strictly inside the fibre over an interior point of the shaking are interior.** -/
theorem update_mem_interior {K : Set (Fin n → ℝ)} (hKc : IsCompact K) (hKconv : Convex ℝ K)
    (hKint : (interior K).Nonempty) {j : Fin n} {z : Fin n → ℝ}
    (hz : z ∈ interior (coordShaking K j)) {s : ℝ}
    (hs1 : sInf (fibre K j z) < s) (hs2 : s < sSup (fibre K j z)) :
    Function.update z j s ∈ interior K := by
  obtain ⟨c, hc⟩ := hKint
  obtain ⟨s₀, hs₀⟩ := exists_interior_on_line hKconv hc hz
  have hne : (fibre K j z).Nonempty := (interior_subset hz).1
  have hfc := isCompact_fibre hKc j z
  have ha : Function.update z j (sInf (fibre K j z)) ∈ K :=
    update_mem_of_mem_fibre (hfc.sInf_mem hne)
  have hb : Function.update z j (sSup (fibre K j z)) ∈ K :=
    update_mem_of_mem_fibre (hfc.sSup_mem hne)
  have hs₀K : s₀ ∈ fibre K j z := (interior_subset hs₀ : Function.update z j s₀ ∈ K)
  have hs₀a : sInf (fibre K j z) ≤ s₀ := csInf_le hfc.bddBelow hs₀K
  have hs₀b : s₀ ≤ sSup (fibre K j z) := le_csSup hfc.bddAbove hs₀K
  -- `update z j s` on an open segment from the interior point to an endpoint
  have hcomb : ∀ (e : ℝ) (θ : ℝ), Function.update z j s =
      θ • Function.update z j s₀ + (1 - θ) • Function.update z j e →
      0 < θ → θ < 1 → Function.update z j e ∈ K → Function.update z j s ∈ interior K := by
    intro e θ heq hθ0 hθ1 he
    rw [heq]
    exact hKconv.openSegment_interior_closure_subset_interior hs₀ (subset_closure he)
      ⟨θ, 1 - θ, hθ0, by linarith, by ring, rfl⟩
  rcases lt_trichotomy s s₀ with hlt | heq | hgt
  · set a := sInf (fibre K j z)
    have hne' : s₀ - a ≠ 0 := by linarith
    refine hcomb a ((s - a) / (s₀ - a)) ?_ (div_pos (by linarith) (by linarith))
      ((div_lt_one (by linarith)).2 (by linarith)) ha
    funext i
    by_cases h : i = j
    · rw [h]
      simp only [Function.update_self, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      field_simp; ring
    · simp only [Function.update_of_ne h, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  · rw [heq]; exact hs₀
  · set b := sSup (fibre K j z)
    have hne' : b - s₀ ≠ 0 := by linarith
    refine hcomb b ((b - s) / (b - s₀)) ?_ (div_pos (by linarith) (by linarith))
      ((div_lt_one (by linarith)).2 (by linarith)) hb
    funext i
    by_cases h : i = j
    · rw [h]
      simp only [Function.update_self, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      field_simp; ring
    · simp only [Function.update_of_ne h, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

/-- **Lemma 3.2 vi)** for `u = e_j`: `G(int K) ≥ G(int sh_{e_j}(K))`. -/
theorem ncard_latticePoints_interior_coordShaking_le {K : Set (Fin n → ℝ)} (hKc : IsCompact K)
    (hKconv : Convex ℝ K) (hKint : (interior K).Nonempty) (j : Fin n) :
    (DiscreteMinkowski.latticePoints (interior (coordShaking K j))
      (standardIntegerLattice n)).ncard ≤
    (DiscreteMinkowski.latticePoints (interior K) (standardIntegerLattice n)).ncard := by
  set Φ : (Fin n → ℝ) → (Fin n → ℝ) := fun z =>
    Function.update z j (z j + ⌊sInf (fibre K j z)⌋) with hΦ
  have hfin : (DiscreteMinkowski.latticePoints (interior K) (standardIntegerLattice n)).Finite :=
    DiscreteMinkowski.finite_inter_lattice (hKc.isBounded.subset interior_subset) _
  refine Set.ncard_le_ncard_of_injOn Φ ?_ ?_ hfin
  · rintro z ⟨hz, hzΛ⟩
    obtain ⟨w, hw⟩ := (mem_standardIntegerLattice_iff n z).1 hzΛ
    obtain ⟨h0, hl⟩ := lt_of_mem_interior_coordShaking hz
    have hz1 : (1 : ℝ) ≤ z j := by
      rw [hw j] at h0 ⊢; exact_mod_cast (Int.cast_pos.1 h0 : 0 < w j)
    set a := sInf (fibre K j z)
    have hfl := Int.floor_le a
    have hfg := Int.lt_floor_add_one a
    refine ⟨update_mem_interior hKc hKconv hKint hz ?_ ?_, ?_⟩
    · linarith
    · unfold fibreLength at hl; linarith
    · refine (mem_standardIntegerLattice_iff n _).2
        ⟨Function.update w j (w j + ⌊a⌋), fun i => ?_⟩
      by_cases h : i = j
      · subst h; simp [hΦ, hw i, a]
      · simp [hΦ, Function.update_of_ne h, hw i]
  · intro z₁ _ z₂ _ hz
    have hoff : ∀ i, i ≠ j → z₁ i = z₂ i := by
      intro i hi
      have := congrFun hz i
      simpa [hΦ, Function.update_of_ne hi] using this
    have hf : fibre K j z₁ = fibre K j z₂ := by
      have : Function.update z₁ j 0 = Function.update z₂ j 0 := by
        funext i
        by_cases h : i = j
        · subst h; simp
        · simp [Function.update_of_ne h, hoff i h]
      rw [← fibre_update K j z₁ 0, this, fibre_update]
    have hj := congrFun hz j
    simp only [hΦ, Function.update_self, hf] at hj
    funext i
    by_cases h : i = j
    · subst h; linarith
    · exact hoff i h

end

end LatticeVolumeInterpolation
