import LemmaFiveOne
import TheoremOneFourLower
import MinkowskiLower

/-!
# Theorem 1.4: the planar bounds

Catalog items `theorem_1_4_upper_bound` (Eq. (1.13)), `theorem_1_4_lower_bound` (Eq. (1.14)),
`theorem_1_4_lower_bound_product_form` (the unnumbered display after Theorem 1.4) and
`diagonal_section_bound` (Eq. (5.3)).

For every `K ∈ K^2`:

  `G(K) ≤ vol(K) (1 + λ_1/2)(1 + λ_2)`  and  `G(int K) ≥ vol(K) (1 - λ_1/2 - λ_2)`.

The proof is the paper's. Theorem 3.1 replaces `K` by an anti-blocking body with no fewer lattice
points, no more interior lattice points, the same volume and no larger minima; Lemma 3.3 (after
swapping the axes if needed) gives `|e_i|_{cs(K)} = λ_i(K)`; Lemma 5.1 moves the body under the
diagonal `x_1 + x_2 ≤ 2/λ_1`. For that body the horizontal sections have length
`f(t) ≤ f(0) - t` (Eq. (5.3)), `f(0) = 2/λ_1` and height `2/λ_2`, and the counting cores
`ncard_le_core_upper` and `ncard_interior_ge_core_lower` give

  `G ≤ vol + 2/λ_1 + 1/λ_2 + 1`  and  `G(int) ≥ vol - 2/λ_1 - 1/λ_2`,

which the planar lower bound of Minkowski's second theorem, `vol λ_1 λ_2 ≥ 2`, turns into the
stated products.
-/

open Set MeasureTheory

namespace LatticeVolumeInterpolation

noncomputable section

/-! ### Swapping the two axes -/

/-- The coordinate swap `(x_1, x_2) ↦ (x_2, x_1)`. -/
def swap2 : (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ) where
  toFun x := ![x 1, x 0]
  invFun x := ![x 1, x 0]
  map_add' x y := by refine vec2_ext ?_ ?_ <;> simp
  map_smul' r x := by refine vec2_ext ?_ ?_ <;> simp
  left_inv x := by refine vec2_ext ?_ ?_ <;> simp
  right_inv x := by refine vec2_ext ?_ ?_ <;> simp

theorem swap2_apply (x : Fin 2 → ℝ) : swap2 x = ![x 1, x 0] := rfl

theorem swap2_mem_lattice_iff (x : Fin 2 → ℝ) :
    swap2 x ∈ standardIntegerLattice 2 ↔ x ∈ standardIntegerLattice 2 := by
  rw [swap2_apply, mem_standardIntegerLattice_iff, mem_standardIntegerLattice_iff]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨![z 1, z 0], fun j => ?_⟩
    have h0 := hz 0
    have h1 := hz 1
    simp at h0 h1
    fin_cases j <;> simp [h0, h1]
  · rintro ⟨z, hz⟩
    refine ⟨![z 1, z 0], fun j => ?_⟩
    fin_cases j <;> simp [hz 0, hz 1]

theorem abs_det_swap2 :
    |LinearMap.det (swap2 : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ))| = 1 := by
  rw [← LinearMap.det_toMatrix', Matrix.det_fin_two]
  simp [LinearMap.toMatrix'_apply, swap2_apply]

theorem swap2_single_one : swap2 (Pi.single 1 (1 : ℝ)) = Pi.single 0 1 := by
  refine vec2_ext ?_ ?_ <;> simp [swap2_apply]

theorem swap2_single_zero : swap2 (Pi.single 0 (1 : ℝ)) = Pi.single 1 1 := by
  refine vec2_ext ?_ ?_ <;> simp [swap2_apply]

theorem axisGauge_swap2_zero (K : Set (Fin 2 → ℝ)) :
    axisGauge (swap2 '' K) 0 = axisGauge K 1 := by
  rw [axisGauge, halfDifferenceBody_image, ← swap2_single_one, gauge_image_apply]

theorem axisGauge_swap2_one (K : Set (Fin 2 → ℝ)) :
    axisGauge (swap2 '' K) 1 = axisGauge K 0 := by
  rw [axisGauge, halfDifferenceBody_image, ← swap2_single_zero, gauge_image_apply]

theorem isAntiBlocking_swap2 {K : Set (Fin 2 → ℝ)} (hK : IsAntiBlocking K) :
    IsAntiBlocking (swap2 '' K) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ i
    fin_cases i <;> simp [swap2_apply, hK.1 x hx]
  · rintro _ ⟨x, hx, rfl⟩ y hy0 hyx
    refine ⟨swap2 y, hK.2 x hx _ (fun i => ?_) (fun i => ?_), ?_⟩
    · fin_cases i <;> simpa [swap2_apply] using hy0 _
    · fin_cases i
      · simpa [swap2_apply] using hyx 1
      · simpa [swap2_apply] using hyx 0
    · rw [← LinearEquiv.trans_apply]
      refine vec2_ext ?_ ?_ <;> simp [swap2_apply]

/-- **Lemma 3.3 in the plane, normalized**: a planar anti-blocking body can be replaced, by
swapping the axes if necessary, by one with `|e_1|_{cs} = λ_1` and `|e_2|_{cs} = λ_2`, changing
none of the paper's functionals. -/
theorem exists_normalized_antiBlocking {K : Set (Fin 2 → ℝ)} (hKc : IsCompact K)
    (hKb : DiscreteMinkowski.IsPaperConvexBody K) (hK : IsAntiBlocking K) :
    ∃ K' : Set (Fin 2 → ℝ), IsCompact K' ∧ DiscreteMinkowski.IsPaperConvexBody K' ∧
      IsAntiBlocking K' ∧ volume K' = volume K ∧ G2 K' = G2 K ∧
      G2 (interior K') = G2 (interior K) ∧ lam2 K' 1 = lam2 K 1 ∧ lam2 K' 2 = lam2 K 2 ∧
      axisGauge K' 0 = lam2 K' 1 ∧ axisGauge K' 1 = lam2 K' 2 := by
  by_cases hle : axisGauge K 0 ≤ axisGauge K 1
  · obtain ⟨h1, h2⟩ := lam2_eq_axisGauge hKc hKb hK hle
    exact ⟨K, hKc, hKb, hK, rfl, rfl, rfl, rfl, rfl, h1.symm, h2.symm⟩
  · push Not at hle
    have hΛ := swap2_mem_lattice_iff
    have hc' := isCompact_image swap2 hKc
    have hb' := isPaperConvexBody_image swap2 hKb
    have hab' := isAntiBlocking_swap2 hK
    have hle' : axisGauge (swap2 '' K) 0 ≤ axisGauge (swap2 '' K) 1 := by
      rw [axisGauge_swap2_zero, axisGauge_swap2_one]; exact hle.le
    obtain ⟨h1, h2⟩ := lam2_eq_axisGauge hc' hb' hab' hle'
    refine ⟨swap2 '' K, hc', hb', hab', volume_image_of_det swap2 abs_det_swap2 K,
      ncard_latticePoints_image swap2 hΛ K, ?_, successiveMinimum_image swap2 hΛ K 1,
      successiveMinimum_image swap2 hΛ K 2, h1.symm, h2.symm⟩
    show G2 (interior (swap2 '' K)) = G2 (interior K)
    rw [interior_image_linearEquiv]
    exact ncard_latticePoints_image swap2 hΛ _

/-! ### The section data of an anti-blocking body -/

theorem hwidth_zero_eq {A : Set (Fin 2 → ℝ)} (hAc : IsCompact A)
    (hAb : DiscreteMinkowski.IsPaperConvexBody A) (hA : IsAntiBlocking A) :
    hwidth A 0 = 2 / axisGauge A 0 := by
  refine IsGreatest.csSup_eq ⟨?_, fun s hs => ?_⟩
  · show pt (2 / axisGauge A 0) 0 ∈ A
    rw [← smul_single_zero']; exact axis_point_mem hAc hAb hA 0
  · have := coord_le_two_div_axisGauge hAb hA (hs : pt s 0 ∈ A) 0
    simpa using this

theorem pheight_eq {A : Set (Fin 2 → ℝ)} (hAc : IsCompact A)
    (hAb : DiscreteMinkowski.IsPaperConvexBody A) (hA : IsAntiBlocking A) :
    pheight A = 2 / axisGauge A 1 := by
  refine IsGreatest.csSup_eq ⟨?_, fun s hs => ?_⟩
  · show pt 0 (2 / axisGauge A 1) ∈ A
    rw [← smul_single_one']; exact axis_point_mem hAc hAb hA 1
  · have := coord_le_two_div_axisGauge hAb hA (hs : pt 0 s ∈ A) 1
    simpa using this

/-- **Eq. (5.3)** for the reduced body: `f(t) ≤ f(0) - t = 2/λ_1 - t`. -/
theorem diagonal_section_bound {A : Set (Fin 2 → ℝ)} (hAc : IsCompact A)
    (hAb : DiscreteMinkowski.IsPaperConvexBody A) (hA : IsAntiBlocking A)
    (hg : axisGauge A 0 = lam2 A 1) (hdiag : ∀ x ∈ A, x 0 + x 1 ≤ 2 / lam2 A 1) {t : ℝ}
    (ht : t ∈ Icc 0 (pheight A)) :
    hwidth A t ≤ hwidth A 0 - t ∧ hwidth A 0 = 2 / lam2 A 1 := by
  have h0 : hwidth A 0 = 2 / lam2 A 1 := by rw [hwidth_zero_eq hAc hAb hA, hg]
  refine ⟨hwidth_le_diag hAc (fun x hx => h0 ▸ hdiag x hx) ?_, h0⟩
  exact (mem_axis_iff hAc hA (hAb.2.2.mono interior_subset) t).2 ht

/-- The planar lower bound of Minkowski's second theorem, `vol(A) λ_1 λ_2 ≥ 2`. -/
theorem two_le_volume_mul_lam {A : Set (Fin 2 → ℝ)} (hAc : IsCompact A)
    (hAb : DiscreteMinkowski.IsPaperConvexBody A) :
    2 ≤ (volume A).toReal * lam2 A 1 * lam2 A 2 := by
  have hdim : Module.finrank ℝ (Fin 2 → ℝ) = 2 := Module.finrank_fin_fun ℝ
  have hl1 : 0 < lam2 A 1 :=
    DiscreteMinkowski.successiveMinimum_pos hAb le_rfl (by rw [hdim]; norm_num)
  have hl2 : 0 < lam2 A 2 :=
    DiscreteMinkowski.successiveMinimum_pos hAb (by norm_num) (by rw [hdim])
  have h := minkowski_second_theorem_lower hAc hAb
  rw [Fin.prod_univ_two, ENNReal.ofReal_le_iff_le_toReal hAc.measure_lt_top.ne] at h
  simp only [Fin.isValue, Fin.val_zero, zero_add, Fin.val_one, Nat.reduceAdd,
    Nat.factorial_two, Nat.cast_ofNat] at h
  change 1 / 2 * (2 / lam2 A 1 * (2 / lam2 A 2)) ≤ _ at h
  have : 1 / 2 * (2 / lam2 A 1 * (2 / lam2 A 2)) = 2 / (lam2 A 1 * lam2 A 2) := by
    field_simp
  rw [this, div_le_iff₀ (mul_pos hl1 hl2)] at h
  linarith

/-! ### The reduction chain -/

/-- Theorem 3.1, Lemma 3.3 and Lemma 5.1 together: every planar convex body is dominated by a
compact anti-blocking body `A` under the diagonal `x_1 + x_2 ≤ 2/λ_1(A)` with
`|e_i|_{cs(A)} = λ_i(A)`. -/
theorem exists_planar_reduction {K : Set (Fin 2 → ℝ)} (hKc : IsCompact K)
    (hKb : DiscreteMinkowski.IsPaperConvexBody K) :
    ∃ A : Set (Fin 2 → ℝ), IsCompact A ∧ DiscreteMinkowski.IsPaperConvexBody A ∧
      IsAntiBlocking A ∧ volume A = volume K ∧ G2 K ≤ G2 A ∧
      G2 (interior A) ≤ G2 (interior K) ∧ lam2 A 1 ≤ lam2 K 1 ∧ lam2 A 2 ≤ lam2 K 2 ∧
      (∀ x ∈ A, x 0 + x 1 ≤ 2 / lam2 A 1) ∧ axisGauge A 0 = lam2 A 1 ∧
      axisGauge A 1 = lam2 A 2 := by
  obtain ⟨K1, hK1c, hK1b, hK1ab, hv1, hG1, hI1, hl1⟩ := theorem_3_1 hKc hKb
  obtain ⟨K2, hK2c, hK2b, hK2ab, hv2, hG2, hI2, hl21, hl22, hg0, hg1⟩ :=
    exists_normalized_antiBlocking hK1c hK1b hK1ab
  obtain ⟨hAc, hAb, hAab, hvA, hGA, hIA, hlA1, hlA2, hdiag, hgA0, hgA1⟩ :=
    lemma_5_1 hK2c hK2b hK2ab hg0 hg1
  have hl10 := hl1 0
  have hl11 := hl1 1
  simp only [Fin.isValue, Fin.val_zero, zero_add, Fin.val_one, Nat.reduceAdd] at hl10 hl11
  refine ⟨planarReduction K2, hAc, hAb, hAab, hvA.trans (hv2.trans hv1), ?_, ?_, ?_, ?_,
    hdiag, hgA0, hgA1⟩
  · exact hG1.trans (hG2.symm.le.trans hGA)
  · exact hIA.trans (hI2.le.trans hI1)
  · exact hlA1.trans (hl21.le.trans hl10)
  · exact hlA2.le.trans (hl22.le.trans hl11)

/-- For the reduced body, the counting cores read `G ≤ vol + 2/λ_1 + 1/λ_2 + 1` and
`G(int) ≥ vol - 2/λ_1 - 1/λ_2`. -/
theorem reduced_body_counts {A : Set (Fin 2 → ℝ)} (hAc : IsCompact A)
    (hAb : DiscreteMinkowski.IsPaperConvexBody A) (hA : IsAntiBlocking A)
    (hdiag : ∀ x ∈ A, x 0 + x 1 ≤ 2 / lam2 A 1) (hg0 : axisGauge A 0 = lam2 A 1)
    (hg1 : axisGauge A 1 = lam2 A 2) :
    (G2 A : ℝ) ≤ (volume A).toReal + 2 / lam2 A 1 + 1 / lam2 A 2 + 1 ∧
      (volume A).toReal - 2 / lam2 A 1 - 1 / lam2 A 2 ≤ (G2 (interior A) : ℝ) := by
  have hne : A.Nonempty := hAb.2.2.mono interior_subset
  have hw : hwidth A 0 = 2 / lam2 A 1 := by rw [hwidth_zero_eq hAc hAb hA, hg0]
  have hT : pheight A = 2 / lam2 A 2 := by rw [pheight_eq hAc hAb hA, hg1]
  have hdiag' : ∀ x ∈ A, x 0 + x 1 ≤ hwidth A 0 := fun x hx => hw ▸ hdiag x hx
  have hvol := volume_eq_integral_hwidth hAc hAb.2.1 hA hne
  have hpos : 0 < ∫ t in (0 : ℝ)..pheight A, hwidth A t := by
    have := volume_pos_of_isPaperConvexBody hAb
    rw [hvol] at this
    exact ENNReal.ofReal_pos.1 this
  have hV : (volume A).toReal = ∫ t in (0 : ℝ)..pheight A, hwidth A t := by
    rw [hvol, ENNReal.toReal_ofReal hpos.le]
  have hup := ncard_le_core_upper hAc hAb.2.1 hA hne hdiag'
  have hlo := ncard_interior_ge_core_lower hAc hAb.2.1 hA hne hdiag'
  rw [← hV, hw, hT] at hup hlo
  have h2 : 2 / lam2 A 2 / 2 = 1 / lam2 A 2 := by ring
  rw [h2] at hup hlo
  exact ⟨hup, hlo⟩

/-! ### Theorem 1.4 -/

/-- **Theorem 1.4, Eq. (1.13).** For every `K ∈ K^2`,
`G(K) ≤ vol(K) (1 + λ_1(K)/2)(1 + λ_2(K))`. -/
theorem theorem_1_4_upper {K : Set (Fin 2 → ℝ)} (hKc : IsCompact K)
    (hKb : DiscreteMinkowski.IsPaperConvexBody K) :
    (G2 K : ℝ) ≤ (volume K).toReal * (1 + lam2 K 1 / 2) * (1 + lam2 K 2) := by
  obtain ⟨A, hAc, hAb, hA, hvA, hGA, -, hl1, hl2, hdiag, hg0, hg1⟩ :=
    exists_planar_reduction hKc hKb
  have hdim : Module.finrank ℝ (Fin 2 → ℝ) = 2 := Module.finrank_fin_fun ℝ
  have hm1 : 0 < lam2 A 1 :=
    DiscreteMinkowski.successiveMinimum_pos hAb le_rfl (by rw [hdim]; norm_num)
  have hm2 : 0 < lam2 A 2 :=
    DiscreteMinkowski.successiveMinimum_pos hAb (by norm_num) (by rw [hdim])
  have hmink := two_le_volume_mul_lam hAc hAb
  obtain ⟨hup, -⟩ := reduced_body_counts hAc hAb hA hdiag hg0 hg1
  rw [hvA] at hup hmink
  set V := (volume K).toReal
  set μ₁ := lam2 A 1
  set μ₂ := lam2 A 2
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have e1 : 2 / μ₁ ≤ V * μ₂ := by rw [div_le_iff₀ hm1]; nlinarith
  have e2 : 1 / μ₂ ≤ V * μ₁ / 2 := by rw [div_le_iff₀ hm2]; nlinarith
  have hGK : (G2 K : ℝ) ≤ G2 A := by exact_mod_cast hGA
  have hmono : (1 + μ₁ / 2) * (1 + μ₂) ≤ (1 + lam2 K 1 / 2) * (1 + lam2 K 2) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  calc (G2 K : ℝ) ≤ V + 2 / μ₁ + 1 / μ₂ + 1 := hGK.trans hup
    _ ≤ V * ((1 + μ₁ / 2) * (1 + μ₂)) := by nlinarith
    _ ≤ V * ((1 + lam2 K 1 / 2) * (1 + lam2 K 2)) := mul_le_mul_of_nonneg_left hmono hV
    _ = V * (1 + lam2 K 1 / 2) * (1 + lam2 K 2) := by ring

/-- **Theorem 1.4, Eq. (1.14).** For every `K ∈ K^2`,
`G(int K) ≥ vol(K) (1 - λ_1(K)/2 - λ_2(K))`. -/
theorem theorem_1_4_lower {K : Set (Fin 2 → ℝ)} (hKc : IsCompact K)
    (hKb : DiscreteMinkowski.IsPaperConvexBody K) :
    (volume K).toReal * (1 - lam2 K 1 / 2 - lam2 K 2) ≤ (G2 (interior K) : ℝ) := by
  obtain ⟨A, hAc, hAb, hA, hvA, -, hIA, hl1, hl2, hdiag, hg0, hg1⟩ :=
    exists_planar_reduction hKc hKb
  have hdim : Module.finrank ℝ (Fin 2 → ℝ) = 2 := Module.finrank_fin_fun ℝ
  have hm1 : 0 < lam2 A 1 :=
    DiscreteMinkowski.successiveMinimum_pos hAb le_rfl (by rw [hdim]; norm_num)
  have hm2 : 0 < lam2 A 2 :=
    DiscreteMinkowski.successiveMinimum_pos hAb (by norm_num) (by rw [hdim])
  have hmink := two_le_volume_mul_lam hAc hAb
  obtain ⟨-, hlo⟩ := reduced_body_counts hAc hAb hA hdiag hg0 hg1
  rw [hvA] at hlo hmink
  set V := (volume K).toReal
  set μ₁ := lam2 A 1
  set μ₂ := lam2 A 2
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have e1 : 2 / μ₁ ≤ V * μ₂ := by rw [div_le_iff₀ hm1]; nlinarith
  have e2 : 1 / μ₂ ≤ V * μ₁ / 2 := by rw [div_le_iff₀ hm2]; nlinarith
  have hIK : (G2 (interior A) : ℝ) ≤ G2 (interior K) := by exact_mod_cast hIA
  calc V * (1 - lam2 K 1 / 2 - lam2 K 2) ≤ V * (1 - μ₁ / 2 - μ₂) :=
        mul_le_mul_of_nonneg_left (by linarith) hV
    _ ≤ V - 2 / μ₁ - 1 / μ₂ := by nlinarith
    _ ≤ G2 (interior K) := hlo.trans hIK

/-- **The product form after Theorem 1.4.** If `λ_1(K) ≤ 2ε/(1 + ε)` then
`G(int K) ≥ vol(K) (1 - λ_1/2)(1 - (1 + ε) λ_2)`. -/
theorem theorem_1_4_lower_product_form {K : Set (Fin 2 → ℝ)} (hKc : IsCompact K)
    (hKb : DiscreteMinkowski.IsPaperConvexBody K) {ε : ℝ} (hε : 0 < ε)
    (hlam : lam2 K 1 ≤ 2 * ε / (1 + ε)) :
    (volume K).toReal * ((1 - lam2 K 1 / 2) * (1 - (1 + ε) * lam2 K 2)) ≤
      (G2 (interior K) : ℝ) := by
  have hdim : Module.finrank ℝ (Fin 2 → ℝ) = 2 := Module.finrank_fin_fun ℝ
  have hl2 : 0 < lam2 K 2 :=
    DiscreteMinkowski.successiveMinimum_pos hKb (by norm_num) (by rw [hdim])
  have hV : 0 ≤ (volume K).toReal := ENNReal.toReal_nonneg
  have hl1' : (1 + ε) * lam2 K 1 ≤ 2 * ε := by
    rw [le_div_iff₀ (by linarith)] at hlam; linarith
  have hprod : (1 - lam2 K 1 / 2) * (1 - (1 + ε) * lam2 K 2) ≤ 1 - lam2 K 1 / 2 - lam2 K 2 := by
    nlinarith
  exact (mul_le_mul_of_nonneg_left hprod hV).trans (theorem_1_4_lower hKc hKb)

end

end LatticeVolumeInterpolation
