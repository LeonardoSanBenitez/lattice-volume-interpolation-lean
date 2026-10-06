import MinimaAntiBlocking

/-!
# Blaschke shaking along a coordinate direction

Catalog items `blaschke_shaking`, `shaking_preserves_convexity` and
`lemma_3_2_shaking_properties` (Sec. 3), for the directions `u = e_j`, which are the ones the
proof of Theorem 3.1 uses.

For `K ⊆ ℝ^n` and a coordinate `j`, the **fibre** of `K` over `y` is
`F(y) = {t ∈ ℝ | y with its j-th coordinate replaced by t lies in K}`, which depends only on
the coordinates of `y` other than `j`; its length is `l(y) = sup F(y) - inf F(y)`. The shaking
pushes each fibre down onto the hyperplane `x_j = 0`, keeping its length:

  `sh_{e_j}(K) = {x | F(x) ≠ ∅, 0 ≤ x_j ≤ l(x)}`.

This is the paper's `⋃_{x ∈ K|e_j^⊥} [x, x + f_{e_j,K}(x) e_j]` (Sec. 3) with
`f_{e_j,K} = l`. For a compact convex `K` every non-empty fibre is the interval
`[inf F, sup F]`.
-/

open Set Module
open scoped Pointwise

namespace LatticeVolumeInterpolation

noncomputable section

variable {n : ℕ}

/-- The fibre of `K` over `y` in the direction `e_j`. -/
def fibre (K : Set (Fin n → ℝ)) (j : Fin n) (y : Fin n → ℝ) : Set ℝ :=
  {t | Function.update y j t ∈ K}

/-- The length of the fibre, `f_{e_j,K}` in the paper. -/
def fibreLength (K : Set (Fin n → ℝ)) (j : Fin n) (y : Fin n → ℝ) : ℝ :=
  sSup (fibre K j y) - sInf (fibre K j y)

/-- **The Blaschke shaking along `e_j`.** -/
def coordShaking (K : Set (Fin n → ℝ)) (j : Fin n) : Set (Fin n → ℝ) :=
  {x | (fibre K j x).Nonempty ∧ 0 ≤ x j ∧ x j ≤ fibreLength K j x}

theorem fibre_update (K : Set (Fin n → ℝ)) (j : Fin n) (y : Fin n → ℝ) (s : ℝ) :
    fibre K j (Function.update y j s) = fibre K j y := by
  ext t
  simp [fibre, Function.update_idem]

theorem fibreLength_update (K : Set (Fin n → ℝ)) (j : Fin n) (y : Fin n → ℝ) (s : ℝ) :
    fibreLength K j (Function.update y j s) = fibreLength K j y := by
  simp [fibreLength, fibre_update]

theorem self_mem_fibre {K : Set (Fin n → ℝ)} (j : Fin n) {x : Fin n → ℝ} (hx : x ∈ K) :
    x j ∈ fibre K j x := by
  simp [fibre, hx]

theorem update_mem_of_mem_fibre {K : Set (Fin n → ℝ)} {j : Fin n} {y : Fin n → ℝ} {t : ℝ}
    (ht : t ∈ fibre K j y) : Function.update y j t ∈ K := ht

theorem isCompact_fibre {K : Set (Fin n → ℝ)} (hK : IsCompact K) (j : Fin n)
    (y : Fin n → ℝ) : IsCompact (fibre K j y) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · exact hK.isClosed.preimage (continuous_const.update j continuous_id)
  · refine ((hK.image (continuous_apply j)).isBounded).subset ?_
    intro t ht
    exact ⟨_, ht, by simp⟩

theorem update_convex_comb (y₁ y₂ : Fin n → ℝ) (j : Fin n) (t₁ t₂ a b : ℝ) :
    Function.update (a • y₁ + b • y₂) j (a * t₁ + b * t₂) =
      a • Function.update y₁ j t₁ + b • Function.update y₂ j t₂ := by
  funext i
  by_cases h : i = j
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem convex_fibre {K : Set (Fin n → ℝ)} (hK : Convex ℝ K) (j : Fin n) (y : Fin n → ℝ) :
    Convex ℝ (fibre K j y) := by
  intro t₁ h₁ t₂ h₂ a b ha hb hab
  have h := hK h₁ h₂ ha hb hab
  rw [← update_convex_comb y y j t₁ t₂ a b] at h
  simp only [fibre, mem_setOf_eq, smul_eq_mul]
  convert h using 2
  rw [← add_smul, hab, one_smul]

/-- A compact fibre is bounded above and below, and contains its extremes. -/
theorem fibre_bdd {K : Set (Fin n → ℝ)} (hK : IsCompact K) (j : Fin n) (y : Fin n → ℝ) :
    BddAbove (fibre K j y) ∧ BddBelow (fibre K j y) :=
  ⟨(isCompact_fibre hK j y).bddAbove, (isCompact_fibre hK j y).bddBelow⟩

theorem sub_le_fibreLength {K : Set (Fin n → ℝ)} (hK : IsCompact K) {j : Fin n}
    {y : Fin n → ℝ} {s t : ℝ} (hs : s ∈ fibre K j y) (ht : t ∈ fibre K j y) :
    t - s ≤ fibreLength K j y := by
  have h1 := le_csSup (fibre_bdd hK j y).1 ht
  have h2 := csInf_le (fibre_bdd hK j y).2 hs
  unfold fibreLength
  linarith

theorem fibreLength_nonneg {K : Set (Fin n → ℝ)} (hK : IsCompact K) {j : Fin n}
    {y : Fin n → ℝ} (hne : (fibre K j y).Nonempty) : 0 ≤ fibreLength K j y := by
  obtain ⟨t, ht⟩ := hne
  have := sub_le_fibreLength hK ht ht
  linarith

/-- **Lemma 3.2 i).** The projection `K | e_j^⊥` lies in the shaking. -/
theorem update_zero_mem_coordShaking {K : Set (Fin n → ℝ)} (hK : IsCompact K) (j : Fin n)
    {x : Fin n → ℝ} (hx : x ∈ K) : Function.update x j 0 ∈ coordShaking K j := by
  have hne : (fibre K j x).Nonempty := ⟨x j, self_mem_fibre j hx⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [fibre_update]; exact hne
  · simp
  · rw [fibreLength_update]; simpa using fibreLength_nonneg hK hne

/-- The data `(a, b, s)` whose image is the shaking: two points of `K` on one line in the
direction `e_j`, in increasing order, and a height between `0` and their distance. -/
def shakingData (K : Set (Fin n → ℝ)) (j : Fin n) :
    Set ((Fin n → ℝ) × (Fin n → ℝ) × ℝ) :=
  {p | p.1 ∈ K ∧ p.2.1 ∈ K ∧ (∀ i, i ≠ j → p.1 i = p.2.1 i) ∧ 0 ≤ p.2.2 ∧
    p.2.2 ≤ p.2.1 j - p.1 j}

theorem coordShaking_eq_image {K : Set (Fin n → ℝ)} (hK : IsCompact K) (j : Fin n) :
    coordShaking K j =
      (fun p : (Fin n → ℝ) × (Fin n → ℝ) × ℝ => Function.update p.1 j p.2.2) ''
        shakingData K j := by
  ext x
  constructor
  · rintro ⟨hne, h0, hl⟩
    have hc := isCompact_fibre hK j x
    have hinf : sInf (fibre K j x) ∈ fibre K j x := hc.sInf_mem hne
    have hsup : sSup (fibre K j x) ∈ fibre K j x := hc.sSup_mem hne
    refine ⟨(Function.update x j (sInf (fibre K j x)),
      Function.update x j (sSup (fibre K j x)), x j), ⟨hinf, hsup, ?_, h0, ?_⟩, ?_⟩
    · intro i hi; simp [Function.update_of_ne hi]
    · simpa [fibreLength] using hl
    · simp
  · rintro ⟨⟨a, b, s⟩, ⟨ha, hb, hab, hs0, hsl⟩, rfl⟩
    have hbf : b j ∈ fibre K j a := by
      have : Function.update a j (b j) = b := by
        funext i
        by_cases h : i = j
        · subst h; simp
        · rw [Function.update_of_ne h]; exact hab i h
      simp only [fibre, mem_setOf_eq, this, hb]
    refine ⟨?_, ?_, ?_⟩
    · rw [fibre_update]; exact ⟨a j, self_mem_fibre j ha⟩
    · simpa using hs0
    · rw [fibreLength_update]
      simp only [Function.update_self]
      exact hsl.trans (sub_le_fibreLength hK (self_mem_fibre j ha) hbf)

theorem isCompact_shakingData {K : Set (Fin n → ℝ)} (hK : IsCompact K) (j : Fin n) :
    IsCompact (shakingData K j) := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  have hsub : shakingData K j ⊆ K ×ˢ (K ×ˢ Icc 0 (2 * R)) := by
    rintro ⟨a, b, s⟩ ⟨ha, hb, -, hs0, hsl⟩
    refine ⟨ha, hb, hs0, ?_⟩
    have hna : ‖a‖ ≤ R := by simpa using hR ha
    have hnb : ‖b‖ ≤ R := by simpa using hR hb
    have h1 : |a j| ≤ R := (norm_le_pi_norm a j).trans hna
    have h2 : |b j| ≤ R := (norm_le_pi_norm b j).trans hnb
    have := abs_le.1 h1
    have := abs_le.1 h2
    linarith
  refine (hK.prod (hK.prod isCompact_Icc)).of_isClosed_subset ?_ hsub
  have hc1 : IsClosed {p : (Fin n → ℝ) × (Fin n → ℝ) × ℝ | p.1 ∈ K} :=
    hK.isClosed.preimage continuous_fst
  have hc2 : IsClosed {p : (Fin n → ℝ) × (Fin n → ℝ) × ℝ | p.2.1 ∈ K} :=
    hK.isClosed.preimage (continuous_fst.comp continuous_snd)
  have hc3 : IsClosed {p : (Fin n → ℝ) × (Fin n → ℝ) × ℝ | ∀ i, i ≠ j → p.1 i = p.2.1 i} := by
    simp only [setOf_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun _ =>
      isClosed_eq ((continuous_apply i).comp continuous_fst)
        ((continuous_apply i).comp (continuous_fst.comp continuous_snd))
  have hc4 : IsClosed {p : (Fin n → ℝ) × (Fin n → ℝ) × ℝ | 0 ≤ p.2.2} :=
    isClosed_le continuous_const (continuous_snd.comp continuous_snd)
  have hc5 : IsClosed {p : (Fin n → ℝ) × (Fin n → ℝ) × ℝ | p.2.2 ≤ p.2.1 j - p.1 j} :=
    isClosed_le (continuous_snd.comp continuous_snd)
      (((continuous_apply j).comp (continuous_fst.comp continuous_snd)).sub
        ((continuous_apply j).comp continuous_fst))
  exact hc1.inter (hc2.inter (hc3.inter (hc4.inter hc5)))

/-- The shaking of a compact set is compact. -/
theorem isCompact_coordShaking {K : Set (Fin n → ℝ)} (hK : IsCompact K) (j : Fin n) :
    IsCompact (coordShaking K j) := by
  rw [coordShaking_eq_image hK j]
  exact (isCompact_shakingData hK j).image (by fun_prop)

/-- **Convexity of the shaking** (`shaking_preserves_convexity`, the orthogonal case quoted from
Campi, Colesanti and Gronchi). The fibre length is concave, because the fibre over a convex
combination contains the corresponding combination of fibres. -/
theorem convex_coordShaking {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hKc : Convex ℝ K)
    (j : Fin n) : Convex ℝ (coordShaking K j) := by
  intro x₁ hx₁ x₂ hx₂ a b ha hb hab
  obtain ⟨hne₁, h0₁, hl₁⟩ := hx₁
  obtain ⟨hne₂, h0₂, hl₂⟩ := hx₂
  have hc₁ := isCompact_fibre hK j x₁
  have hc₂ := isCompact_fibre hK j x₂
  set y := a • x₁ + b • x₂ with hy
  have hcomb : ∀ t₁ ∈ fibre K j x₁, ∀ t₂ ∈ fibre K j x₂, a * t₁ + b * t₂ ∈ fibre K j y := by
    intro t₁ ht₁ t₂ ht₂
    simp only [fibre, mem_setOf_eq]
    rw [hy, update_convex_comb x₁ x₂ j t₁ t₂ a b]
    exact hKc ht₁ ht₂ ha hb hab
  have hsup := hcomb _ (hc₁.sSup_mem hne₁) _ (hc₂.sSup_mem hne₂)
  have hinf := hcomb _ (hc₁.sInf_mem hne₁) _ (hc₂.sInf_mem hne₂)
  have hlen : a * fibreLength K j x₁ + b * fibreLength K j x₂ ≤ fibreLength K j y := by
    have := sub_le_fibreLength hK hinf hsup
    unfold fibreLength at this ⊢
    nlinarith
  refine ⟨⟨_, hsup⟩, ?_, ?_⟩
  · simp only [hy, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    positivity
  · simp only [hy, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hlen ⊢
    nlinarith

theorem update_smul_sub (x a b : Fin n → ℝ) (j : Fin n) (r : ℝ)
    (hx : x = r • ((2 : ℝ)⁻¹ • (a - b))) :
    Function.update x j 0 =
      r • ((2 : ℝ)⁻¹ • (Function.update a j 0 - Function.update b j 0)) := by
  subst hx
  funext i
  by_cases h : i = j
  · subst h; simp
  · simp [Function.update_of_ne h]

/-- **Lemma 3.2 iv)** for `u = e_j`: `|x|_{cs(K)} ≥ |x | e_j^⊥|_{cs(sh K)}`. -/
theorem gauge_coordShaking_update_le {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (hKb : DiscreteMinkowski.IsPaperConvexBody K) (j : Fin n) (x : Fin n → ℝ) :
    gauge (DiscreteMinkowski.halfDifferenceBody (coordShaking K j)) (Function.update x j 0) ≤
      gauge (DiscreteMinkowski.halfDifferenceBody K) x := by
  refine le_of_forall_gt_imp_ge_of_dense fun r hr => ?_
  have hr0 : 0 < r := lt_of_le_of_lt (gauge_nonneg _) hr
  have hx : x ∈ r • DiscreteMinkowski.halfDifferenceBody K :=
    DiscreteMinkowski.mem_smul_of_gauge_lt hKb hr
  obtain ⟨d, hd, rfl⟩ := mem_smul_set.1 hx
  rw [DiscreteMinkowski.halfDifferenceBody_apply] at hd
  obtain ⟨w, ⟨a, ha, b, hb, rfl⟩, rfl⟩ := mem_smul_set.1 hd
  have hmem : Function.update (r • ((2 : ℝ)⁻¹ • (a - b))) j 0 ∈
      r • DiscreteMinkowski.halfDifferenceBody (coordShaking K j) := by
    rw [update_smul_sub _ a b j r rfl, DiscreteMinkowski.halfDifferenceBody_apply]
    exact smul_mem_smul_set (smul_mem_smul_set (sub_mem_sub
      (update_zero_mem_coordShaking hK j ha) (update_zero_mem_coordShaking hK j hb)))
  exact DiscreteMinkowski.gauge_le_of_mem_smul hr0.le hmem

/-- **Lemma 3.2 iii)** for `u = e_j`, in the direction used by Claim 1:
`|e_j|_{cs(sh K)} ≤ |e_j|_{cs(K)}`. -/
theorem gauge_coordShaking_single_le {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (hKb : DiscreteMinkowski.IsPaperConvexBody K) (j : Fin n) :
    gauge (DiscreteMinkowski.halfDifferenceBody (coordShaking K j))
        (Pi.single j (1 : ℝ) : Fin n → ℝ) ≤
      gauge (DiscreteMinkowski.halfDifferenceBody K) (Pi.single j (1 : ℝ) : Fin n → ℝ) := by
  refine le_of_forall_gt_imp_ge_of_dense fun r hr => ?_
  have hr0 : 0 < r := lt_of_le_of_lt (gauge_nonneg _) hr
  have hx : (Pi.single j (1 : ℝ) : Fin n → ℝ) ∈ r • DiscreteMinkowski.halfDifferenceBody K :=
    DiscreteMinkowski.mem_smul_of_gauge_lt hKb hr
  obtain ⟨d, hd, hdx⟩ := mem_smul_set.1 hx
  rw [DiscreteMinkowski.halfDifferenceBody_apply] at hd
  obtain ⟨w, ⟨a, ha, b, hb, rfl⟩, rfl⟩ := mem_smul_set.1 hd
  -- coordinates of `e_j = (r/2)(a - b)`
  have hcoord : ∀ i, (Pi.single j (1 : ℝ) : Fin n → ℝ) i = r * (2⁻¹ * (a i - b i)) := by
    intro i
    rw [← hdx]
    simp [smul_eq_mul]
  have hoff : ∀ i, i ≠ j → b i = a i := by
    intro i hi
    have := hcoord i
    rw [Pi.single_eq_of_ne hi] at this
    have hr2 : r * 2⁻¹ ≠ 0 := by positivity
    have : r * 2⁻¹ * (a i - b i) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hr2
    · linarith
  have hon : a j - b j = 2 / r := by
    have := hcoord j
    rw [Pi.single_eq_same] at this
    field_simp
    linarith
  have hbf : b j ∈ fibre K j a := by
    have : Function.update a j (b j) = b := by
      funext i
      by_cases h : i = j
      · subst h; simp
      · rw [Function.update_of_ne h]; exact (hoff i h).symm
    simp only [fibre, mem_setOf_eq, this, hb]
  have hlen : 2 / r ≤ fibreLength K j a := by
    have := sub_le_fibreLength hK hbf (self_mem_fibre j ha)
    linarith
  have hp : Function.update a j 0 ∈ coordShaking K j := update_zero_mem_coordShaking hK j ha
  have hq : Function.update a j (2 / r) ∈ coordShaking K j := by
    refine ⟨?_, ?_, ?_⟩
    · rw [fibre_update]; exact ⟨a j, self_mem_fibre j ha⟩
    · simp only [Function.update_self]; positivity
    · rw [fibreLength_update]; simpa using hlen
  have hdiff : (Pi.single j (1 : ℝ) : Fin n → ℝ) =
      r • ((2 : ℝ)⁻¹ • (Function.update a j (2 / r) - Function.update a j 0)) := by
    funext i
    by_cases h : i = j
    · subst h; simp; field_simp
    · simp [Function.update_of_ne h, Pi.single_eq_of_ne h]
  have hmem : (Pi.single j (1 : ℝ) : Fin n → ℝ) ∈
      r • DiscreteMinkowski.halfDifferenceBody (coordShaking K j) := by
    rw [hdiff, DiscreteMinkowski.halfDifferenceBody_apply]
    exact smul_mem_smul_set (smul_mem_smul_set (sub_mem_sub hq hp))
  exact DiscreteMinkowski.gauge_le_of_mem_smul hr0.le hmem

/-- Lemma 3.2 iii) for every multiple `c e_j` of the shaking direction. -/
theorem gauge_coordShaking_smul_single_le {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (hKb : DiscreteMinkowski.IsPaperConvexBody K) (j : Fin n) (c : ℝ) :
    gauge (DiscreteMinkowski.halfDifferenceBody (coordShaking K j))
        (c • (Pi.single j (1 : ℝ) : Fin n → ℝ)) ≤
      gauge (DiscreteMinkowski.halfDifferenceBody K) (c • (Pi.single j (1 : ℝ) : Fin n → ℝ)) := by
  have h1 := gauge_halfDifferenceBody_smul (coordShaking K j) c (Pi.single j (1 : ℝ))
  have h2 := gauge_halfDifferenceBody_smul K c (Pi.single j (1 : ℝ))
  rw [h1, h2]
  exact mul_le_mul_of_nonneg_left (gauge_coordShaking_single_le hK hKb j) (abs_nonneg c)

/-- A non-empty fibre of a compact convex set is the interval between its extremes. -/
theorem fibre_eq_Icc {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hKc : Convex ℝ K) {j : Fin n}
    {y : Fin n → ℝ} (hne : (fibre K j y).Nonempty) :
    fibre K j y = Icc (sInf (fibre K j y)) (sSup (fibre K j y)) := by
  have hc := isCompact_fibre hK j y
  refine Subset.antisymm (fun t ht => ⟨csInf_le hc.bddBelow ht, le_csSup hc.bddAbove ht⟩) ?_
  have hord := (convex_iff_ordConnected.1 (convex_fibre hKc j y))
  exact hord.out (hc.sInf_mem hne) (hc.sSup_mem hne)

open Classical in
/-- The fibre of the shaking: `[0, l(y)]` over a non-empty fibre of `K`, empty otherwise. -/
theorem fibre_coordShaking (K : Set (Fin n → ℝ)) (j : Fin n) (y : Fin n → ℝ) :
    fibre (coordShaking K j) j y =
      if (fibre K j y).Nonempty then Icc 0 (fibreLength K j y) else ∅ := by
  ext t
  change Function.update y j t ∈ coordShaking K j ↔ _
  simp only [coordShaking, mem_setOf_eq, fibre_update, fibreLength_update,
    Function.update_self]
  split_ifs with h
  · simp [h]
  · simp [h]

open Classical in
/-- The measure of a fibre of a compact convex set is its length, or `0` when it is empty. -/
theorem volume_fibre {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hKc : Convex ℝ K) (j : Fin n)
    (y : Fin n → ℝ) :
    MeasureTheory.volume (fibre K j y) =
      if (fibre K j y).Nonempty then ENNReal.ofReal (fibreLength K j y) else 0 := by
  split_ifs with h
  · rw [fibre_eq_Icc hK hKc h, Real.volume_Icc]
    rfl
  · rw [not_nonempty_iff_eq_empty.1 h, MeasureTheory.measure_empty]

/-- **Lemma 3.2 ii)** for `u = e_j`: shaking preserves volume. Both bodies have, over every
point of the hyperplane, a fibre of the same length, so Fubini gives the same volume. -/
theorem volume_coordShaking {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hKc : Convex ℝ K)
    (j : Fin n) : MeasureTheory.volume (coordShaking K j) = MeasureTheory.volume K := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := j.2; omega⟩
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) j with he
  have hpres : MeasureTheory.MeasurePreserving e MeasureTheory.volume
      (MeasureTheory.volume.prod MeasureTheory.volume) :=
    MeasureTheory.measurePreserving_piFinSuccAbove
      (fun _ : Fin (m + 1) => (MeasureTheory.volume : MeasureTheory.Measure ℝ)) j
  have hsymm : ∀ (t : ℝ) (y : Fin m → ℝ), e.symm (t, y) = Fin.insertNth j t y := fun _ _ => rfl
  have hvol : ∀ S : Set (Fin (m + 1) → ℝ), MeasurableSet S →
      MeasureTheory.volume S =
        ∫⁻ y, MeasureTheory.volume (fibre S j (Fin.insertNth j 0 y)) := by
    intro S hS
    have hS' : MeasurableSet (e.symm ⁻¹' S) := hS.preimage e.symm.measurable
    have hpre : e ⁻¹' (e.symm ⁻¹' S) = S := by
      ext x; simp
    conv_lhs => rw [← hpre]
    rw [hpres.measure_preimage hS'.nullMeasurableSet,
      MeasureTheory.Measure.prod_apply_symm hS']
    refine MeasureTheory.lintegral_congr fun y => ?_
    congr 1
    ext t
    simp only [mem_preimage, mem_setOf_eq, fibre, hsymm, Fin.update_insertNth]
  rw [hvol _ (isCompact_coordShaking hK j).isClosed.measurableSet,
    hvol _ hK.isClosed.measurableSet]
  refine MeasureTheory.lintegral_congr fun y => ?_
  classical
  rw [fibre_coordShaking, volume_fibre hK hKc]
  split_ifs with h
  · rw [Real.volume_Icc, sub_zero]
  · exact MeasureTheory.measure_empty

/-- **Lemma 3.2 v)** for `u = e_j`: `G(K) ≤ G(sh_{e_j}(K))`. Each lattice point is moved down
its line by the integer `⌈inf F⌉`, which lands it in the shaken fibre `[0, l]`; the move is
injective because it does not change the line. -/
theorem ncard_latticePoints_le_coordShaking {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (j : Fin n) :
    (DiscreteMinkowski.latticePoints K (standardIntegerLattice n)).ncard ≤
      (DiscreteMinkowski.latticePoints (coordShaking K j) (standardIntegerLattice n)).ncard := by
  set Φ : (Fin n → ℝ) → (Fin n → ℝ) := fun z =>
    Function.update z j (z j - ⌈sInf (fibre K j z)⌉) with hΦ
  have hfin : (DiscreteMinkowski.latticePoints (coordShaking K j)
      (standardIntegerLattice n)).Finite :=
    DiscreteMinkowski.finite_inter_lattice (isCompact_coordShaking hK j).isBounded _
  refine Set.ncard_le_ncard_of_injOn Φ ?_ ?_ hfin
  · rintro z ⟨hzK, hzΛ⟩
    obtain ⟨w, hw⟩ := (mem_standardIntegerLattice_iff n z).1 hzΛ
    have hc := isCompact_fibre hK j z
    have hzf : z j ∈ fibre K j z := self_mem_fibre j hzK
    have hinf : sInf (fibre K j z) ≤ z j := csInf_le hc.bddBelow hzf
    have hsup : z j ≤ sSup (fibre K j z) := le_csSup hc.bddAbove hzf
    have hceil : (⌈sInf (fibre K j z)⌉ : ℝ) ≤ z j := by
      rw [hw j]; exact_mod_cast Int.ceil_le.2 (by rw [← hw j]; exact hinf)
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · rw [hΦ, fibre_update]; exact ⟨_, hzf⟩
    · simp only [hΦ, Function.update_self]; linarith
    · simp only [hΦ, Function.update_self, fibreLength_update]
      unfold fibreLength
      linarith [Int.le_ceil (sInf (fibre K j z))]
    · refine (mem_standardIntegerLattice_iff n _).2
        ⟨Function.update w j (w j - ⌈sInf (fibre K j z)⌉), fun i => ?_⟩
      by_cases h : i = j
      · subst h; simp [hΦ, hw i]
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
