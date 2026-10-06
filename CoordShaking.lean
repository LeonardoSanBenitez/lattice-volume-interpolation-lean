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

end

end LatticeVolumeInterpolation
