import ConcaveIntegralBounds
import AntiBlocking
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Data.Fin.VecNotation

/-!
# Horizontal sections of a planar anti-blocking body

Support for catalog item `theorem_1_4_upper_bound` and `theorem_1_4_lower_bound` (Sec. 5,
proof of Theorem 1.4). For a compact convex anti-blocking `A ⊆ ℝ^2` the paper considers

  `f : [0, T] → ℝ`, `t ↦ vol_1(A ∩ ℓ_t)`,  `ℓ_t = {x : x_2 = t}`,

where `T` is the height of `A`. Because `A` is anti-blocking, `A ∩ ℓ_t = [0, f(t)] × {t}` for
`t ∈ [0, T]` and is empty otherwise; `f` is concave (convexity of `A`), non-negative, and
`vol(A) = ∫_0^T f` (Fubini). If `A` lies under the diagonal `x_1 + x_2 ≤ f(0)`, then
`f(t) ≤ f(0) - t`, the paper's (5.3).
-/

open MeasureTheory Set
open scoped ENNReal

namespace LatticeVolumeInterpolation

noncomputable section

/-- The point `(s, t)` of the plane. -/
abbrev pt (s t : ℝ) : Fin 2 → ℝ := ![s, t]

theorem pt_comb (a b s₁ t₁ s₂ t₂ : ℝ) :
    a • pt s₁ t₁ + b • pt s₂ t₂ = pt (a * s₁ + b * s₂) (a * t₁ + b * t₂) := by
  ext i; fin_cases i <;> simp

theorem pt_eta (x : Fin 2 → ℝ) : pt (x 0) (x 1) = x := by
  ext i; fin_cases i <;> rfl

/-- The horizontal section of `A` at height `t`. -/
def hsec (A : Set (Fin 2 → ℝ)) (t : ℝ) : Set ℝ := {s | pt s t ∈ A}

/-- Its length, `f(t)` in the paper. -/
def hwidth (A : Set (Fin 2 → ℝ)) (t : ℝ) : ℝ := sSup (hsec A t)

/-- The height of `A`. -/
def pheight (A : Set (Fin 2 → ℝ)) : ℝ := sSup {t | pt 0 t ∈ A}

variable {A : Set (Fin 2 → ℝ)}

theorem isCompact_hsec (hc : IsCompact A) (t : ℝ) : IsCompact (hsec A t) := by
  refine Metric.isCompact_of_isClosed_isBounded
    (hc.isClosed.preimage (by fun_prop : Continuous fun s : ℝ => pt s t)) ?_
  refine ((hc.image (continuous_apply 0)).isBounded).subset ?_
  intro s hs; exact ⟨_, hs, by simp⟩

theorem nonneg_of_mem_antiBlocking (hab : IsAntiBlocking A) {x : Fin 2 → ℝ} (hx : x ∈ A) (i : Fin 2) :
    0 ≤ x i := hab.1 x hx i

/-- Lowering coordinates in an anti-blocking planar set. -/
theorem pt_mem_of_le (hab : IsAntiBlocking A) {s t s' t' : ℝ} (h : pt s t ∈ A)
    (hs' : 0 ≤ s') (hss : s' ≤ s) (ht' : 0 ≤ t') (htt : t' ≤ t) : pt s' t' ∈ A := by
  refine hab.2 _ h _ (fun i => ?_) (fun i => ?_) <;> fin_cases i <;> simpa

theorem hsec_eq_Icc (hc : IsCompact A) (hab : IsAntiBlocking A) {t : ℝ} (ht : pt 0 t ∈ A) :
    hsec A t = Icc 0 (hwidth A t) := by
  have hne : (hsec A t).Nonempty := ⟨0, ht⟩
  have hcpt := isCompact_hsec hc t
  have hsup : hwidth A t ∈ hsec A t := hcpt.sSup_mem hne
  ext s
  constructor
  · intro hs
    exact ⟨by simpa using nonneg_of_mem_antiBlocking hab hs 0, le_csSup hcpt.bddAbove hs⟩
  · rintro ⟨h0, h1⟩
    exact pt_mem_of_le hab hsup h0 h1 (by simpa using nonneg_of_mem_antiBlocking hab ht 1) le_rfl

theorem hsec_eq_empty (hab : IsAntiBlocking A) {t : ℝ} (ht : pt 0 t ∉ A) : hsec A t = ∅ := by
  ext s
  simp only [hsec, mem_setOf_eq, mem_empty_iff_false, iff_false]
  intro hs
  have h0 : 0 ≤ s := by simpa using nonneg_of_mem_antiBlocking hab hs 0
  have h1 : 0 ≤ t := by simpa using nonneg_of_mem_antiBlocking hab hs 1
  exact ht (pt_mem_of_le hab hs le_rfl h0 h1 le_rfl)

theorem axis_set_eq_Icc (hc : IsCompact A) (hab : IsAntiBlocking A) (hne : A.Nonempty) :
    {t | pt 0 t ∈ A} = Icc 0 (pheight A) := by
  obtain ⟨x, hx⟩ := hne
  have h0 : pt 0 0 ∈ A := pt_mem_of_le hab ((pt_eta x).symm ▸ hx) le_rfl
    (nonneg_of_mem_antiBlocking hab hx 0) le_rfl (nonneg_of_mem_antiBlocking hab hx 1)
  have hcpt : IsCompact {t | pt 0 t ∈ A} := by
    refine Metric.isCompact_of_isClosed_isBounded
      (hc.isClosed.preimage (by fun_prop : Continuous fun t : ℝ => pt 0 t)) ?_
    refine ((hc.image (continuous_apply 1)).isBounded).subset ?_
    intro t ht; exact ⟨_, ht, by simp⟩
  have hsup : pheight A ∈ {t | pt 0 t ∈ A} := hcpt.sSup_mem ⟨0, h0⟩
  ext t
  constructor
  · intro ht
    exact ⟨by simpa using nonneg_of_mem_antiBlocking hab ht 1, le_csSup hcpt.bddAbove ht⟩
  · rintro ⟨h0', h1'⟩
    exact pt_mem_of_le hab hsup le_rfl le_rfl h0' h1'

theorem pheight_nonneg (hc : IsCompact A) (hab : IsAntiBlocking A) (hne : A.Nonempty) :
    0 ≤ pheight A := by
  have := axis_set_eq_Icc hc hab hne
  obtain ⟨x, hx⟩ := hne
  have h0 : pt 0 0 ∈ A := pt_mem_of_le hab ((pt_eta x).symm ▸ hx) le_rfl
    (nonneg_of_mem_antiBlocking hab hx 0) le_rfl (nonneg_of_mem_antiBlocking hab hx 1)
  have : (0 : ℝ) ∈ Icc 0 (pheight A) := by rw [← this]; exact h0
  exact this.2

theorem mem_axis_iff (hc : IsCompact A) (hab : IsAntiBlocking A) (hne : A.Nonempty) (t : ℝ) :
    pt 0 t ∈ A ↔ t ∈ Icc 0 (pheight A) := by
  rw [← axis_set_eq_Icc hc hab hne]; rfl

theorem hwidth_nonneg (hc : IsCompact A) (hab : IsAntiBlocking A) {t : ℝ} (ht : pt 0 t ∈ A) :
    0 ≤ hwidth A t := by
  have := hsec_eq_Icc hc hab ht
  have h0 : (0 : ℝ) ∈ hsec A t := ht
  rw [this] at h0; exact h0.2

theorem pt_hwidth_mem (hc : IsCompact A) {t : ℝ} (ht : pt 0 t ∈ A) :
    pt (hwidth A t) t ∈ A := (isCompact_hsec hc t).sSup_mem ⟨0, ht⟩

/-- **`f` is concave** on `[0, T]`. -/
theorem concaveOn_hwidth (hc : IsCompact A) (hconv : Convex ℝ A) (hab : IsAntiBlocking A)
    (hne : A.Nonempty) : ConcaveOn ℝ (Icc 0 (pheight A)) (hwidth A) := by
  refine ⟨convex_Icc _ _, fun t₁ ht₁ t₂ ht₂ a b ha hb hab' => ?_⟩
  have h₁ := pt_hwidth_mem hc ((mem_axis_iff hc hab hne t₁).2 ht₁)
  have h₂ := pt_hwidth_mem hc ((mem_axis_iff hc hab hne t₂).2 ht₂)
  have hcomb := hconv h₁ h₂ ha hb hab'
  rw [pt_comb] at hcomb
  simp only [smul_eq_mul]
  exact le_csSup (isCompact_hsec hc _).bddAbove hcomb

/-- **(5.3)**: under the diagonal, `f(t) ≤ f(0) - t`. -/
theorem hwidth_le_diag (hc : IsCompact A)
    (hdiag : ∀ x ∈ A, x 0 + x 1 ≤ hwidth A 0) {t : ℝ} (ht : pt 0 t ∈ A) :
    hwidth A t ≤ hwidth A 0 - t := by
  have := hdiag _ (pt_hwidth_mem hc ht)
  simp at this
  linarith

/-- **Fubini**: `vol(A) = ∫_0^T f`. -/
theorem volume_eq_integral_hwidth (hc : IsCompact A) (hconv : Convex ℝ A)
    (hab : IsAntiBlocking A) (hne : A.Nonempty) :
    volume A = ENNReal.ofReal (∫ t in (0 : ℝ)..pheight A, hwidth A t) := by
  have hT := pheight_nonneg hc hab hne
  set e := MeasurableEquiv.finTwoArrow (α := ℝ)
  have hpres : MeasurePreserving e volume (volume.prod volume) :=
    volume_preserving_finTwoArrow ℝ
  have hAm : MeasurableSet A := hc.isClosed.measurableSet
  have hpre : e ⁻¹' (e.symm ⁻¹' A) = A := by ext x; simp
  have hmeas : MeasurableSet (e.symm ⁻¹' A) := hAm.preimage e.symm.measurable
  conv_lhs => rw [← hpre]
  rw [hpres.measure_preimage hmeas.nullMeasurableSet, Measure.prod_apply_symm hmeas]
  have hfib : ∀ t : ℝ, volume ((fun s => (s, t)) ⁻¹' (e.symm ⁻¹' A)) =
      (Icc 0 (pheight A)).indicator (fun t => ENNReal.ofReal (hwidth A t)) t := by
    intro t
    have hset : (fun s => (s, t)) ⁻¹' (e.symm ⁻¹' A) = hsec A t := by
      ext s; exact Iff.rfl
    rw [hset]
    by_cases ht : t ∈ Icc 0 (pheight A)
    · rw [indicator_of_mem ht, hsec_eq_Icc hc hab ((mem_axis_iff hc hab hne t).2 ht),
        Real.volume_Icc, sub_zero]
    · rw [indicator_of_notMem ht, hsec_eq_empty hab (fun h => ht ((mem_axis_iff hc hab hne t).1 h)),
        measure_empty]
  simp_rw [hfib]
  have hconc := concaveOn_hwidth hc hconv hab hne
  have hint := concave_intervalIntegrable hT hconc
  rw [lintegral_indicator measurableSet_Icc, ← ofReal_integral_eq_lintegral_ofReal,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT]
  · exact (intervalIntegrable_iff_integrableOn_Icc_of_le hT).1 hint
  · refine (ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ fun t ht => ?_)
    exact hwidth_nonneg hc hab ((mem_axis_iff hc hab hne t).2 ht)

end

end LatticeVolumeInterpolation
