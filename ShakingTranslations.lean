import LemmaFiveOne
import Mathlib.Order.ConditionallyCompleteLattice.Indexed

/-!
# Translation bridges for the arbitrary diagonal intercept

Catalog item `lemma_5_1_properties_of_the_planar_reduction`, Lemma 5.1
with its arbitrary diagonal intercept.

Coordinate shaking forgets translation along the direction being shaken.
General shaking is covariant when both the body and target hyperplane move.
-/

open Set
open MeasureTheory
open scoped Pointwise

namespace LatticeVolumeInterpolation

theorem interval_span_image_add (A : Set ℝ) (c : ℝ)
    (ha : BddAbove A) (hb : BddBelow A) :
    sSup ((fun t => t + c) '' A) - sInf ((fun t => t + c) '' A) = sSup A - sInf A := by
  rcases A.eq_empty_or_nonempty with rfl | hne
  · simp
  · have hu := (OrderIso.addRight c).map_csSup' hne ha
    have hl := (OrderIso.addRight c).map_csInf' hne hb
    change sSup A + c = sSup ((fun t => t + c) '' A) at hu
    change sInf A + c = sInf ((fun t => t + c) '' A) at hl
    rw [← hu, ← hl]
    ring

theorem fibre_image_add_single {n : ℕ} (K : Set (Fin n → ℝ)) (j : Fin n)
    (c : ℝ) (x : Fin n → ℝ) :
    fibre ((fun y => y + Pi.single j c) '' K) j x =
      (fun t => t + c) '' fibre K j x := by
  classical
  ext t
  constructor
  · rintro ⟨y, hy, he⟩
    refine ⟨t - c, ?_, by ring⟩
    change Function.update x j (t - c) ∈ K
    have hh : Function.update x j (t - c) = y := by
      ext i
      have hi := congrFun he i
      by_cases hij : i = j
      · subst i; simp at hi ⊢; linarith
      · simpa [Function.update_of_ne hij, Pi.single_eq_of_ne hij] using hi.symm
    rwa [hh]
  · rintro ⟨s, hs, rfl⟩
    refine ⟨Function.update x j s, hs, ?_⟩
    ext i
    by_cases hij : i = j
    · subst i; simp
    · simp [Function.update_of_ne hij, Pi.single_eq_of_ne hij]

theorem coordShaking_image_add_single {n : ℕ} {K : Set (Fin n → ℝ)}
    (hc : IsCompact K) (j : Fin n) (c : ℝ) :
    coordShaking ((fun y => y + Pi.single j c) '' K) j = coordShaking K j := by
  ext x
  have hf := fibre_image_add_single K j c x
  have hl : fibreLength ((fun y => y + Pi.single j c) '' K) j x = fibreLength K j x := by
    unfold fibreLength
    rw [hf]
    exact interval_span_image_add _ c (isCompact_fibre hc j x).bddAbove (isCompact_fibre hc j x).bddBelow
  simp only [coordShaking, mem_setOf_eq, hf, Set.image_nonempty, hl]

theorem obliqueProj_image_add (ν u : Fin 2 → ℝ) (c : ℝ) (v x : Fin 2 → ℝ) :
    obliqueProj ν (c + dot2 ν v) u (x + v) = obliqueProj ν c u x + v := by
  unfold obliqueProj
  rw [dot2_add]
  have hh : dot2 ν x + dot2 ν v - (c + dot2 ν v) = dot2 ν x - c := by ring
  rw [hh]
  abel

theorem dirFibre_image_add (K : Set (Fin 2 → ℝ)) (u p v : Fin 2 → ℝ) :
    dirFibre ((fun x => x + v) '' K) u (p + v) = dirFibre K u p := by
  ext t
  change (p + v + t • unitDir u ∈ (fun x => x + v) '' K) ↔ p + t • unitDir u ∈ K
  have he : p + v + t • unitDir u = (p + t • unitDir u) + v := by abel
  rw [he, (add_left_injective v).mem_set_image]

theorem generalShaking_image_add (K : Set (Fin 2 → ℝ)) (ν u : Fin 2 → ℝ)
    (c : ℝ) (v : Fin 2 → ℝ) :
    generalShaking ((fun x => x + v) '' K) ν (c + dot2 ν v) u =
      (fun x => x + v) '' generalShaking K ν c u := by
  ext y
  constructor
  · rintro ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, s, hs, rfl⟩
    rw [obliqueProj_image_add] at hs ⊢
    have hl : dirLength ((fun x => x + v) '' K) u (obliqueProj ν c u x + v) =
        dirLength K u (obliqueProj ν c u x) := by
      unfold dirLength; rw [dirFibre_image_add]
    rw [hl] at hs
    refine ⟨obliqueProj ν c u x + s • unitDir u, ⟨_, ⟨x, hx, rfl⟩, s, hs, rfl⟩, ?_⟩
    abel
  · rintro ⟨_, ⟨_, ⟨x, hx, rfl⟩, s, hs, rfl⟩, rfl⟩
    refine ⟨_, ⟨x + v, ⟨x, hx, rfl⟩, rfl⟩, s, ?_, ?_⟩
    · rw [obliqueProj_image_add]
      simpa only [dirLength, dirFibre_image_add] using hs
    · rw [obliqueProj_image_add]
      abel

theorem diagShaking_one_intercept {K : Set (Fin 2 → ℝ)} (hc : IsCompact K) (m : ℝ) :
    generalShaking K diagNormal m (negAxis 1) =
      (fun x => x + Pi.single 1 m) '' diagShaking 1 K := by
  have h := dot2_diagNormal_negAxis_ne 1
  have hd := dot2_unitDir_ne_zero h
  have hchart : ∀ x, shakeChart diagNormal m (negAxis 1) x =
      shakeChart diagNormal 0 (negAxis 1) x + Pi.single 1 m := by
    intro x
    simp only [shakeChart, unitDir_negAxis]
    ext i
    fin_cases i <;> simp [negAxis, diagNormal, dot2] <;> ring
  have hinv : ∀ x, shakeChartInv diagNormal m (negAxis 1) x =
      shakeChartInv diagNormal 0 (negAxis 1) x + Pi.single 1 m := by
    intro x
    simp only [shakeChartInv, unitDir_negAxis]
    ext i
    fin_cases i <;> simp [negAxis, diagNormal, dot2] <;> ring
  have himage : shakeChart diagNormal m (negAxis 1) '' K =
      (fun x => x + Pi.single 1 m) '' (shakeChart diagNormal 0 (negAxis 1) '' K) := by
    rw [Set.image_image]
    congr 1
    funext x
    exact hchart x
  change generalShaking K diagNormal m (negAxis 1) =
    (fun x => x + Pi.single 1 m) '' generalShaking K diagNormal 0 (negAxis 1)
  rw [generalShaking_eq h, generalShaking_eq h, himage,
    coordShaking_image_add_single (isCompact_image_shakeChart hd hc) 1 m]
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨_, ⟨z, hz, rfl⟩, (hinv z).symm⟩
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, hinv z⟩

/-- The paper's reduction against the diagonal with arbitrary real intercept. -/
noncomputable def planarReductionAt (m : ℝ) (K : Set (Fin 2 → ℝ)) : Set (Fin 2 → ℝ) :=
  coordShaking (generalShaking (generalShaking K diagNormal m (negAxis 1))
    diagNormal m (negAxis 0)) 1

/-- The two diagonal steps acquire only a vertical translation, which the
last coordinate shaking removes. Integrality of the intercept is unnecessary. -/
theorem planarReductionAt_eq {K : Set (Fin 2 → ℝ)} (hc : IsCompact K) (m : ℝ) :
    planarReductionAt m K = planarReduction K := by
  unfold planarReductionAt
  rw [diagShaking_one_intercept hc m]
  have hm : dot2 diagNormal (Pi.single 1 m) = m := by simp [dot2, diagNormal]
  have hcov := generalShaking_image_add (diagShaking 1 K) diagNormal (negAxis 0) 0 (Pi.single 1 m)
  simp only [zero_add, hm] at hcov
  rw [hcov]
  change coordShaking ((fun x => x + Pi.single 1 m) '' diagShaking 0 (diagShaking 1 K)) 1 = _
  rw [coordShaking_image_add_single (isCompact_diagShaking 0 (isCompact_diagShaking 1 hc))]
  rfl

/-- Lemma 5.1 with the source's arbitrary intercept, and all its conclusions. -/
theorem lemma_5_1_at {K : Set (Fin 2 → ℝ)} (hKc : IsCompact K)
    (hKb : DiscreteMinkowski.IsPaperConvexBody K) (hK : IsAntiBlocking K)
    (h1 : axisGauge K 0 = lam2 K 1) (h2 : axisGauge K 1 = lam2 K 2) (m : ℝ) :
    IsCompact (planarReductionAt m K) ∧ DiscreteMinkowski.IsPaperConvexBody (planarReductionAt m K) ∧
      IsAntiBlocking (planarReductionAt m K) ∧ volume (planarReductionAt m K) = volume K ∧
      G2 K ≤ G2 (planarReductionAt m K) ∧ G2 (interior (planarReductionAt m K)) ≤ G2 (interior K) ∧
      lam2 (planarReductionAt m K) 1 ≤ lam2 K 1 ∧ lam2 (planarReductionAt m K) 2 = lam2 K 2 ∧
      (∀ x ∈ planarReductionAt m K, x 0 + x 1 ≤ 2 / lam2 (planarReductionAt m K) 1) ∧
      axisGauge (planarReductionAt m K) 0 = lam2 (planarReductionAt m K) 1 ∧
      axisGauge (planarReductionAt m K) 1 = lam2 (planarReductionAt m K) 2 := by
  rw [planarReductionAt_eq hKc m]
  exact lemma_5_1 hKc hKb hK h1 h2

end LatticeVolumeInterpolation
