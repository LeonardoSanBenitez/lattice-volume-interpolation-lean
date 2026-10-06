import CoordShaking
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Successive coordinate shakings and Claim 2

Catalog items `claim_2_coordinate_projection_stability` and the parts of
`theorem_3_1_anti_blocking_reduction` that concern the body itself.

The proof of Theorem 3.1 shakes successively in the directions `e_1, ..., e_n`:
`K_0 = K`, `K_j = sh_{e_j}(K_{j-1})`. Indexing coordinates from `0`, `shakeUpTo K k` is the body
after shaking along `e_0, ..., e_{k-1}`. Each shaking keeps the body compact and convex
(`isCompact_coordShaking`, `convex_coordShaking`), keeps its volume (Lemma 3.2 ii)) and so its
non-empty interior, and does not decrease `G` (Lemma 3.2 v)).

**Claim 2** (`claim_2`): every point of `K_k` stays in `K_k` when any of its first `k`
coordinates is set to `0`. At `k = n`, with convexity, this is the anti-blocking property
(`isAntiBlocking_shakeUpTo`).
-/

open Set Module MeasureTheory
open scoped Pointwise

namespace LatticeVolumeInterpolation

noncomputable section

variable {n : ℕ}

/-- The body after shaking along `e_0, ..., e_{k-1}`. -/
def shakeUpTo (K : Set (Fin n → ℝ)) : ℕ → Set (Fin n → ℝ)
  | 0 => K
  | k + 1 => if h : k < n then coordShaking (shakeUpTo K k) ⟨k, h⟩ else shakeUpTo K k

theorem shakeUpTo_succ_of_lt (K : Set (Fin n → ℝ)) {k : ℕ} (h : k < n) :
    shakeUpTo K (k + 1) = coordShaking (shakeUpTo K k) ⟨k, h⟩ := by
  simp [shakeUpTo, h]

theorem shakeUpTo_succ_of_le (K : Set (Fin n → ℝ)) {k : ℕ} (h : n ≤ k) :
    shakeUpTo K (k + 1) = shakeUpTo K k := by
  simp [shakeUpTo, not_lt.2 h]

theorem isCompact_shakeUpTo {K : Set (Fin n → ℝ)} (hK : IsCompact K) :
    ∀ k, IsCompact (shakeUpTo K k)
  | 0 => hK
  | k + 1 => by
    by_cases h : k < n
    · rw [shakeUpTo_succ_of_lt K h]; exact isCompact_coordShaking (isCompact_shakeUpTo hK k) _
    · rw [shakeUpTo_succ_of_le K (not_lt.1 h)]; exact isCompact_shakeUpTo hK k

theorem convex_shakeUpTo {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hKc : Convex ℝ K) :
    ∀ k, Convex ℝ (shakeUpTo K k)
  | 0 => hKc
  | k + 1 => by
    by_cases h : k < n
    · rw [shakeUpTo_succ_of_lt K h]
      exact convex_coordShaking (isCompact_shakeUpTo hK k) (convex_shakeUpTo hK hKc k) _
    · rw [shakeUpTo_succ_of_le K (not_lt.1 h)]; exact convex_shakeUpTo hK hKc k

theorem volume_shakeUpTo {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hKc : Convex ℝ K) :
    ∀ k, volume (shakeUpTo K k) = volume K
  | 0 => rfl
  | k + 1 => by
    by_cases h : k < n
    · rw [shakeUpTo_succ_of_lt K h, volume_coordShaking (isCompact_shakeUpTo hK k)
        (convex_shakeUpTo hK hKc k), volume_shakeUpTo hK hKc k]
    · rw [shakeUpTo_succ_of_le K (not_lt.1 h)]; exact volume_shakeUpTo hK hKc k

theorem ncard_latticePoints_le_shakeUpTo {K : Set (Fin n → ℝ)} (hK : IsCompact K) :
    ∀ k, (DiscreteMinkowski.latticePoints K (standardIntegerLattice n)).ncard ≤
      (DiscreteMinkowski.latticePoints (shakeUpTo K k) (standardIntegerLattice n)).ncard
  | 0 => le_rfl
  | k + 1 => by
    by_cases h : k < n
    · rw [shakeUpTo_succ_of_lt K h]
      exact (ncard_latticePoints_le_shakeUpTo hK k).trans
        (ncard_latticePoints_le_coordShaking (isCompact_shakeUpTo hK k) _)
    · rw [shakeUpTo_succ_of_le K (not_lt.1 h)]; exact ncard_latticePoints_le_shakeUpTo hK k

/-- A convex set of positive volume has non-empty interior. -/
theorem interior_nonempty_of_volume_pos {S : Set (Fin n → ℝ)} (hS : Convex ℝ S)
    (hvol : 0 < volume S) : (interior S).Nonempty := by
  by_contra h
  have hspan : affineSpan ℝ S ≠ ⊤ := by
    intro htop
    exact h ((hS.interior_nonempty_iff_affineSpan_eq_top).2 htop)
  have h0 : volume (affineSpan ℝ S : Set (Fin n → ℝ)) = 0 :=
    Measure.addHaar_affineSubspace volume _ hspan
  have := measure_mono (μ := volume) (subset_affineSpan ℝ S)
  rw [h0] at this
  exact (lt_irrefl _ (hvol.trans_le this))

/-- Each `K_k` is a convex body in the paper's sense. -/
theorem isPaperConvexBody_shakeUpTo {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (hKb : DiscreteMinkowski.IsPaperConvexBody K) (k : ℕ) :
    DiscreteMinkowski.IsPaperConvexBody (shakeUpTo K k) := by
  refine ⟨(isCompact_shakeUpTo hK k).isBounded, convex_shakeUpTo hK hKb.2.1 k, ?_⟩
  refine interior_nonempty_of_volume_pos (convex_shakeUpTo hK hKb.2.1 k) ?_
  rw [volume_shakeUpTo hK hKb.2.1 k]
  obtain ⟨x, hx⟩ := hKb.2.2
  exact lt_of_lt_of_le (isOpen_interior.measure_pos volume ⟨x, hx⟩)
    (measure_mono interior_subset)

/-- The first `k` coordinates of every point of `K_k` are non-negative. -/
theorem nonneg_of_mem_shakeUpTo {K : Set (Fin n → ℝ)} :
    ∀ k, ∀ x ∈ shakeUpTo K k, ∀ i : Fin n, i.1 < k → 0 ≤ x i
  | 0 => fun _ _ _ hi => absurd hi (Nat.not_lt_zero _)
  | k + 1 => by
    intro x hx i hi
    by_cases h : k < n
    · rw [shakeUpTo_succ_of_lt K h] at hx
      obtain ⟨⟨t, ht⟩, h0, -⟩ := hx
      by_cases hik : i.1 = k
      · have : i = ⟨k, h⟩ := Fin.ext hik
        subst this; exact h0
      · have hne : i ≠ ⟨k, h⟩ := fun e => hik (congrArg Fin.val e)
        have := nonneg_of_mem_shakeUpTo k _ ht i (by omega)
        rwa [Function.update_of_ne hne] at this
    · rw [shakeUpTo_succ_of_le K (not_lt.1 h)] at hx
      exact nonneg_of_mem_shakeUpTo k x hx i (by omega)

/-- **Claim 2.** For `x ∈ K_k` and a coordinate `i < k`, setting `x_i = 0` stays in `K_k`. -/
theorem claim_2 {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hKc : Convex ℝ K) :
    ∀ k, ∀ x ∈ shakeUpTo K k, ∀ i : Fin n, i.1 < k → Function.update x i 0 ∈ shakeUpTo K k
  | 0 => fun _ _ _ hi => absurd hi (Nat.not_lt_zero _)
  | k + 1 => by
    intro x hx i hi
    by_cases h : k < n
    · set j : Fin n := ⟨k, h⟩ with hj
      have hKk := isCompact_shakeUpTo hK k
      rw [shakeUpTo_succ_of_lt K h] at hx ⊢
      by_cases hik : i.1 = k
      · -- Lemma 3.2 i)
        have hij : i = j := Fin.ext hik
        subst hij
        obtain ⟨⟨t, ht⟩, -, -⟩ := hx
        have := update_zero_mem_coordShaking hKk j ht
        rwa [Function.update_idem] at this
      · have hij : i ≠ j := fun e => hik (congrArg Fin.val e)
        obtain ⟨hne, h0, hl⟩ := hx
        have hc := isCompact_fibre hKk j x
        set a := sInf (fibre (shakeUpTo K k) j x) with ha
        have haF : a ∈ fibre (shakeUpTo K k) j x := hc.sInf_mem hne
        have hsupF : sSup (fibre (shakeUpTo K k) j x) ∈ fibre (shakeUpTo K k) j x :=
          hc.sSup_mem hne
        -- the segment `[y, y + x_j e_j]` from the lowest point `y` lies in `K_k`
        have hseg : ∀ t ∈ Icc a (a + x j), t ∈ fibre (shakeUpTo K k) j x := by
          intro t ht
          have hord := convex_iff_ordConnected.1
            (convex_fibre (convex_shakeUpTo hK hKc k) j x)
          refine hord.out haF hsupF ⟨ht.1, ?_⟩
          unfold fibreLength at hl
          linarith [ht.2]
        -- by induction its projection along `e_i` lies in `K_k`
        have hproj : ∀ t ∈ Icc a (a + x j),
            t ∈ fibre (shakeUpTo K k) j (Function.update x i 0) := by
          intro t ht
          have hmem := claim_2 hK hKc k _ (hseg t ht) i (by omega)
          simp only [fibre, mem_setOf_eq]
          rw [Function.update_comm hij]; exact hmem
        have hlen : x j ≤ fibreLength (shakeUpTo K k) j (Function.update x i 0) := by
          have := sub_le_fibreLength hKk (hproj a ⟨le_rfl, by linarith⟩)
            (hproj (a + x j) ⟨by linarith, le_rfl⟩)
          linarith
        refine ⟨⟨a, hproj a ⟨le_rfl, by linarith⟩⟩, ?_, ?_⟩
        · rw [Function.update_of_ne hij.symm]; exact h0
        · rw [Function.update_of_ne hij.symm]; exact hlen
    · rw [shakeUpTo_succ_of_le K (not_lt.1 h)] at hx ⊢
      exact claim_2 hK hKc k x hx i (by omega)

/-- Lowering one coordinate of a point of a convex set closed under zeroing that coordinate. -/
theorem update_mem_of_le {S : Set (Fin n → ℝ)} (hS : Convex ℝ S) {x : Fin n → ℝ} (hx : x ∈ S)
    {i : Fin n} (hzero : Function.update x i 0 ∈ S) {t : ℝ} (ht0 : 0 ≤ t) (htx : t ≤ x i) :
    Function.update x i t ∈ S := by
  rcases (ht0.trans htx).eq_or_lt with hxi | hxi
  · have : t = 0 := le_antisymm (hxi ▸ htx) ht0
    rw [this]; exact hzero
  · have hcomb := hS hx hzero (div_nonneg ht0 hxi.le)
      (by rw [sub_nonneg, div_le_one hxi]; exact htx) (by ring : t / x i + (1 - t / x i) = 1)
    convert hcomb using 1
    funext l
    by_cases h : l = i
    · subst h; simp; field_simp
    · simp [Function.update_of_ne h]; ring

/-- **The body after all `n` shakings is anti-blocking.** -/
theorem isAntiBlocking_shakeUpTo {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hKc : Convex ℝ K) :
    IsAntiBlocking (shakeUpTo K n) := by
  set A := shakeUpTo K n
  have hAc := convex_shakeUpTo hK hKc n
  refine ⟨fun x hx i => nonneg_of_mem_shakeUpTo n x hx i i.2, ?_⟩
  intro x hx y hy0 hyx
  -- lower the coordinates one at a time, along a finite set `s` of coordinates
  have key : ∀ s : Finset (Fin n), (fun l => if l ∈ s then y l else x l) ∈ A := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hx
    | insert i s hi ih =>
      set z := fun l => if l ∈ s then y l else x l with hz
      have hzi : z i = x i := by simp [hz, hi]
      have hzero : Function.update z i 0 ∈ A := claim_2 hK hKc n z ih i i.2
      have h := update_mem_of_le hAc ih hzero (hy0 i) (by rw [hzi]; exact hyx i)
      convert h using 1
      funext l
      by_cases h : l = i
      · subst h; simp
      · simp [Finset.mem_insert, h, hz]
  have := key Finset.univ
  simpa using this

end

end LatticeVolumeInterpolation
