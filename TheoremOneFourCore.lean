import PlanarSections
import CoordinateLattice

/-!
# The counting core of Theorem 1.4

Catalog items `theorem_1_4_upper_bound` and `theorem_1_4_lower_bound`, the part of the proof
after the reductions (Sec. 5, proof of Theorem 1.4). For a compact convex anti-blocking
`A ⊆ ℝ^2` of height `T`, with section length `f` and bottom width `a = f(0)`, lying under the
diagonal `x_1 + x_2 ≤ a`:

* `G(A) ≤ vol(A) + a + T/2 + 1` (`ncard_le_core_upper`): the lattice points lie on the lines
  `x_2 = i`, `0 ≤ i ≤ ⌊T⌋`, each carrying at most `f(i) + 1` of them; the paper then rewrites
  `∑ f(i)` with the trapezoid bound of Lemma 5.2 and (5.3).
-/

open MeasureTheory Set
open scoped ENNReal

namespace LatticeVolumeInterpolation

noncomputable section

variable {A : Set (Fin 2 → ℝ)}

/-- `∑_{i=0}^N f(i) ≤ (f(0) + f(N))/2 + ∫_0^N f`, by the trapezoid bound on each `[i-1, i]`. -/
theorem sum_le_trapezoid {f : ℝ → ℝ} {T : ℝ} (hf : ConcaveOn ℝ (Icc 0 T) f) :
    ∀ N : ℕ, (N : ℝ) ≤ T →
      ∑ i ∈ Finset.range (N + 1), f i ≤ (f 0 + f N) / 2 + ∫ t in (0 : ℝ)..N, f t
  | 0, _ => by simp
  | N + 1, hN => by
    have hN' : (N : ℝ) ≤ T := by push_cast at hN; linarith
    have ih := sum_le_trapezoid hf N hN'
    have hsub : ConcaveOn ℝ (Icc (N : ℝ) (N + 1)) f :=
      hf.subset (Icc_subset_Icc (Nat.cast_nonneg N) (by push_cast at hN; exact hN))
        (convex_Icc _ _)
    have hchord := concave_integral_chord_le (by linarith : (N : ℝ) ≤ N + 1) hsub
    have hint1 : IntervalIntegrable f volume 0 N :=
      concave_intervalIntegrable (Nat.cast_nonneg N)
        (hf.subset (Icc_subset_Icc le_rfl hN') (convex_Icc _ _))
    have hint2 : IntervalIntegrable f volume N (N + 1) :=
      concave_intervalIntegrable (by linarith) hsub
    rw [Finset.sum_range_succ, Nat.cast_succ,
      ← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
    nlinarith [ih, hchord]

/-- The lattice points of `A` lie on the lines `x_2 = i`, `0 ≤ i ≤ ⌊T⌋`, with at most
`⌊f(i)⌋ + 1` on each. -/
theorem ncard_latticePoints_le_sum (hc : IsCompact A) (hab : IsAntiBlocking A)
    (hne : A.Nonempty) :
    ((DiscreteMinkowski.latticePoints A (standardIntegerLattice 2)).ncard : ℝ) ≤
      ∑ i ∈ Finset.range (⌊pheight A⌋₊ + 1), (hwidth A i + 1) := by
  classical
  set N := ⌊pheight A⌋₊
  set S : Finset (Fin 2 → ℝ) := (Finset.range (N + 1)).biUnion fun i =>
    (Finset.range (⌊hwidth A i⌋₊ + 1)).image fun k : ℕ => pt (k : ℝ) (i : ℝ)
  have hsub : DiscreteMinkowski.latticePoints A (standardIntegerLattice 2) ⊆ ↑S := by
    rintro z ⟨hzA, hzΛ⟩
    obtain ⟨w, hw⟩ := (mem_standardIntegerLattice_iff 2 z).1 hzΛ
    have h0 := nonneg_of_mem_antiBlocking hab hzA 0
    have h1 := nonneg_of_mem_antiBlocking hab hzA 1
    rw [hw 0] at h0; rw [hw 1] at h1
    have hw0 : 0 ≤ w 0 := by exact_mod_cast h0
    have hw1 : 0 ≤ w 1 := by exact_mod_cast h1
    set i := (w 1).toNat
    set k := (w 0).toNat
    have hi : (i : ℝ) = z 1 := by
      rw [hw 1]; exact_mod_cast Int.toNat_of_nonneg hw1
    have hk : (k : ℝ) = z 0 := by
      rw [hw 0]; exact_mod_cast Int.toNat_of_nonneg hw0
    have hzpt : pt k i = z := by rw [hk, hi, pt_eta]
    have hzA' : pt (z 0) (z 1) ∈ A := by rw [pt_eta]; exact hzA
    have hax : pt 0 (z 1) ∈ A := pt_mem_of_le hab hzA' le_rfl (le_of_eq_of_le rfl
      (nonneg_of_mem_antiBlocking hab hzA 0)) (nonneg_of_mem_antiBlocking hab hzA 1) le_rfl
    have hT : z 1 ≤ pheight A := ((mem_axis_iff hc hab hne _).1 hax).2
    have hwid : z 0 ≤ hwidth A (z 1) := by
      have := hsec_eq_Icc hc hab hax
      have hmem : z 0 ∈ hsec A (z 1) := hzA'
      rw [this] at hmem; exact hmem.2
    simp only [S, Finset.coe_biUnion, Finset.coe_range, Finset.coe_image, mem_iUnion,
      mem_Iio, mem_image, exists_prop]
    refine ⟨i, Nat.lt_succ_of_le (Nat.le_floor (show (i : ℝ) ≤ pheight A by rw [hi]; exact hT)),
      k, Nat.lt_succ_of_le (Nat.le_floor (show (k : ℝ) ≤ hwidth A i by rw [hk, hi]; exact hwid)),
      hzpt⟩
  have hcard : (DiscreteMinkowski.latticePoints A (standardIntegerLattice 2)).ncard ≤ S.card := by
    rw [← Set.ncard_coe_finset S]
    exact Set.ncard_le_ncard hsub (Finset.finite_toSet S)
  have hS : S.card ≤ ∑ i ∈ Finset.range (N + 1), (⌊hwidth A i⌋₊ + 1) := by
    refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun i _ => ?_)
    exact Finset.card_image_le.trans (by simp)
  calc ((DiscreteMinkowski.latticePoints A (standardIntegerLattice 2)).ncard : ℝ)
      ≤ ∑ i ∈ Finset.range (N + 1), ((⌊hwidth A i⌋₊ : ℝ) + 1) := by
        exact_mod_cast hcard.trans hS
    _ ≤ ∑ i ∈ Finset.range (N + 1), (hwidth A i + 1) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hiT : (i : ℝ) ≤ pheight A := by
          have := Finset.mem_range.1 hi
          exact (Nat.cast_le.2 (Nat.lt_succ_iff.1 this)).trans (Nat.floor_le
            (pheight_nonneg hc hab hne))
        have hax : pt 0 (i : ℝ) ∈ A := (mem_axis_iff hc hab hne _).2 ⟨Nat.cast_nonneg i, hiT⟩
        have := Nat.floor_le (hwidth_nonneg hc hab hax)
        linarith

/-- **The upper counting core**: `G(A) ≤ vol(A) + a + T/2 + 1`. -/
theorem ncard_le_core_upper (hc : IsCompact A) (hconv : Convex ℝ A) (hab : IsAntiBlocking A)
    (hne : A.Nonempty) (hdiag : ∀ x ∈ A, x 0 + x 1 ≤ hwidth A 0) :
    ((DiscreteMinkowski.latticePoints A (standardIntegerLattice 2)).ncard : ℝ) ≤
      (∫ t in (0 : ℝ)..pheight A, hwidth A t) + hwidth A 0 + pheight A / 2 + 1 := by
  set T := pheight A
  set N := ⌊T⌋₊
  have hT := pheight_nonneg hc hab hne
  have hNT : (N : ℝ) ≤ T := Nat.floor_le hT
  have hconc := concaveOn_hwidth hc hconv hab hne
  have hcount := ncard_latticePoints_le_sum hc hab hne
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    at hcount
  have htrap := sum_le_trapezoid hconc N hNT
  have hfN : hwidth A N ≤ hwidth A 0 - N :=
    hwidth_le_diag hc hdiag ((mem_axis_iff hc hab hne _).2 ⟨Nat.cast_nonneg N, hNT⟩)
  have hint : ∫ t in (0 : ℝ)..N, hwidth A t ≤ ∫ t in (0 : ℝ)..T, hwidth A t := by
    have h1 : IntervalIntegrable (hwidth A) volume 0 N :=
      concave_intervalIntegrable (Nat.cast_nonneg N)
        (hconc.subset (Icc_subset_Icc le_rfl hNT) (convex_Icc _ _))
    have h2 : IntervalIntegrable (hwidth A) volume N T :=
      concave_intervalIntegrable hNT
        (hconc.subset (Icc_subset_Icc (Nat.cast_nonneg N) le_rfl) (convex_Icc _ _))
    rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
    have : 0 ≤ ∫ t in (N : ℝ)..T, hwidth A t :=
      intervalIntegral.integral_nonneg hNT fun t ht =>
        hwidth_nonneg hc hab ((mem_axis_iff hc hab hne _).2
          ⟨(Nat.cast_nonneg N).trans ht.1, ht.2⟩)
    linarith
  have hcast : ((N + 1 : ℕ) : ℝ) = N + 1 := by push_cast; ring
  rw [hcast] at hcount
  linarith

end

end LatticeVolumeInterpolation
