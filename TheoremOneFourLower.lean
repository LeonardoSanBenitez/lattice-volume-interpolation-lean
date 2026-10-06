import TheoremOneFourCore
import Davenport
import Mathlib.Analysis.Convex.Deriv

/-!
# The lower counting core of Theorem 1.4

Catalog item `theorem_1_4_lower_bound`, the part of the proof after the reductions. For a compact
convex anti-blocking `A ⊆ ℝ^2` of height `T` and bottom width `a = f(0)`, under the diagonal
`x_1 + x_2 ≤ a`: `G(int A) ≥ vol(A) - a - T/2` (`ncard_interior_ge_core_lower`).

The paper assumes `f` differentiable and says that otherwise `f` can be approximated. Here `f'`
is the right derivative `d`, which exists at every interior point of `[0, T]` because `f` is
concave (Formalization decision 7 (b)); the paper's steps then go through with the slope
inequalities of concave functions:

* `∫_i^{i+1} f ≤ f(i) + d(i)/2` (Lemma 5.2, upper bound, with a right derivative);
* `∫_N^T f ≤ f(N) + (T - N) d(N)/2`, which needs `d(N) ≤ 0` and `f(T) ≥ 0`;
* `-d(i) ≥ f(i-1) - f(i)` and `(T - N)(-d(N)) ≥ f(N-1) - f(T-1)`, by comparing the right
  derivative with secant slopes and using that it decreases.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LatticeVolumeInterpolation

noncomputable section

/-- The right derivative of a concave function, computed through its convex negative. -/
def rdv (f : ℝ → ℝ) (x : ℝ) : ℝ := -derivWithin (-f) (Ioi x) x

section RightDeriv

variable {f : ℝ → ℝ} {T : ℝ} (hf : ConcaveOn ℝ (Icc 0 T) f)
include hf

theorem hasDerivWithinAt_rdv {x : ℝ} (hx : x ∈ Ioo 0 T) :
    HasDerivWithinAt f (rdv f x) (Ioi x) x := by
  have hint : x ∈ interior (Icc 0 T) := by rwa [interior_Icc]
  have h := hf.neg.hasDerivWithinAt_rightDeriv_of_mem_interior hint
  have h2 := h.neg
  rw [neg_neg] at h2
  exact h2

theorem rdv_antitone {x y : ℝ} (hx : x ∈ Ioo 0 T) (hy : y ∈ Ioo 0 T) (hxy : x ≤ y) :
    rdv f y ≤ rdv f x := by
  have hm := hf.neg.monotoneOn_rightDeriv (by rwa [interior_Icc]) (by rwa [interior_Icc]) hxy
  simp only [rdv, neg_le_neg_iff]
  exact hm

/-- The secant slope over `[a, b]` is at least the right derivative at `b`. -/
theorem rdv_le_slope {a b : ℝ} (ha : a ∈ Icc 0 T) (hb : b ∈ Ioo 0 T) (hab : a < b) :
    rdv f b ≤ (f b - f a) / (b - a) := by
  have hint : b ∈ interior (Icc 0 T) := by rwa [interior_Icc]
  have hdiff := (hf.neg.hasDerivWithinAt_leftDeriv_of_mem_interior hint).differentiableWithinAt
  have h1 := hf.neg.slope_le_leftDeriv ha (Ioo_subset_Icc_self hb) hab hdiff
  have h2 := hf.neg.leftDeriv_le_rightDeriv_of_mem_interior hint
  rw [slope_def_field] at h1
  simp only [Pi.neg_apply] at h1
  have : ((-f b) - (-f a)) / (b - a) = -((f b - f a) / (b - a)) := by ring
  rw [this] at h1
  simp only [rdv]
  linarith

/-- The right derivative at `x` is at least the secant slope over `[x, y]`. -/
theorem slope_le_rdv {x y : ℝ} (hx : x ∈ Ioo 0 T) (hy : y ∈ Icc 0 T) (hxy : x < y) :
    (f y - f x) / (y - x) ≤ rdv f x := by
  have h := hf.slope_le_of_hasDerivWithinAt_Ioi (Ioo_subset_Icc_self hx) hy hxy
    (hasDerivWithinAt_rdv hf hx)
  rwa [slope_def_field] at h

end RightDeriv

variable {A : Set (Fin 2 → ℝ)}

/-- Points strictly inside a section strictly below the top are interior. -/
theorem pt_mem_interior (hc : IsCompact A) (hconv : Convex ℝ A) (hab : IsAntiBlocking A)
    (hne : A.Nonempty) {s t : ℝ} (ht : t ∈ Ioo 0 (pheight A)) (hs : 0 < s)
    (hsf : s < hwidth A t) : pt s t ∈ interior A := by
  have hconc := concaveOn_hwidth hc hconv hab hne
  have hcont : ContinuousAt (hwidth A) t := by
    have h := hconc.continuousOn_interior
    rw [interior_Icc] at h
    exact h.continuousAt (Ioo_mem_nhds ht.1 ht.2)
  set ε := (hwidth A t - s) / 2 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  obtain ⟨δ₁, hδ₁, hδ₁f⟩ := Metric.continuousAt_iff.1 hcont ε hεpos
  set δ := min (min δ₁ ε) (min s (min t (pheight A - t))) with hδ
  have hδpos : 0 < δ := by
    simp only [hδ, lt_min_iff]; exact ⟨⟨hδ₁, hεpos⟩, hs, ht.1, by linarith [ht.2]⟩
  refine mem_interior_iff_mem_nhds.2 (Metric.mem_nhds_iff.2 ⟨δ, hδpos, fun y hy => ?_⟩)
  rw [Metric.mem_ball, dist_pi_lt_iff hδpos] at hy
  have hy0 := hy 0
  have hy1 := hy 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Real.dist_eq] at hy0 hy1
  rw [abs_lt] at hy0 hy1
  have hδle : δ ≤ δ₁ ∧ δ ≤ ε ∧ δ ≤ s ∧ δ ≤ t ∧ δ ≤ pheight A - t := by
    simp only [hδ, min_le_iff, le_refl, true_or, or_true, and_self]
  obtain ⟨h1, h2, h3, h4, h5⟩ := hδle
  have hyt : y 1 ∈ Ioo 0 (pheight A) := ⟨by linarith, by linarith⟩
  have hfy : hwidth A t - ε < hwidth A (y 1) := by
    have := hδ₁f (show dist (y 1) t < δ₁ by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    rw [Real.dist_eq, abs_lt] at this
    linarith [this.1]
  have hax : pt 0 (y 1) ∈ A := (mem_axis_iff hc hab hne _).2 (Ioo_subset_Icc_self hyt)
  have hsecEq := hsec_eq_Icc hc hab hax
  have hmem : y 0 ∈ hsec A (y 1) := by
    rw [hsecEq]; constructor <;> linarith
  rw [← pt_eta y]; exact hmem

/-- The lattice points of `int A` on the lines `x_2 = j + 1`, `j < N`, with `N < T`. -/
theorem sum_le_ncard_interior (hc : IsCompact A) (hconv : Convex ℝ A) (hab : IsAntiBlocking A)
    (hne : A.Nonempty) {N : ℕ} (hN : (N : ℝ) < pheight A) :
    ∑ j ∈ Finset.range N, (hwidth A ((j : ℝ) + 1) - 1) ≤
      ((DiscreteMinkowski.latticePoints (interior A) (standardIntegerLattice 2)).ncard : ℝ) := by
  classical
  set S : Finset (Fin 2 → ℝ) := (Finset.range N).biUnion fun j =>
    (Finset.Ioo 0 ⌈hwidth A ((j : ℝ) + 1)⌉₊).image fun k : ℕ => pt (k : ℝ) ((j : ℝ) + 1)
  have hsub : (S : Set (Fin 2 → ℝ)) ⊆
      DiscreteMinkowski.latticePoints (interior A) (standardIntegerLattice 2) := by
    intro z hz
    simp only [S, Finset.coe_biUnion, Finset.coe_range, Finset.coe_image, Finset.coe_Ioo,
      mem_iUnion, mem_image, mem_Ioo, mem_Iio, exists_prop] at hz
    obtain ⟨j, hjN, k, ⟨hk0, hkf⟩, rfl⟩ := hz
    have hjN' : (j : ℝ) + 1 ≤ N := by exact_mod_cast hjN
    refine ⟨pt_mem_interior hc hconv hab hne ⟨by positivity, by linarith⟩
      (by exact_mod_cast hk0) (Nat.lt_ceil.1 hkf), ?_⟩
    exact (mem_standardIntegerLattice_iff 2 _).2
      ⟨![k, j + 1], fun i => by fin_cases i <;> simp⟩
  have hfin : (DiscreteMinkowski.latticePoints (interior A) (standardIntegerLattice 2)).Finite :=
    DiscreteMinkowski.finite_inter_lattice (hc.isBounded.subset interior_subset) _
  have hcard : S.card ≤
      (DiscreteMinkowski.latticePoints (interior A) (standardIntegerLattice 2)).ncard := by
    rw [← Set.ncard_coe_finset S]; exact Set.ncard_le_ncard hsub hfin
  have hdisj : (↑(Finset.range N) : Set ℕ).PairwiseDisjoint fun j =>
      (Finset.Ioo 0 ⌈hwidth A ((j : ℝ) + 1)⌉₊).image fun k : ℕ => pt (k : ℝ) ((j : ℝ) + 1) := by
    intro i _ j _ hij
    refine Finset.disjoint_left.2 fun z hz hz' => hij ?_
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hz
    obtain ⟨l, -, hl⟩ := Finset.mem_image.1 hz'
    have := congrFun hl 1
    simp at this
    exact_mod_cast this.symm
  have hScard : S.card = ∑ j ∈ Finset.range N, (⌈hwidth A ((j : ℝ) + 1)⌉₊ - 1) := by
    rw [Finset.card_biUnion hdisj]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.card_image_of_injective _ (fun k l h => by
      have := congrFun h 0; simpa using this), Nat.card_Ioo, Nat.sub_zero]
  calc ∑ j ∈ Finset.range N, (hwidth A ((j : ℝ) + 1) - 1)
      ≤ ∑ j ∈ Finset.range N, ((⌈hwidth A ((j : ℝ) + 1)⌉₊ - 1 : ℕ) : ℝ) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rcases Nat.eq_zero_or_pos ⌈hwidth A ((j : ℝ) + 1)⌉₊ with h0 | hpos
        · rw [h0]; simp only [Nat.zero_sub, Nat.cast_zero]
          have := Nat.ceil_eq_zero.1 h0; linarith
        · rw [Nat.cast_sub hpos, Nat.cast_one]
          linarith [Nat.le_ceil (hwidth A ((j : ℝ) + 1))]
    _ = (S.card : ℝ) := by rw [hScard]; push_cast; rfl
    _ ≤ _ := by exact_mod_cast hcard

/-- The unit strips `[0, 1], ..., [k, k + 1]`: by the diagonal on `[0, 1]` and Lemma 5.2 with
`f'(i) ≤ f(i) - f(i-1)` on the others,
`∫_0^{k+1} f ≤ a - 1/2 + ∑_{j<k} f(j+1) + (f(k) - f(0))/2`. -/
theorem integral_le_strips {f : ℝ → ℝ} {T a : ℝ} (hf : ConcaveOn ℝ (Icc 0 T) f)
    (hdiag : ∀ t ∈ Icc 0 T, f t ≤ a - t) :
    ∀ k : ℕ, (k : ℝ) + 1 < T →
      ∫ t in (0 : ℝ)..((k : ℝ) + 1), f t ≤
        a - 1 / 2 + ∑ j ∈ Finset.range k, f ((j : ℝ) + 1) + (f k - f 0) / 2
  | 0, hT => by
    simp only [Nat.cast_zero, zero_add, Finset.range_zero, Finset.sum_empty, sub_self, zero_div,
      add_zero]
    have hT' : (1 : ℝ) ≤ T := by simpa using hT.le
    have hle : ∫ t in (0 : ℝ)..1, f t ≤ ∫ t in (0 : ℝ)..1, (a + (-1) * (t - 0)) := by
      refine intervalIntegral.integral_mono_on zero_le_one ?_ (intervalIntegrable_affine a (-1))
        fun t ht => ?_
      · exact concave_intervalIntegrable zero_le_one
          (hf.subset (Icc_subset_Icc le_rfl hT') (convex_Icc _ _))
      · have := hdiag t ⟨ht.1, ht.2.trans hT'⟩; linarith
    have hval := integral_affine_from_left (a := 0) (b := 1) a (-1)
    linarith
  | k + 1, hT => by
    have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hcast] at hT ⊢
    have hT' : (k : ℝ) + 1 < T := by linarith
    have ih := integral_le_strips hf hdiag k hT'
    have hx : (k : ℝ) + 1 ∈ Ioo 0 T := ⟨by positivity, hT'⟩
    have hsub : ConcaveOn ℝ (Icc ((k : ℝ) + 1) ((k : ℝ) + 1 + 1)) f :=
      hf.subset (Icc_subset_Icc hx.1.le hT.le) (convex_Icc _ _)
    have htan := concave_integral_le_tangent (by linarith) hsub (hasDerivWithinAt_rdv hf hx)
    rw [show (k : ℝ) + 1 + 1 - ((k : ℝ) + 1) = 1 by ring, one_mul, one_mul] at htan
    have hsl := rdv_le_slope hf (a := (k : ℝ)) ⟨Nat.cast_nonneg k, by linarith⟩ hx
      (by linarith)
    rw [show (k : ℝ) + 1 - k = 1 by ring, div_one] at hsl
    have hint1 : IntervalIntegrable f volume 0 ((k : ℝ) + 1) :=
      concave_intervalIntegrable hx.1.le (hf.subset (Icc_subset_Icc le_rfl hT'.le)
        (convex_Icc _ _))
    have hint2 : IntervalIntegrable f volume ((k : ℝ) + 1) ((k : ℝ) + 1 + 1) :=
      concave_intervalIntegrable (by linarith) hsub
    rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2, Finset.sum_range_succ]
    linarith

/-- **The lower counting core**: `G(int A) ≥ vol(A) - a - T/2`, with `vol(A) = ∫_0^T f`. -/
theorem ncard_interior_ge_core_lower (hc : IsCompact A) (hconv : Convex ℝ A)
    (hab : IsAntiBlocking A) (hne : A.Nonempty) (hdiag : ∀ x ∈ A, x 0 + x 1 ≤ hwidth A 0) :
    (∫ t in (0 : ℝ)..pheight A, hwidth A t) - hwidth A 0 - pheight A / 2 ≤
      ((DiscreteMinkowski.latticePoints (interior A) (standardIntegerLattice 2)).ncard : ℝ) := by
  set T := pheight A with hTdef
  have hT0 : 0 ≤ T := pheight_nonneg hc hab hne
  have hconc : ConcaveOn ℝ (Icc 0 T) (hwidth A) := concaveOn_hwidth hc hconv hab hne
  have hdiag' : ∀ t ∈ Icc 0 T, hwidth A t ≤ hwidth A 0 - t := fun t ht =>
    hwidth_le_diag hc hdiag ((mem_axis_iff hc hab hne t).2 ht)
  have hnn : ∀ t ∈ Icc 0 T, 0 ≤ hwidth A t := fun t ht =>
    hwidth_nonneg hc hab ((mem_axis_iff hc hab hne t).2 ht)
  have hG0 : (0 : ℝ) ≤
      ((DiscreteMinkowski.latticePoints (interior A) (standardIntegerLattice 2)).ncard : ℝ) :=
    Nat.cast_nonneg _
  have ha0 : 0 ≤ hwidth A 0 := hnn 0 ⟨le_rfl, hT0⟩
  have hintT : IntervalIntegrable (hwidth A) volume 0 T := concave_intervalIntegrable hT0 hconc
  by_cases hT1 : T ≤ 1
  · have hle : ∫ t in (0 : ℝ)..T, hwidth A t ≤ ∫ t in (0 : ℝ)..T, hwidth A 0 :=
      intervalIntegral.integral_mono_on hT0 hintT intervalIntegrable_const fun t ht => by
        linarith [hdiag' t ht, ht.1]
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hle
    have : T * hwidth A 0 ≤ hwidth A 0 := mul_le_of_le_one_left ha0 hT1
    linarith
  push Not at hT1
  -- `N = ⌈T⌉ - 1 = k + 1`, so `N < T ≤ N + 1`
  have hc2 : 2 ≤ ⌈T⌉₊ := by
    have : 1 < ⌈T⌉₊ := Nat.lt_ceil.2 (by exact_mod_cast hT1)
    omega
  set k := ⌈T⌉₊ - 2 with hk
  have hkc : ((k : ℝ) + 1) + 1 = (⌈T⌉₊ : ℝ) := by
    have : k + 2 = ⌈T⌉₊ := by omega
    rw [← this]; push_cast; ring
  have hxT : (k : ℝ) + 1 < T := by
    have := Nat.ceil_lt_add_one hT0; linarith
  have hTx : T ≤ (k : ℝ) + 1 + 1 := by rw [hkc]; exact Nat.le_ceil T
  have hx : (k : ℝ) + 1 ∈ Ioo 0 T := ⟨by positivity, hxT⟩
  have hδ : 0 < T - ((k : ℝ) + 1) := by linarith
  -- the strips up to `N`
  have hstrips := integral_le_strips hconc hdiag' k hxT
  -- the last piece `[N, T]`
  have hsubN : ConcaveOn ℝ (Icc ((k : ℝ) + 1) T) (hwidth A) :=
    hconc.subset (Icc_subset_Icc hx.1.le le_rfl) (convex_Icc _ _)
  have htan := concave_integral_le_tangent hxT.le hsubN (hasDerivWithinAt_rdv hconc hx)
  have hslT := slope_le_rdv hconc hx ⟨hT0, le_rfl⟩ hxT
  rw [div_le_iff₀ hδ] at hslT
  have hfT := hnn T ⟨hT0, le_rfl⟩
  have hfN := hnn _ ⟨hx.1.le, hxT.le⟩
  have hu : 0 ≤ hwidth A ((k : ℝ) + 1) +
      (T - ((k : ℝ) + 1)) * rdv (hwidth A) ((k : ℝ) + 1) / 2 := by nlinarith
  have hlast := mul_le_mul_of_nonneg_right (show T - ((k : ℝ) + 1) ≤ 1 by linarith) hu
  -- the bracket: `(T - N)(-f'(N)) ≥ f(N-1) - f(T-1)`
  have hT1' : T - 1 ∈ Ioo 0 T := ⟨by linarith, by linarith⟩
  have hsl2 := rdv_le_slope hconc (a := (k : ℝ)) ⟨Nat.cast_nonneg k, by linarith⟩ hT1'
    (by linarith)
  rw [show T - 1 - (k : ℝ) = T - ((k : ℝ) + 1) by ring, le_div_iff₀ hδ] at hsl2
  have hanti := rdv_antitone hconc hT1' hx (by linarith)
  have hanti' := mul_le_mul_of_nonneg_left hanti hδ.le
  have hfT1 := hdiag' (T - 1) ⟨hT1'.1.le, hT1'.2.le⟩
  -- assemble
  have hint1 : IntervalIntegrable (hwidth A) volume 0 ((k : ℝ) + 1) :=
    concave_intervalIntegrable hx.1.le (hconc.subset (Icc_subset_Icc le_rfl hxT.le)
      (convex_Icc _ _))
  have hint2 : IntervalIntegrable (hwidth A) volume ((k : ℝ) + 1) T :=
    concave_intervalIntegrable hxT.le hsubN
  rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
  have hcount := sum_le_ncard_interior hc hconv hab hne (N := k + 1) (by push_cast; exact hxT)
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    Finset.sum_range_succ] at hcount
  push_cast at hcount
  nlinarith

end

end LatticeVolumeInterpolation
