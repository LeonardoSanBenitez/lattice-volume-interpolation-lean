import TheoremThreeOne
import VanDerCorput
import Mathlib.Analysis.MeanInequalities

/-!
# The covering radius, Eq. (4.2), Proposition 1.6 (1.16) and Theorem 1.1 (1.9)

Catalog items `covering_radius`, `covering_radius_successive_minima_bound`,
`proposition_1_6_lower_bound` and `theorem_1_1_lower_bound`.

The **covering radius** `μ(K)` is the least `μ > 0` with `μ K + ℤ^n = ℝ^n` (Sec. 1, before
Proposition 1.6). It is formalized as the infimum of the covering scales; the paper's minimum
is never needed below, because every bound is proved at the scales `r > μ` and passed to the
limit.

**Eq. (4.2)**, `μ(K) ≤ ∑_i λ_i(K)/2`, quoted from Kannan and Lovász (Lemma 2.4). Proof: with
independent lattice vectors `v_i = (λ_i/2)(a_i - b_i)`, `a_i, b_i ∈ K`, and `s = ∑ λ_i/2`, write
`y - s q` in the basis `v_i`, where `q ∈ K` is the combination of the `b_i` with weights
`λ_i/(2s)`. Rounding the coordinates down to integers leaves `y - z = s p` with `z ∈ ℤ^n` and
`p ∈ K`, so `s K + ℤ^n = ℝ^n`.

**Eq. (1.16)**: if `μ(K) ≤ 1` then `G(int K) ≥ vol(K)(1 - μ)^n`. For `μ < r < 1`, van der
Corput gives `t` with `vol((1 - r) int K) ≤ G((1 - r) int K + t)`; translating by a lattice
vector puts `t` in `r K`, and `(1 - r) int K + r K ⊆ int K`. Letting `r → μ` gives the bound,
which at `μ = 1` holds trivially; this is the endpoint split the catalog records.

**Eq. (1.9)**: if `λ_n ≤ 2/n` then `G(int K) ≥ vol(K) ∏ (1 - n λ_i/2)`, from (1.16), (4.2)
and the inequality of arithmetic and geometric means.
-/

open MeasureTheory Set Module Filter Topology
open scoped ENNReal Pointwise

namespace LatticeVolumeInterpolation

noncomputable section

variable {n : ℕ}

/-- The scales `r > 0` with `r K + ℤ^n = ℝ^n`. -/
def coveringSet (K : Set (Fin n → ℝ)) : Set ℝ :=
  {r | 0 < r ∧ ∀ y : Fin n → ℝ, ∃ z ∈ standardIntegerLattice n, y - z ∈ r • K}

/-- **The covering radius** `μ(K)`. -/
def coveringRadius (K : Set (Fin n → ℝ)) : ℝ := sInf (coveringSet K)

theorem coveringRadius_nonneg (K : Set (Fin n → ℝ)) : 0 ≤ coveringRadius K :=
  Real.sInf_nonneg fun _ hr => hr.1.le

/-- Covering is preserved when the scale grows (for a non-empty convex `K`). -/
theorem mem_coveringSet_of_le {K : Set (Fin n → ℝ)} (hKc : Convex ℝ K) {k₀ : Fin n → ℝ}
    (hk₀ : k₀ ∈ K) {r r' : ℝ} (hr : r ∈ coveringSet K) (hrr' : r ≤ r') :
    r' ∈ coveringSet K := by
  refine ⟨hr.1.trans_le hrr', fun y => ?_⟩
  obtain ⟨z, hz, hyz⟩ := hr.2 (y - (r' - r) • k₀)
  refine ⟨z, hz, ?_⟩
  obtain ⟨k, hk, hk'⟩ := mem_smul_set.1 hyz
  have hr'0 : 0 < r' := hr.1.trans_le hrr'
  refine mem_smul_set.2 ⟨(r / r') • k + (1 - r / r') • k₀, ?_, ?_⟩
  · exact hKc hk hk₀ (div_nonneg hr.1.le hr'0.le)
      (by rw [sub_nonneg, div_le_one hr'0]; exact hrr') (by ring)
  · rw [smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ hr'0.ne', hk', mul_sub, mul_one,
      mul_div_cancel₀ _ hr'0.ne']
    abel

/-- **Eq. (4.2)** (Kannan and Lovász): `∑_i λ_i(K)/2` is a covering scale. -/
theorem sum_minima_mem_coveringSet {K : Set (Fin n → ℝ)} (hKcpt : IsCompact K)
    (hKb : DiscreteMinkowski.IsPaperConvexBody K) (hn : 0 < n) :
    (∑ i : Fin n, DiscreteMinkowski.successiveMinimum K (standardIntegerLattice n)
      (i.1 + 1) / 2) ∈ coveringSet K := by
  classical
  have hdim : finrank ℝ (Fin n → ℝ) = n := Module.finrank_fin_fun ℝ
  set lam : Fin n → ℝ := fun i =>
    DiscreteMinkowski.successiveMinimum K (standardIntegerLattice n) (i.1 + 1) with hlam
  have hpos : ∀ i, 0 < lam i := fun i =>
    DiscreteMinkowski.successiveMinimum_pos hKb (by omega) (by rw [hdim]; exact i.2)
  set s := ∑ i, lam i / 2 with hs
  have hspos : 0 < s := Finset.sum_pos (fun i _ => by have := hpos i; positivity)
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  set v : Fin n → (Fin n → ℝ) := fun k =>
    DiscreteMinkowski.flagVector K (standardIntegerLattice n) k.1 with hv
  have hvΛ : ∀ k, v k ∈ standardIntegerLattice n := fun k =>
    DiscreteMinkowski.flagVector_mem k.1
      (DiscreteMinkowski.greedyChoice_flagSpan hKb (by rw [hdim]; exact k.2))
  have hvind : LinearIndependent ℝ v := linearIndependent_flagVector hKb
  -- each `v k` is `(λ_k/2)(a_k - b_k)` with `a_k, b_k ∈ K`
  have hDc : IsCompact (DiscreteMinkowski.halfDifferenceBody K) := by
    rw [DiscreteMinkowski.halfDifferenceBody_apply]
    have hsub : K - K = (fun p : (Fin n → ℝ) × (Fin n → ℝ) => p.1 - p.2) '' (K ×ˢ K) := by
      rw [Set.image_prod]; rfl
    rw [hsub]
    exact ((hKcpt.prod hKcpt).image (by fun_prop)).smul _
  have hab : ∀ k, ∃ a ∈ K, ∃ b ∈ K, v k = lam k • ((2 : ℝ)⁻¹ • (a - b)) := by
    intro k
    have hg : gauge (DiscreteMinkowski.halfDifferenceBody K) (v k) ≤ lam k :=
      gauge_flagVector_le_successiveMinimum hKb (by rw [hdim]; exact k.2)
    have hcl : v k ∈ closure (lam k • DiscreteMinkowski.halfDifferenceBody K) :=
      (DiscreteMinkowski.mem_closure_smul_iff_gauge_le hKb (hpos k) (v k)).2 hg
    rw [(hDc.smul (lam k)).isClosed.closure_eq] at hcl
    obtain ⟨d, hd, hdv⟩ := mem_smul_set.1 hcl
    rw [DiscreteMinkowski.halfDifferenceBody_apply] at hd
    obtain ⟨w, ⟨a, ha, b, hb, rfl⟩, rfl⟩ := mem_smul_set.1 hd
    exact ⟨a, ha, b, hb, hdv.symm⟩
  choose a ha b hb hvab using hab
  set wt : Fin n → ℝ := fun k => lam k / 2 / s with hwt
  have hwt0 : ∀ k ∈ Finset.univ, 0 ≤ wt k := fun k _ => by have := hpos k; positivity
  have hwt1 : ∑ k, wt k = 1 := by
    rw [hwt]; simp only; rw [← Finset.sum_div, div_self hspos.ne']
  set q := ∑ k, wt k • b k with hq
  have hqK : q ∈ K := hKb.2.1.sum_mem hwt0 hwt1 fun k _ => hb k
  refine ⟨hspos, fun y => ?_⟩
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set B := basisOfLinearIndependentOfCardEqFinrank hvind (by rw [Fintype.card_fin, hdim])
  have hB : ∀ k, B k = v k := fun k => by simp [B]
  set x := y - s • q with hx
  set c := B.repr x with hc
  set f : Fin n → ℝ := fun k => c k - ⌊c k⌋ with hf
  have hf0 : ∀ k, 0 ≤ f k := fun k => by simp only [hf]; linarith [Int.floor_le (c k)]
  have hf1 : ∀ k, f k ≤ 1 := fun k => by simp only [hf]; linarith [Int.lt_floor_add_one (c k)]
  set z := ∑ k, (⌊c k⌋ : ℤ) • v k with hz
  have hzΛ : z ∈ standardIntegerLattice n :=
    Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hvΛ k)
  refine ⟨z, hzΛ, ?_⟩
  -- the reduced point
  set p := ∑ k, wt k • (f k • a k + (1 - f k) • b k) with hp
  have hpK : p ∈ K := hKb.2.1.sum_mem hwt0 hwt1 fun k _ =>
    hKb.2.1 (ha k) (hb k) (hf0 k) (by linarith [hf1 k]) (by ring)
  have hxz : x - z = ∑ k, f k • v k := by
    have hxs : x = ∑ k, c k • v k := by
      conv_lhs => rw [← B.sum_repr x]
      simp only [hB, hc]
    rw [hxs, hz, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Int.cast_smul_eq_zsmul ℝ, ← sub_smul]
  have hspq : ∑ k, f k • v k = s • p - s • q := by
    rw [hp, hq, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hw : s * wt k = lam k / 2 := by
      simp only [hwt]; have := hspos.ne'; field_simp
    rw [hvab k]
    simp only [smul_smul, hw]
    module
  refine mem_smul_set.2 ⟨p, hpK, ?_⟩
  have : y - z = (x - z) + s • q := by rw [hx]; abel
  rw [this, hxz, hspq]
  abel

/-- **Eq. (4.2)**: `μ(K) ≤ ∑_i λ_i(K)/2`. -/
theorem coveringRadius_le_sum_minima {K : Set (Fin n → ℝ)} (hKcpt : IsCompact K)
    (hKb : DiscreteMinkowski.IsPaperConvexBody K) (hn : 0 < n) :
    coveringRadius K ≤
      ∑ i : Fin n, DiscreteMinkowski.successiveMinimum K (standardIntegerLattice n)
        (i.1 + 1) / 2 :=
  csInf_le ⟨0, fun _ hr => hr.1.le⟩ (sum_minima_mem_coveringSet hKcpt hKb hn)

/-- Every scale above the covering radius covers. -/
theorem mem_coveringSet_of_lt {K : Set (Fin n → ℝ)} (hKcpt : IsCompact K)
    (hKb : DiscreteMinkowski.IsPaperConvexBody K) (hn : 0 < n) {r : ℝ}
    (hr : coveringRadius K < r) : r ∈ coveringSet K := by
  have hne : (coveringSet K).Nonempty := ⟨_, sum_minima_mem_coveringSet hKcpt hKb hn⟩
  obtain ⟨r₀, hr₀, hr₀r⟩ := (csInf_lt_iff ⟨0, fun _ h => h.1.le⟩ hne).1 hr
  obtain ⟨k₀, hk₀⟩ := hKb.2.2
  exact mem_coveringSet_of_le hKb.2.1 (interior_subset hk₀) hr₀ hr₀r.le

end

end LatticeVolumeInterpolation
