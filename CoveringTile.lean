import PropOneSix
import Mathlib.Order.Disjointed

/-!
# Proposition 1.6, Eq. (1.15), by the paper's tile

Catalog item `proposition_1_6_upper_bound`, by the paper's route (Sec. 4, proof of
Proposition 1.6). For a covering scale `r` (so `r K + ℤ^n = ℝ^n`) the paper builds a measurable
`S ⊆ r K` whose lattice translates are disjoint and which has volume `1`:

* `P = [0, 1)^n`; finitely many translates `x_1 + r K, ..., x_m + r K` with `x_i ∈ ℤ^n` cover `P`;
* `P_i = (P \ ⋃_{j<i} P_j) ∩ (x_i + r K)` and `S = ⋃_i (P_i - x_i)`.

Then `G(K) = vol((K ∩ ℤ^n) + S) ≤ vol(K + r K) = (1 + r)^n vol(K)`.

The paper works at `r = μ(K)` and asserts that `μ(K)` is a minimum; here the tile is built at
every covering scale `r > μ(K)` and the bound passes to the limit, as in `PropOneSix.lean`.
The paper's pieces are interiorly disjoint; taking `P` half-open makes them disjoint, so no
null sets need to be discarded.
-/

open MeasureTheory Set Module Filter Topology
open scoped ENNReal Pointwise

namespace LatticeVolumeInterpolation

noncomputable section

variable {n : ℕ}

/-- Two points of `[0, 1)^n` that differ by a lattice vector are equal. -/
theorem eq_of_mem_unitCubeIco_of_sub_mem {p p' : Fin n → ℝ} (hp : p ∈ unitCubeIco n)
    (hp' : p' ∈ unitCubeIco n) (h : p - p' ∈ standardIntegerLattice n) : p = p' := by
  rw [unitCubeIco, ZSpan.fundamentalDomain_pi_basisFun] at hp hp'
  obtain ⟨w, hw⟩ := (mem_standardIntegerLattice_iff n _).1 h
  funext i
  have hi : 0 ≤ p i ∧ p i < 1 := hp i (mem_univ i)
  have hi' : 0 ≤ p' i ∧ p' i < 1 := hp' i (mem_univ i)
  have hwi := hw i
  simp only [Pi.sub_apply] at hwi
  have hlt : ((w i : ℤ) : ℝ) < 1 := by rw [← hwi]; linarith [hi.1, hi'.2]
  have hgt : (-1 : ℝ) < ((w i : ℤ) : ℝ) := by rw [← hwi]; linarith [hi.2, hi'.1]
  have h0 : w i = 0 := by
    have h1 : w i < 1 := by exact_mod_cast hlt
    have h2 : -1 < w i := by exact_mod_cast hgt
    omega
  rw [h0, Int.cast_zero, sub_eq_zero] at hwi
  exact hwi

theorem image_sub_eq_vadd (A : Set (Fin n → ℝ)) (c : Fin n → ℝ) :
    (fun p => p - c) '' A = (-c) +ᵥ A := by
  rw [← Set.image_vadd]
  congr 1
  funext p
  rw [vadd_eq_add, sub_eq_add_neg, add_comm]

/-- **The tile.** At a covering scale `r` there is a measurable `S ⊆ r K` of volume `1` whose
differences meet `ℤ^n` only at `0`. -/
theorem exists_tile {K : Set (Fin n → ℝ)} (hKcpt : IsCompact K) {r : ℝ}
    (hr : r ∈ coveringSet K) :
    ∃ S : Set (Fin n → ℝ), MeasurableSet S ∧ S ⊆ r • K ∧ volume S = 1 ∧
      ∀ d ∈ S - S, d ∈ (standardIntegerLattice n : Set (Fin n → ℝ)) → d = 0 := by
  classical
  set P := unitCubeIco n with hP
  set rK := r • K with hrK
  have hrKc : IsCompact rK := hKcpt.smul r
  -- the finitely many lattice translates of `r K` that meet `P`
  set X := {x : Fin n → ℝ | x ∈ standardIntegerLattice n ∧ ((x +ᵥ rK) ∩ P).Nonempty} with hX
  have hXfin : X.Finite := by
    have hb : Bornology.IsBounded (P - rK) := by
      have hPb : Bornology.IsBounded P := by
        rw [hP, unitCubeIco, ZSpan.fundamentalDomain_pi_basisFun]
        exact (Metric.isBounded_Icc (0 : Fin n → ℝ) 1).subset fun y hy =>
          ⟨fun i => (hy i (mem_univ i)).1, fun i => (hy i (mem_univ i)).2.le⟩
      exact hPb.sub hrKc.isBounded
    refine (DiscreteMinkowski.finite_inter_lattice hb (standardIntegerLattice n)).subset ?_
    rintro x ⟨hxΛ, ⟨y, ⟨k, hk, rfl⟩, hyP⟩⟩
    refine ⟨⟨x +ᵥ k, hyP, k, hk, ?_⟩, hxΛ⟩
    simp [vadd_eq_add]
  set m := hXfin.toFinset.card
  set e := hXfin.toFinset.equivFin
  set x : ℕ → (Fin n → ℝ) := fun i => if h : i < m then (e.symm ⟨i, h⟩ : Fin n → ℝ) else 0
  have hxX : ∀ i, i < m → x i ∈ X := by
    intro i hi
    simp only [x, dif_pos hi]
    exact (hXfin.mem_toFinset).1 (e.symm ⟨i, hi⟩).2
  set f : ℕ → Set (Fin n → ℝ) := fun i => if i < m then P ∩ (x i +ᵥ rK) else ∅ with hf
  set D := disjointed f
  have hfm : ∀ i, MeasurableSet (f i) := by
    intro i
    simp only [hf]
    split_ifs
    · exact (measurableSet_unitCubeIco n).inter (hrKc.vadd (x i)).isClosed.measurableSet
    · exact MeasurableSet.empty
  have hDm : ∀ i, MeasurableSet (D i) := MeasurableSet.disjointed hfm
  have hDP : ∀ i, D i ⊆ P := fun i => (disjointed_subset f i).trans (by
    simp only [hf]; split_ifs
    · exact inter_subset_left
    · exact empty_subset _)
  have hDrK : ∀ i p, p ∈ D i → p - x i ∈ rK := by
    intro i p hp
    have hpf := disjointed_subset f i hp
    simp only [hf] at hpf
    split_ifs at hpf with hi
    · obtain ⟨k, hk, rfl⟩ := hpf.2
      simpa [vadd_eq_add] using hk
    · exact absurd hpf (Set.notMem_empty _)
  -- the pieces of `P` cover it
  have hcover : ⋃ i, D i = P := by
    rw [iUnion_disjointed]
    refine Subset.antisymm (iUnion_subset fun i => ?_) fun p hp => ?_
    · simp only [hf]; split_ifs
      · exact inter_subset_left
      · exact empty_subset _
    · obtain ⟨z, hz, hpz⟩ := hr.2 p
      have hzX : z ∈ X := ⟨hz, ⟨p, ⟨p - z, hpz, by simp [vadd_eq_add]⟩, hp⟩⟩
      have hzmem : z ∈ hXfin.toFinset := (hXfin.mem_toFinset).2 hzX
      set i := (e ⟨z, hzmem⟩ : ℕ)
      have hi : i < m := (e ⟨z, hzmem⟩).2
      have hxi : x i = z := by
        simp only [x, dif_pos hi]
        have : (⟨i, hi⟩ : Fin m) = e ⟨z, hzmem⟩ := Fin.ext rfl
        rw [this, Equiv.symm_apply_apply]
      refine mem_iUnion.2 ⟨i, ?_⟩
      simp only [hf, if_pos hi]
      exact ⟨hp, ⟨p - z, hpz, by rw [hxi]; simp [vadd_eq_add]⟩⟩
  -- the tile
  set S := ⋃ i, (fun p => p - x i) '' D i with hS
  have hpm : ∀ i, MeasurableSet ((fun p => p - x i) '' D i) := fun i => by
    rw [image_sub_eq_vadd]; exact (hDm i).const_vadd _
  have hSm : MeasurableSet S := MeasurableSet.iUnion hpm
  have hSrK : S ⊆ rK := iUnion_subset fun i => by
    rintro _ ⟨p, hp, rfl⟩; exact hDrK i p hp
  -- the shifted pieces are disjoint
  have hpiece : ∀ i j p q, p ∈ D i → q ∈ D j →
      p - x i - (q - x j) ∈ standardIntegerLattice n → i = j ∧ p = q := by
    intro i j p q hp hq hd
    have hxi : ∀ k, x k ∈ standardIntegerLattice n := fun k => by
      by_cases hk : k < m
      · exact (hxX k hk).1
      · simp only [x, dif_neg hk]; exact (standardIntegerLattice n).zero_mem
    have hpq : p - q ∈ standardIntegerLattice n := by
      have := (standardIntegerLattice n).add_mem hd ((standardIntegerLattice n).sub_mem (hxi i)
        (hxi j))
      convert this using 1; abel
    have hpeq := eq_of_mem_unitCubeIco_of_sub_mem (hDP i hp) (hDP j hq) hpq
    subst hpeq
    refine ⟨?_, rfl⟩
    by_contra hij
    exact (disjoint_disjointed f hij).le_bot ⟨hp, hq⟩
  have hvol : volume S = 1 := by
    have hdisj : Pairwise (Function.onFun Disjoint fun i => (fun p => p - x i) '' D i) := by
      intro i j hij
      refine Set.disjoint_left.2 ?_
      rintro _ ⟨p, hp, rfl⟩ ⟨q, hq, hpq⟩
      have h0 : p - x i - (q - x j) = 0 := by
        simp only at hpq; rw [hpq]; abel
      have := hpiece i j p q hp hq (by rw [h0]; exact (standardIntegerLattice n).zero_mem)
      exact hij this.1
    have hvi : ∀ i, volume ((fun p => p - x i) '' D i) = volume (D i) := fun i => by
      rw [image_sub_eq_vadd, measure_vadd]
    calc volume S = ∑' i, volume ((fun p => p - x i) '' D i) := measure_iUnion hdisj hpm
      _ = ∑' i, volume (D i) := by simp_rw [hvi]
      _ = volume (⋃ i, D i) := (measure_iUnion (disjoint_disjointed f) hDm).symm
      _ = 1 := by rw [hcover, volume_unitCubeIco]
  refine ⟨S, hSm, hSrK, hvol, ?_⟩
  rintro _ ⟨s, hs, s', hs', rfl⟩ hd
  obtain ⟨i, hi⟩ := mem_iUnion.1 hs
  obtain ⟨p, hp, rfl⟩ := hi
  obtain ⟨j, hj⟩ := mem_iUnion.1 hs'
  obtain ⟨q, hq, rfl⟩ := hj
  obtain ⟨rfl, rfl⟩ := hpiece i j p q hp hq hd
  exact sub_self _

/-- Eq. (1.15) at a covering scale `r`, by the paper's tile:
`G(K) = vol((K ∩ ℤ^n) + S) ≤ vol(K + r K) = (1 + r)^n vol(K)`. -/
theorem prop_1_6_upper_at_scale_tile {K : Set (Fin n → ℝ)} (hKcpt : IsCompact K)
    (hKb : DiscreteMinkowski.IsPaperConvexBody K) {r : ℝ} (hr : r ∈ coveringSet K) :
    ((DiscreteMinkowski.latticePoints K (standardIntegerLattice n)).ncard : ℝ≥0∞) ≤
      volume K * ENNReal.ofReal ((1 + r) ^ n) := by
  classical
  have hdim : finrank ℝ (Fin n → ℝ) = n := Module.finrank_fin_fun ℝ
  obtain ⟨S, hSm, hSrK, hSvol, hSavoid⟩ := exists_tile hKcpt hr
  set P := DiscreteMinkowski.latticePoints K (standardIntegerLattice n)
  have hPfin : P.Finite := DiscreteMinkowski.finite_inter_lattice hKcpt.isBounded _
  set Xs := hPfin.toFinset
  have hXΛ : ∀ w ∈ Xs, w ∈ standardIntegerLattice n := fun w hw =>
    ((hPfin.mem_toFinset).1 hw).2
  have hcount := DiscreteMinkowski.measure_biUnion_vadd volume hSm hSavoid hXΛ
  rw [hSvol, mul_one] at hcount
  have hsub : (⋃ w ∈ Xs, (w +ᵥ S)) ⊆ (1 + r) • K := by
    rw [hKb.2.1.add_smul zero_le_one hr.1.le, one_smul]
    refine iUnion₂_subset fun w hw => ?_
    rintro _ ⟨s, hs, rfl⟩
    exact Set.add_mem_add ((hPfin.mem_toFinset).1 hw).1 (hSrK hs)
  have hcard : (Xs.card : ℝ≥0∞) = (P.ncard : ℝ≥0∞) := by
    rw [Set.ncard_eq_toFinset_card P hPfin]
  rw [← hcard, ← hcount]
  calc volume (⋃ w ∈ Xs, (w +ᵥ S)) ≤ volume ((1 + r) • K) := measure_mono hsub
    _ = volume K * ENNReal.ofReal ((1 + r) ^ n) := by
        rw [Measure.addHaar_smul_of_nonneg volume (by linarith [hr.1] : (0 : ℝ) ≤ 1 + r), hdim,
          mul_comm]

/-- **Proposition 1.6, Eq. (1.15)**, by the paper's tile: `G(K) ≤ vol(K)(1 + μ(K))^n`. -/
theorem proposition_1_6_upper {K : Set (Fin n → ℝ)} (hKcpt : IsCompact K)
    (hKb : DiscreteMinkowski.IsPaperConvexBody K) :
    ((DiscreteMinkowski.latticePoints K (standardIntegerLattice n)).ncard : ℝ) ≤
      (volume K).toReal * (1 + coveringRadius K) ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using ncard_le_volume_dim_zero hKb
  have hKtop : volume K ≠ ⊤ := hKcpt.measure_lt_top.ne
  set f : ℝ → ℝ := fun r => (volume K).toReal * (1 + r) ^ n
  have hcont : Tendsto f (𝓝[>] coveringRadius K) (𝓝 (f (coveringRadius K))) :=
    ((continuous_const.mul ((continuous_const.add continuous_id).pow n)).tendsto _).mono_left
      nhdsWithin_le_nhds
  refine ge_of_tendsto hcont ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr' : coveringRadius K < r := hr
  have h := prop_1_6_upper_at_scale_tile hKcpt hKb (mem_coveringSet_of_lt hKcpt hKb hn hr')
  have hr0 : 0 ≤ (1 + r) ^ n := pow_nonneg (by linarith [coveringRadius_nonneg K]) n
  have := ENNReal.toReal_mono (ENNReal.mul_ne_top hKtop ENNReal.ofReal_ne_top) h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hr0, ENNReal.toReal_natCast] at this
  exact this

end

end LatticeVolumeInterpolation
