import Davenport
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Lemma 3.3: an anti-blocking body realizes its minima on the coordinate axes

Catalog item `lemma_3_3_minima_at_standard_basis`. For a compact anti-blocking convex body
`K ⊆ ℝ^n`, the coordinates can be permuted so that `|e_i|_{cs(K)} = λ_i(K)`, and then
`(2/λ_i(K)) e_i ∈ K`. Here `cs(K) = (K - K)/2`, `|·|_{cs(K)}` is its gauge, and the
permutation is the order in which the axis gauges `a_j = |e_j|_{cs(K)}` increase.

The paper's proof is recorded in the catalog as having two gaps: the coordinate projection of
a minimal vector need not lie in `K`, and the one-line minimality argument does not handle
repeated minima. The proof here keeps the paper's ingredients (projection onto coordinate
axes, the gauge, anti-blocking) and replaces the ordering step:

* zeroing coordinates never increases the gauge of `cs(K)`, because `K - K` is closed under
  it when `K` is anti-blocking (`gauge_zeroOn_le`); so a lattice vector `v` with `v_j ≠ 0`
  has `a_j ≤ |v|_{cs(K)}`;
* the first `i` sorted axes are independent lattice vectors of gauge at most the `i`-th
  smallest `a_j`, so `λ_i` is at most it;
* the first `i` vectors of a minimal flag span `i` dimensions, so their supports cover at
  least `i` coordinates, each with `a_j ≤ λ_i`; so the `i`-th smallest `a_j` is at most
  `λ_i`. This holds whatever the multiplicities of the minima.

For the second claim, `e_j / a_j = (p - q)/2` with `p, q ∈ K` (attained because `K` is
compact), so `p_j ≥ 2/a_j` and `(2/a_j) e_j ≤ p` coordinatewise, which puts it in `K`.
-/

open Set Module
open scoped Pointwise

namespace LatticeVolumeInterpolation

noncomputable section

variable {n : ℕ}

/-- Zeroing the coordinates in `J`. -/
def zeroOn (J : Finset (Fin n)) (x : Fin n → ℝ) : Fin n → ℝ := fun i => if i ∈ J then 0 else x i

theorem zeroOn_mem_of_antiBlocking {K : Set (Fin n → ℝ)} (hK : IsAntiBlocking K)
    (J : Finset (Fin n)) {x : Fin n → ℝ} (hx : x ∈ K) : zeroOn J x ∈ K := by
  refine hK.2 x hx _ (fun i => ?_) (fun i => ?_)
  · unfold zeroOn; split_ifs
    · exact le_rfl
    · exact hK.1 x hx i
  · unfold zeroOn; split_ifs
    · exact hK.1 x hx i
    · exact le_rfl

theorem zeroOn_smul_sub (J : Finset (Fin n)) (r : ℝ) (a b : Fin n → ℝ) :
    zeroOn J (r • (a - b)) = r • (zeroOn J a - zeroOn J b) := by
  funext i
  simp only [zeroOn, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  split_ifs <;> ring

/-- A dilate of `cs(K)` is closed under zeroing coordinates when `K` is anti-blocking. -/
theorem zeroOn_mem_smul_halfDifferenceBody {K : Set (Fin n → ℝ)} (hK : IsAntiBlocking K)
    (J : Finset (Fin n)) {r : ℝ} {x : Fin n → ℝ}
    (hx : x ∈ r • DiscreteMinkowski.halfDifferenceBody K) :
    zeroOn J x ∈ r • DiscreteMinkowski.halfDifferenceBody K := by
  obtain ⟨y, hy, rfl⟩ := mem_smul_set.1 hx
  rw [DiscreteMinkowski.halfDifferenceBody_apply] at hy
  obtain ⟨d, ⟨a, ha, b, hb, rfl⟩, rfl⟩ := mem_smul_set.1 hy
  refine mem_smul_set.2 ⟨(2 : ℝ)⁻¹ • (zeroOn J a - zeroOn J b), ?_, ?_⟩
  · rw [DiscreteMinkowski.halfDifferenceBody_apply]
    exact smul_mem_smul_set (sub_mem_sub (zeroOn_mem_of_antiBlocking hK J ha)
      (zeroOn_mem_of_antiBlocking hK J hb))
  · simp only [smul_smul]
    rw [zeroOn_smul_sub]

/-- **Zeroing coordinates does not increase the gauge of `cs(K)`.** -/
theorem gauge_zeroOn_le {K : Set (Fin n → ℝ)} (hKb : DiscreteMinkowski.IsPaperConvexBody K)
    (hK : IsAntiBlocking K) (J : Finset (Fin n)) (x : Fin n → ℝ) :
    gauge (DiscreteMinkowski.halfDifferenceBody K) (zeroOn J x) ≤
      gauge (DiscreteMinkowski.halfDifferenceBody K) x := by
  refine le_of_forall_gt_imp_ge_of_dense fun r hr => ?_
  have hr0 : 0 < r := lt_of_le_of_lt (gauge_nonneg _) hr
  have hx : x ∈ r • DiscreteMinkowski.halfDifferenceBody K :=
    DiscreteMinkowski.mem_smul_of_gauge_lt hKb hr
  exact DiscreteMinkowski.gauge_le_of_mem_smul hr0.le
    (zeroOn_mem_smul_halfDifferenceBody hK J hx)

/-- The gauge of `cs(K)` is absolutely homogeneous, `cs(K)` being symmetric. -/
theorem gauge_halfDifferenceBody_smul (K : Set (Fin n → ℝ)) (c : ℝ) (x : Fin n → ℝ) :
    gauge (DiscreteMinkowski.halfDifferenceBody K) (c • x) =
      |c| * gauge (DiscreteMinkowski.halfDifferenceBody K) x := by
  rcases le_or_gt 0 c with hc | hc
  · rw [gauge_smul_of_nonneg hc, abs_of_nonneg hc, smul_eq_mul]
  · have : c • x = -(|c| • x) := by
      rw [abs_of_neg hc, neg_smul, neg_neg]
    rw [this, gauge_neg (fun y hy => DiscreteMinkowski.neg_mem_halfDifferenceBody hy),
      gauge_smul_of_nonneg (abs_nonneg c), smul_eq_mul]

theorem zeroOn_erase_eq_single (j : Fin n) (v : Fin n → ℝ) :
    zeroOn (Finset.univ.erase j) v = v j • Pi.single j (1 : ℝ) := by
  funext i
  by_cases h : i = j
  · subst h
    simp only [zeroOn, Finset.mem_erase, ne_eq, not_true_eq_false, false_and, if_false,
      Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
  · have hi : i ∈ Finset.univ.erase j := Finset.mem_erase.2 ⟨h, Finset.mem_univ i⟩
    simp only [zeroOn, hi, if_true, Pi.smul_apply, Pi.single_eq_of_ne h, smul_eq_mul,
      mul_zero]

/-- **A lattice vector with a non-zero `j`-th coordinate bounds the `j`-th axis gauge.** -/
theorem axis_gauge_le_of_coord_ne_zero {K : Set (Fin n → ℝ)}
    (hKb : DiscreteMinkowski.IsPaperConvexBody K) (hK : IsAntiBlocking K)
    {v : Fin n → ℝ} (hv : v ∈ standardIntegerLattice n) {j : Fin n} (hvj : v j ≠ 0) :
    gauge (DiscreteMinkowski.halfDifferenceBody K) (Pi.single j 1) ≤
      gauge (DiscreteMinkowski.halfDifferenceBody K) v := by
  obtain ⟨w, hw⟩ := (mem_standardIntegerLattice_iff n v).1 hv
  have hwj : w j ≠ 0 := by
    intro h; apply hvj; rw [hw j, h, Int.cast_zero]
  have h1 : (1 : ℝ) ≤ |v j| := by
    rw [hw j, ← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hwj
  have hsm : gauge (DiscreteMinkowski.halfDifferenceBody K) (v j • Pi.single j (1 : ℝ)) =
      |v j| * gauge (DiscreteMinkowski.halfDifferenceBody K) (Pi.single j (1 : ℝ)) :=
    gauge_halfDifferenceBody_smul K (v j) (Pi.single j (1 : ℝ))
  have hle : gauge (DiscreteMinkowski.halfDifferenceBody K) (zeroOn (Finset.univ.erase j) v) ≤
      gauge (DiscreteMinkowski.halfDifferenceBody K) v := gauge_zeroOn_le hKb hK _ v
  rw [zeroOn_erase_eq_single, hsm] at hle
  have h2 : gauge (DiscreteMinkowski.halfDifferenceBody K) (Pi.single j (1 : ℝ)) ≤
      |v j| * gauge (DiscreteMinkowski.halfDifferenceBody K) (Pi.single j (1 : ℝ)) :=
    le_mul_of_one_le_left (gauge_nonneg _) h1
  exact h2.trans hle

/-- **The `k`-th vector of the minimal flag has gauge exactly `λ_{k+1}`.** The dependency
proves `λ_{k+1} ≤ |v_k|`; the reverse holds because at every admissible scale some lattice
point lies outside the `k`-dimensional flag span. -/
theorem gauge_flagVector_le_successiveMinimum {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {K : Set E} {Λ : Submodule ℤ E}
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (hK : DiscreteMinkowski.IsPaperConvexBody K)
    {k : ℕ} (hk : k < finrank ℝ E) :
    gauge (DiscreteMinkowski.halfDifferenceBody K) (DiscreteMinkowski.flagVector K Λ k) ≤
      DiscreteMinkowski.successiveMinimum K Λ (k + 1) := by
  rw [DiscreteMinkowski.successiveMinimum_eq_sInf]
  refine le_csInf (DiscreteMinkowski.minimaSet_nonempty hK hk) ?_
  rintro r ⟨hr0, hrank⟩
  by_contra hlt
  push Not at hlt
  have hsub : DiscreteMinkowski.scaledLatticeSpan K Λ r ≤ DiscreteMinkowski.flagSpan K Λ k := by
    refine Submodule.span_le.2 fun z hz => ?_
    by_contra hzn
    have hmin := DiscreteMinkowski.flagVector_gauge_min k
      (DiscreteMinkowski.greedyChoice_flagSpan hK hk) hz.2 hzn
    have hzr := DiscreteMinkowski.gauge_le_of_mem_smul hr0.le hz.1
    linarith
  have := Submodule.finrank_mono hsub
  rw [DiscreteMinkowski.finrank_flagSpan hK k hk.le] at this
  omega

/-- The vectors vanishing off a set `J` of coordinates. -/
def supportedOn (J : Finset (Fin n)) : Submodule ℝ (Fin n → ℝ) where
  carrier := {y | ∀ j, j ∉ J → y j = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' := fun hx hy j hj => by simp [hx j hj, hy j hj]
  smul_mem' := fun c x hx j hj => by simp [hx j hj]

/-- A subspace of vectors supported on `J` has dimension at most `|J|`. -/
theorem finrank_le_card_of_le_supportedOn (W : Submodule ℝ (Fin n → ℝ)) (J : Finset (Fin n))
    (hW : W ≤ supportedOn J) : finrank ℝ W ≤ J.card := by
  set φ : W →ₗ[ℝ] ({j // j ∈ J} → ℝ) :=
    (LinearMap.pi fun j : {j // j ∈ J} => LinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j.1)
      ∘ₗ W.subtype with hφ
  have hinj : Function.Injective φ := by
    intro x y hxy
    apply Subtype.ext
    funext j
    by_cases hj : j ∈ J
    · have := congrFun hxy ⟨j, hj⟩
      simpa [hφ] using this
    · rw [hW x.2 j hj, hW y.2 j hj]
  have h := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h

variable {K : Set (Fin n → ℝ)}

/-- The `j`-th axis gauge `a_j = |e_j|_{cs(K)}`. -/
abbrev axisGauge (K : Set (Fin n → ℝ)) (j : Fin n) : ℝ :=
  gauge (DiscreteMinkowski.halfDifferenceBody K) (Pi.single j (1 : ℝ))

/-- **At least `i` axes have gauge at most `λ_i`.** The first `i` vectors of the minimal flag
have gauge at most `λ_i` and span `i` dimensions, so their supports cover at least `i`
coordinates. -/
theorem le_card_axisGauge_le (hKb : DiscreteMinkowski.IsPaperConvexBody K)
    (hK : IsAntiBlocking K) {i : ℕ} (hi : i ≤ n) :
    i ≤ (Finset.univ.filter fun j =>
      axisGauge K j ≤ DiscreteMinkowski.successiveMinimum K (standardIntegerLattice n) i).card := by
  classical
  set Λ := standardIntegerLattice n
  set v := DiscreteMinkowski.flagVector K Λ
  have hdim : finrank ℝ (Fin n → ℝ) = n := Module.finrank_fin_fun ℝ
  set J := Finset.univ.filter fun j => ∃ k < i, v k j ≠ 0 with hJ
  have hvS : ∀ m, m < i → v m ∈ ((supportedOn J : Submodule ℝ (Fin n → ℝ)) : Set _) := by
    intro m hm j hj
    simp only [hJ, Finset.mem_filter, Finset.mem_univ, true_and, not_exists, not_and,
      not_not] at hj
    exact hj m hm
  have hflag : DiscreteMinkowski.flagSpan K Λ i ≤ supportedOn J := by
    have := DiscreteMinkowski.flagSpan_le_span (K := K) (Λ := Λ) i hvS
    rwa [Submodule.span_eq] at this
  have hrank : finrank ℝ (DiscreteMinkowski.flagSpan K Λ i) = i :=
    DiscreteMinkowski.finrank_flagSpan hKb i (by rw [hdim]; exact hi)
  have hiJ : i ≤ J.card := hrank ▸ finrank_le_card_of_le_supportedOn _ J hflag
  refine hiJ.trans (Finset.card_le_card fun j hj => ?_)
  simp only [hJ, Finset.mem_filter, Finset.mem_univ, true_and] at hj
  obtain ⟨k, hk, hvk⟩ := hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hkd : k < finrank ℝ (Fin n → ℝ) := by rw [hdim]; omega
  have hvΛ : v k ∈ Λ := DiscreteMinkowski.flagVector_mem k
    (DiscreteMinkowski.greedyChoice_flagSpan hKb hkd)
  have h1 : axisGauge K j ≤ gauge (DiscreteMinkowski.halfDifferenceBody K) (v k) :=
    axis_gauge_le_of_coord_ne_zero hKb hK hvΛ hvk
  have h2 : gauge (DiscreteMinkowski.halfDifferenceBody K) (v k) ≤
      DiscreteMinkowski.successiveMinimum K Λ (k + 1) :=
    gauge_flagVector_le_successiveMinimum hKb hkd
  have h3 : DiscreteMinkowski.successiveMinimum K Λ (k + 1) ≤
      DiscreteMinkowski.successiveMinimum K Λ i :=
    DiscreteMinkowski.successiveMinimum_mono_of_le_finrank hKb (by omega) (by rw [hdim]; exact hi)
  linarith

/-- **Order statistics.** If `a ∘ σ` is monotone and at least `i + 1` indices have `a_j ≤ t`,
then `a (σ i) ≤ t`. -/
theorem le_of_card_filter_le {a : Fin n → ℝ} {σ : Equiv.Perm (Fin n)} (hσ : Monotone (a ∘ σ))
    {t : ℝ} (i : Fin n) (h : i.1 + 1 ≤ (Finset.univ.filter fun j => a j ≤ t).card) :
    a (σ i) ≤ t := by
  classical
  by_contra hlt
  push Not at hlt
  have hsub : (Finset.univ.filter fun j => a j ≤ t) ⊆ (Finset.Iio i).map σ.toEmbedding := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    simp only [Finset.mem_map, Finset.mem_Iio, Equiv.toEmbedding_apply]
    refine ⟨σ.symm j, ?_, by simp⟩
    by_contra hk
    push Not at hk
    have := hσ hk
    simp only [Function.comp_apply, Equiv.apply_symm_apply] at this
    linarith
  have := Finset.card_le_card hsub
  rw [Finset.card_map, Fin.card_Iio] at this
  omega

/-- The axis point `(2/a_j) e_j` lies in `K`. -/
theorem axis_point_mem (hKc : IsCompact K) (hKb : DiscreteMinkowski.IsPaperConvexBody K)
    (hK : IsAntiBlocking K) (j : Fin n) :
    (2 / axisGauge K j) • (Pi.single j (1 : ℝ) : Fin n → ℝ) ∈ K := by
  set D := DiscreteMinkowski.halfDifferenceBody K with hD
  have hne : (Pi.single j (1 : ℝ) : Fin n → ℝ) ≠ 0 := by
    intro h; have := congrFun h j; simp at this
  have hpos : 0 < axisGauge K j := DiscreteMinkowski.gauge_pos_of_ne_zero hKb hne
  have hDc : IsCompact D := by
    rw [hD, DiscreteMinkowski.halfDifferenceBody_apply]
    have hsub : K - K = (fun p : (Fin n → ℝ) × (Fin n → ℝ) => p.1 - p.2) '' (K ×ˢ K) := by
      rw [Set.image_prod]; rfl
    rw [hsub]
    exact ((hKc.prod hKc).image (by fun_prop)).smul _
  have hcl : Pi.single j (1 : ℝ) ∈ closure (axisGauge K j • D) :=
    (DiscreteMinkowski.mem_closure_smul_iff_gauge_le hKb hpos (Pi.single j (1 : ℝ))).2 le_rfl
  rw [(hDc.smul (axisGauge K j)).isClosed.closure_eq] at hcl
  obtain ⟨d, hd, hdj⟩ := mem_smul_set.1 hcl
  rw [hD, DiscreteMinkowski.halfDifferenceBody_apply] at hd
  obtain ⟨w, ⟨p, hp, q, hq, rfl⟩, rfl⟩ := mem_smul_set.1 hd
  have hcoord := congrFun hdj j
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.single_eq_same] at hcoord
  have hq0 : 0 ≤ q j := hK.1 q hq j
  have hpj : 2 / axisGauge K j ≤ p j := by
    rw [div_le_iff₀ hpos]
    nlinarith
  refine hK.2 p hp _ (fun i => ?_) (fun i => ?_)
  · simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg (div_nonneg zero_le_two hpos.le) (by
      by_cases h : i = j
      · subst h; simp
      · simp [Pi.single_eq_of_ne h])
  · simp only [Pi.smul_apply, smul_eq_mul]
    by_cases h : i = j
    · subst h; simpa using hpj
    · simp only [Pi.single_eq_of_ne h, mul_zero]
      exact hK.1 p hp i

/-- **Lemma 3.3.** For a compact anti-blocking convex body, there is a permutation `σ` of the
coordinates with `|e_{σ(i)}|_{cs(K)} = λ_{i+1}(K)` and `(2/λ_{i+1}(K)) e_{σ(i)} ∈ K` for every
`i` (indices from `0`). -/
theorem lemma_3_3 (hKc : IsCompact K) (hKb : DiscreteMinkowski.IsPaperConvexBody K)
    (hK : IsAntiBlocking K) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i : Fin n,
      axisGauge K (σ i) =
          DiscreteMinkowski.successiveMinimum K (standardIntegerLattice n) (i.1 + 1) ∧
        (2 / DiscreteMinkowski.successiveMinimum K (standardIntegerLattice n) (i.1 + 1)) •
          Pi.single (σ i) (1 : ℝ) ∈ K := by
  classical
  set a := axisGauge K
  set σ := Tuple.sort a
  have hσ : Monotone (a ∘ σ) := Tuple.monotone_sort a
  refine ⟨σ, fun i => ?_⟩
  have hge : a (σ i) ≤
      DiscreteMinkowski.successiveMinimum K (standardIntegerLattice n) (i.1 + 1) :=
    le_of_card_filter_le hσ i (le_card_axisGauge_le hKb hK i.2)
  have hle : DiscreteMinkowski.successiveMinimum K (standardIntegerLattice n) (i.1 + 1) ≤
      a (σ i) := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hpos : 0 < a (σ i) + ε := by
      have := gauge_nonneg (s := DiscreteMinkowski.halfDifferenceBody K)
        (Pi.single (σ i) (1 : ℝ))
      linarith
    refine DiscreteMinkowski.successiveMinimum_le_of_finrank_gauge_lt hKb hpos ?_
    set b : {k // k ∈ Finset.Iic i} → (Fin n → ℝ) := fun k => Pi.single (σ k.1) (1 : ℝ)
    have hb : LinearIndependent ℝ b := by
      have hinj : Function.Injective (fun k : {k // k ∈ Finset.Iic i} => σ k.1) :=
        fun k l hkl => Subtype.ext (σ.injective hkl)
      have h := (Pi.basisFun ℝ (Fin n)).linearIndependent.comp _ hinj
      simpa [b, Function.comp_def] using h
    have hspan : Submodule.span ℝ (Set.range b) ≤ Submodule.span ℝ
        {x : Fin n → ℝ | x ∈ (standardIntegerLattice n : Set (Fin n → ℝ)) ∧
          gauge (DiscreteMinkowski.halfDifferenceBody K) x < a (σ i) + ε} := by
      refine Submodule.span_mono ?_
      rintro _ ⟨k, rfl⟩
      refine ⟨(mem_standardIntegerLattice_iff n _).2
        ⟨Pi.single (σ k.1) 1, fun l => ?_⟩, ?_⟩
      · by_cases h : l = σ k.1
        · subst h; simp [b]
        · simp [b, Pi.single_eq_of_ne h]
      · have hk : k.1 ≤ i := Finset.mem_Iic.1 k.2
        have := hσ hk
        simp only [Function.comp_apply] at this
        change a (σ k.1) < a (σ i) + ε
        linarith
    have hcard := finrank_span_eq_card hb
    rw [Fintype.card_coe, Fin.card_Iic] at hcard
    calc i.1 + 1 = finrank ℝ (Submodule.span ℝ (Set.range b)) := hcard.symm
      _ ≤ _ := Submodule.finrank_mono hspan
  have heq : a (σ i) =
      DiscreteMinkowski.successiveMinimum K (standardIntegerLattice n) (i.1 + 1) :=
    le_antisymm hge hle
  refine ⟨heq, ?_⟩
  rw [← heq]
  exact axis_point_mem hKc hKb hK (σ i)

end

end LatticeVolumeInterpolation
