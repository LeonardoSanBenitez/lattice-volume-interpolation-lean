import CoveringRadius

/-!
# Proposition 1.6, Eq. (1.16), and Theorem 1.1, Eq. (1.9)

Catalog items `proposition_1_6_lower_bound` and `theorem_1_1_lower_bound`; the argument is in
the header of `CoveringRadius.lean`.
-/

open MeasureTheory Set Module Filter Topology
open scoped ENNReal Pointwise

namespace LatticeVolumeInterpolation

noncomputable section

variable {n : ℕ}

/-- A convex body and its interior have the same volume (the boundary is null). -/
theorem volume_interior_eq {K : Set (Fin n → ℝ)} (hKc : Convex ℝ K) :
    volume (interior K) = volume K := by
  refine le_antisymm (measure_mono interior_subset) ?_
  calc volume K ≤ volume (closure K) := measure_mono subset_closure
    _ = volume (interior K ∪ frontier K) := by rw [closure_eq_interior_union_frontier]
    _ ≤ volume (interior K) + volume (frontier K) := measure_union_le _ _
    _ = volume (interior K) := by rw [hKc.addHaar_frontier volume, add_zero]

/-- Translating by a lattice vector does not change the lattice point count. -/
theorem ncard_latticePoints_translate (S : Set (Fin n → ℝ)) (t : Fin n → ℝ)
    {z : Fin n → ℝ} (hz : z ∈ standardIntegerLattice n) :
    (DiscreteMinkowski.latticePoints ((fun y => y + (t - z)) '' S)
      (standardIntegerLattice n)).ncard =
    (DiscreteMinkowski.latticePoints ((fun y => y + t) '' S) (standardIntegerLattice n)).ncard := by
  have himg : DiscreteMinkowski.latticePoints ((fun y => y + (t - z)) '' S)
      (standardIntegerLattice n) =
      (fun w => w - z) '' DiscreteMinkowski.latticePoints ((fun y => y + t) '' S)
        (standardIntegerLattice n) := by
    ext w
    simp only [DiscreteMinkowski.latticePoints_apply, mem_inter_iff, mem_image, SetLike.mem_coe]
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hw⟩
      refine ⟨y + t, ⟨⟨y, hy, rfl⟩, ?_⟩, by abel⟩
      have := (standardIntegerLattice n).add_mem hw hz
      convert this using 1; abel
    · rintro ⟨_, ⟨⟨y, hy, rfl⟩, hw⟩, rfl⟩
      exact ⟨⟨y, hy, by abel⟩, (standardIntegerLattice n).sub_mem hw hz⟩
  rw [himg, Set.ncard_image_of_injective _ (sub_left_injective)]

/-- In dimension `0` the space is a point, and `vol(K) ≤ 1 = G(int K)`. -/
theorem volume_le_ncard_interior_dim_zero {K : Set (Fin 0 → ℝ)}
    (hKb : DiscreteMinkowski.IsPaperConvexBody K) :
    (volume K).toReal ≤
      ((DiscreteMinkowski.latticePoints (interior K) (standardIntegerLattice 0)).ncard : ℝ) := by
  obtain ⟨x, hx⟩ := hKb.2.2
  have hx0 : x = 0 := Subsingleton.elim _ _
  have h0 : (0 : Fin 0 → ℝ) ∈ DiscreteMinkowski.latticePoints (interior K)
      (standardIntegerLattice 0) := ⟨hx0 ▸ hx, (standardIntegerLattice 0).zero_mem⟩
  have hfin : (DiscreteMinkowski.latticePoints (interior K) (standardIntegerLattice 0)).Finite :=
    Set.toFinite _
  have h1 : 1 ≤ (DiscreteMinkowski.latticePoints (interior K) (standardIntegerLattice 0)).ncard :=
    (Set.ncard_pos hfin).2 ⟨0, h0⟩
  have hvol : volume K ≤ 1 := by
    calc volume K ≤ volume (univ : Set (Fin 0 → ℝ)) := measure_mono (subset_univ K)
      _ = 1 := by rw [volume_pi, Measure.pi_of_empty]; simp
  calc (volume K).toReal ≤ 1 := ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hvol)
    _ ≤ _ := by exact_mod_cast h1

/-- Eq. (1.16) at a covering scale `r < 1`: `vol(K)(1 - r)^n ≤ G(int K)`. -/
theorem prop_1_6_lower_at_scale {K : Set (Fin n → ℝ)} (hKcpt : IsCompact K)
    (hKb : DiscreteMinkowski.IsPaperConvexBody K) {r : ℝ} (hr : r ∈ coveringSet K)
    (hr1 : r < 1) :
    (volume K).toReal * (1 - r) ^ n ≤
      ((DiscreteMinkowski.latticePoints (interior K) (standardIntegerLattice n)).ncard : ℝ) := by
  have hdim : finrank ℝ (Fin n → ℝ) = n := Module.finrank_fin_fun ℝ
  set K' := (1 - r) • interior K with hK'
  have h1r : 0 < 1 - r := by linarith
  have hK'm : MeasurableSet K' := (isOpen_interior.smul₀ h1r.ne').measurableSet
  have hK'b : Bornology.IsBounded K' :=
    (hKb.1.subset interior_subset).smul₀ (1 - r)
  obtain ⟨t, ht⟩ := van_der_corput hK'm hK'b
  obtain ⟨z, hz, htz⟩ := hr.2 t
  -- the translate by `t - z ∈ r K` lies in `int K`
  have hsub : (fun y => y + (t - z)) '' K' ⊆ interior K := by
    rintro _ ⟨y, hy, rfl⟩
    have := hKb.2.1.combo_interior_self_subset_interior h1r hr.1.le (by ring)
    exact this (Set.add_mem_add hy htz)
  have hfinI : (DiscreteMinkowski.latticePoints (interior K) (standardIntegerLattice n)).Finite :=
    DiscreteMinkowski.finite_inter_lattice (hKb.1.subset interior_subset) _
  have hcount : (DiscreteMinkowski.latticePoints ((fun y => y + t) '' K')
      (standardIntegerLattice n)).ncard ≤
      (DiscreteMinkowski.latticePoints (interior K) (standardIntegerLattice n)).ncard := by
    rw [← ncard_latticePoints_translate K' t hz]
    exact Set.ncard_le_ncard (Set.inter_subset_inter_left _ hsub) hfinI
  have hvolK' : volume K' = ENNReal.ofReal ((1 - r) ^ n) * volume K := by
    rw [hK', Measure.addHaar_smul_of_nonneg volume h1r.le, hdim,
      volume_interior_eq hKb.2.1]
  have hKtop : volume K ≠ ⊤ := hKcpt.measure_lt_top.ne
  have hle : volume K' ≤
      ((DiscreteMinkowski.latticePoints (interior K) (standardIntegerLattice n)).ncard : ℝ≥0∞) :=
    ht.trans (by exact_mod_cast hcount)
  rw [hvolK'] at hle
  have := ENNReal.toReal_mono (ENNReal.natCast_ne_top _) hle
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_natCast,
    mul_comm] at this
  exact this

/-- **Proposition 1.6, Eq. (1.16).** If `μ(K) ≤ 1` then `G(int K) ≥ vol(K)(1 - μ(K))^n`. -/
theorem proposition_1_6_lower {K : Set (Fin n → ℝ)} (hKcpt : IsCompact K)
    (hKb : DiscreteMinkowski.IsPaperConvexBody K) (hμ : coveringRadius K ≤ 1) :
    (volume K).toReal * (1 - coveringRadius K) ^ n ≤
      ((DiscreteMinkowski.latticePoints (interior K) (standardIntegerLattice n)).ncard : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using volume_le_ncard_interior_dim_zero hKb
  rcases hμ.eq_or_lt with heq | hlt
  · rw [heq, sub_self, zero_pow hn.ne', mul_zero]; positivity
  -- the bound at every covering scale `r ∈ (μ, 1)`, then `r → μ`
  set f : ℝ → ℝ := fun r => (volume K).toReal * (1 - r) ^ n
  have hcont : Tendsto f (𝓝[>] coveringRadius K) (𝓝 (f (coveringRadius K))) :=
    ((continuous_const.mul ((continuous_const.sub continuous_id).pow n)).tendsto _).mono_left
      nhdsWithin_le_nhds
  refine le_of_tendsto hcont ?_
  filter_upwards [Ioo_mem_nhdsGT hlt] with r hr
  exact prop_1_6_lower_at_scale hKcpt hKb (mem_coveringSet_of_lt hKcpt hKb hn hr.1) hr.2

/-- **AM-GM** in the form used for Eq. (1.9): `∏ z_i ≤ ((∑ z_i)/n)^n` for `z_i ≥ 0`. -/
theorem prod_le_mean_pow {z : Fin n → ℝ} (hz : ∀ i, 0 ≤ z i) :
    ∏ i, z i ≤ ((∑ i, z i) / n) ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h := Real.geom_mean_le_arith_mean Finset.univ (fun _ => (1 : ℝ)) z
    (fun _ _ => zero_le_one) (by simp [hn]) (fun i _ => hz i)
  simp only [Real.rpow_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, one_mul] at h
  have hP : 0 ≤ ∏ i, z i := Finset.prod_nonneg fun i _ => hz i
  calc ∏ i, z i = ((∏ i, z i) ^ ((n : ℝ)⁻¹)) ^ n := by
        rw [Real.rpow_inv_natCast_pow hP hn.ne']
    _ ≤ ((∑ i, z i) / n) ^ n :=
        pow_le_pow_left₀ (Real.rpow_nonneg hP _) h n

/-- **Theorem 1.1, Eq. (1.9).** If `λ_n(K) ≤ 2/n` then
`G(int K) ≥ vol(K) ∏_{i=1}^n (1 - n λ_i(K)/2)`. -/
theorem theorem_1_1_lower {K : Set (Fin n → ℝ)} (hKcpt : IsCompact K)
    (hKb : DiscreteMinkowski.IsPaperConvexBody K)
    (hlamn : DiscreteMinkowski.successiveMinimum K (standardIntegerLattice n) n ≤ 2 / n) :
    (volume K).toReal * ∏ i : Fin n, (1 - (n : ℝ) *
        DiscreteMinkowski.successiveMinimum K (standardIntegerLattice n) (i.1 + 1) / 2) ≤
      ((DiscreteMinkowski.latticePoints (interior K) (standardIntegerLattice n)).ncard : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using volume_le_ncard_interior_dim_zero hKb
  have hdim : finrank ℝ (Fin n → ℝ) = n := Module.finrank_fin_fun ℝ
  set lam : Fin n → ℝ := fun i =>
    DiscreteMinkowski.successiveMinimum K (standardIntegerLattice n) (i.1 + 1) with hlam
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hlamle : ∀ i, lam i ≤ 2 / n := fun i =>
    (DiscreteMinkowski.successiveMinimum_mono_of_le_finrank hKb (by omega)
      (by rw [hdim])).trans hlamn
  have hz : ∀ i, 0 ≤ 1 - (n : ℝ) * lam i / 2 := by
    intro i
    have := hlamle i
    rw [le_div_iff₀ hnpos] at this
    linarith
  -- `μ ≤ ∑ λ_i/2 ≤ 1`
  have hsum : ∑ i, lam i / 2 ≤ 1 := by
    calc ∑ i, lam i / 2 ≤ ∑ _i : Fin n, (1 / n : ℝ) :=
          Finset.sum_le_sum fun i _ => by
            have h := div_le_div_of_nonneg_right (hlamle i) (show (0 : ℝ) ≤ 2 by norm_num)
            have h2 : (2 : ℝ) / n / 2 = 1 / n := by field_simp
            linarith
      _ = 1 := by simp [Finset.card_univ]; field_simp
  have hμ := coveringRadius_le_sum_minima hKcpt hKb hn
  have h16 := proposition_1_6_lower hKcpt hKb (hμ.trans hsum)
  -- `(1 - μ)^n ≥ (1 - ∑ λ_i/2)^n = (mean of 1 - nλ_i/2)^n ≥ ∏ (1 - nλ_i/2)`
  have hmean : 1 - ∑ i, lam i / 2 = (∑ i, (1 - (n : ℝ) * lam i / 2)) / n := by
    have h1 : ∑ i, (1 - (n : ℝ) * lam i / 2) = n - n * ∑ i, lam i / 2 := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
      simp [mul_div_assoc]
    rw [h1]
    field_simp
  have hpow : (1 - ∑ i, lam i / 2) ^ n ≤ (1 - coveringRadius K) ^ n :=
    pow_le_pow_left₀ (by linarith) (by linarith) n
  have hamgm := prod_le_mean_pow hz
  rw [← hmean] at hamgm
  have hvol : 0 ≤ (volume K).toReal := ENNReal.toReal_nonneg
  calc (volume K).toReal * ∏ i, (1 - (n : ℝ) * lam i / 2)
      ≤ (volume K).toReal * (1 - ∑ i, lam i / 2) ^ n := mul_le_mul_of_nonneg_left hamgm hvol
    _ ≤ (volume K).toReal * (1 - coveringRadius K) ^ n := mul_le_mul_of_nonneg_left hpow hvol
    _ ≤ _ := h16

end

end LatticeVolumeInterpolation
