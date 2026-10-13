import BetaIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Prod

/-!
# A lower bound from a section and a projection

Let `U` and `V` be finite-dimensional real spaces of dimensions `k ≥ 1` and `m`, with Haar
measures `μ` and `ν`. If a convex set `C ⊆ U × V` contains `A × {0}` and its
projection onto `V` contains the compact set `B`, then

  `μ(A) ν(B) k! m! / (k + m)! ≤ (μ × ν)(C)`.

This is the volume computation behind the general Rogers-Shephard
inequality (Eq. (4.1), catalog item `rogers_shephard_section_projection`): there `C = K`,
`A = K ∩ L_I` and `B = K | L_I^⊥`, and `k! m! / (k + m)! = 1 / binom(n, k)`.

If `v = sb` with `b ∈ B` and `s ∈ [0, 1]`, take any lift `(w,b) ∈ C`.
Convexity gives `(sw + (1 - s)A) × {v} ⊆ C`, so translation invariance bounds the
fibre measure below by `(1 - s)^k μ(A)`. Taking the least such `s`
(it exists because `B` is compact) and writing `(1 - s_0)^k = ∫_{s_0}^1 k (1 - s)^(k-1) ds`,
the fibre measure dominates `μ(A) ∫_0^1 1[v ∈ sB] k (1 - s)^(k-1) ds`. Integrating over `v`
and exchanging the order of integration gives
`μ(A) ν(B) ∫_0^1 k (1 - s)^(k-1) s^m ds = μ(A) ν(B) k! m! / (k + m)!`.
-/

open MeasureTheory Measure Set Module
open scoped Pointwise ENNReal

namespace LatticeVolumeInterpolation

noncomputable section

variable {U V : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U] [MeasurableSpace U] [BorelSpace U]
  [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
  [FiniteDimensional ℝ V]

/-- The scales at which a vector lies in a dilate of `B`, as a subset of `V × ℝ`. -/
def scaleSet (B : Set V) : Set (V × ℝ) := {p | p.2 ∈ Icc (0 : ℝ) 1 ∧ p.1 ∈ p.2 • B}

omit [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V] in
theorem scaleSet_eq_image (B : Set V) :
    scaleSet B = (fun q : V × ℝ => (q.2 • q.1, q.2)) '' (B ×ˢ Icc (0 : ℝ) 1) := by
  ext ⟨v, s⟩
  simp only [scaleSet, mem_setOf_eq, mem_image, mem_prod, Prod.mk.injEq, Prod.exists]
  constructor
  · rintro ⟨hs, hv⟩
    obtain ⟨b, hb, rfl⟩ := mem_smul_set.1 hv
    exact ⟨b, s, ⟨hb, hs⟩, rfl, rfl⟩
  · rintro ⟨b, t, ⟨hb, ht⟩, rfl, rfl⟩
    exact ⟨ht, smul_mem_smul_set hb⟩

omit [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V] in
theorem isCompact_scaleSet {B : Set V} (hB : IsCompact B) : IsCompact (scaleSet B) := by
  rw [scaleSet_eq_image]
  exact (hB.prod isCompact_Icc).image (by fun_prop)

/-- The weight `k (1 - s)^(k-1)` on `[0, 1]`, as an extended nonnegative real. -/
def joinWeight (k : ℕ) (s : ℝ) : ℝ≥0∞ := ENNReal.ofReal (k * (1 - s) ^ (k - 1))

theorem measurable_joinWeight (k : ℕ) : Measurable (joinWeight k) := by
  unfold joinWeight
  fun_prop

/-- `∫_{s_0}^1 k (1 - s)^(k-1) ds = (1 - s_0)^k` for `k ≥ 1`. -/
theorem integral_joinWeight {k : ℕ} (hk : 1 ≤ k) {s₀ : ℝ} (hs₀ : s₀ ≤ 1) :
    ∫⁻ s in Icc s₀ 1, joinWeight k s = ENNReal.ofReal ((1 - s₀) ^ k) := by
  have hcont : Continuous fun s : ℝ => (k : ℝ) * (1 - s) ^ (k - 1) := by fun_prop
  have hnn : 0 ≤ᵐ[volume.restrict (Icc s₀ 1)] fun s : ℝ => (k : ℝ) * (1 - s) ^ (k - 1) := by
    refine (ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ fun s hs => ?_)
    exact mul_nonneg (Nat.cast_nonneg k) (pow_nonneg (by linarith [hs.2]) _)
  unfold joinWeight
  rw [← ofReal_integral_eq_lintegral_ofReal (hcont.integrableOn_Icc) hnn,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hs₀,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_left (fun t => t ^ (k - 1)) 1, integral_pow]
  congr 1
  have hk' : k - 1 + 1 = k := Nat.sub_add_cancel hk
  rw [hk', sub_self, zero_pow (by omega), sub_zero]
  have : ((k - 1 : ℕ) : ℝ) + 1 = k := by exact_mod_cast hk'
  rw [this]
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  field_simp

omit [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V] in
/-- **The fibre estimate.** For each `v`, the fibre of `C` over `v` has measure at least
`μ(A) ∫_0^1 1[v ∈ sB] k (1 - s)^(k-1) ds`. -/
theorem projection_fibre_lower_bound (μ : Measure U) [μ.IsAddHaarMeasure] {k : ℕ}
    (hk : 1 ≤ k) (hkU : finrank ℝ U = k)
    {A : Set U} {B : Set V} (hB : IsCompact B) {C : Set (U × V)} (hC : Convex ℝ C)
    (hAC : ∀ a ∈ A, (a, (0 : V)) ∈ C) (hBC : ∀ b ∈ B, ∃ u : U, (u, b) ∈ C) (v : V) :
    μ A * ∫⁻ s, (scaleSet B).indicator (fun p => joinWeight k p.2) (v, s)
      ≤ μ ((fun u => (u, v)) ⁻¹' C) := by
  set S : Set ℝ := {s | (v, s) ∈ scaleSet B} with hS
  have hind : ∀ s, (scaleSet B).indicator (fun p => joinWeight k p.2) (v, s)
      = S.indicator (joinWeight k) s := by
    intro s
    by_cases h : (v, s) ∈ scaleSet B
    · rw [indicator_of_mem h, indicator_of_mem (show s ∈ S from h)]
    · rw [indicator_of_notMem h, indicator_of_notMem (show s ∉ S from h)]
  simp_rw [hind]
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · simp [hSe]
  have hScpt : IsCompact S := by
    have : S = Prod.mk v ⁻¹' scaleSet B := rfl
    rw [this]
    refine Metric.isCompact_of_isClosed_isBounded
      ((isCompact_scaleSet hB).isClosed.preimage (continuous_const.prodMk continuous_id)) ?_
    refine (Metric.isBounded_Icc (0 : ℝ) 1).subset ?_
    intro s hs
    exact hs.1
  set s₀ := sInf S with hs₀def
  have hs₀ : s₀ ∈ S := hScpt.sInf_mem hSne
  have hs₀I : s₀ ∈ Icc (0 : ℝ) 1 := hs₀.1
  have hSsub : S ⊆ Icc s₀ 1 := fun s hs =>
    ⟨csInf_le hScpt.bddBelow hs, hs.1.2⟩
  have hint : ∫⁻ s, S.indicator (joinWeight k) s ≤ ENNReal.ofReal ((1 - s₀) ^ k) := by
    rw [lintegral_indicator (hScpt.isClosed.measurableSet), ← integral_joinWeight hk hs₀I.2]
    exact lintegral_mono_set hSsub
  obtain ⟨b, hb, hvb⟩ := mem_smul_set.1 hs₀.2
  obtain ⟨w, hw⟩ := hBC b hb
  have hsub : (s₀ • w) +ᵥ ((1 - s₀) • A) ⊆ (fun u => (u, v)) ⁻¹' C := by
    rintro u ⟨z, ⟨a, ha, rfl⟩, rfl⟩
    have hcomb := hC (hAC a ha) hw (by linarith [hs₀I.2] : (0 : ℝ) ≤ 1 - s₀)
      hs₀I.1 (by ring)
    simp only [mem_preimage]
    convert hcomb using 1
    ext <;> simp [hvb, vadd_eq_add, add_comm]
  calc μ A * ∫⁻ s, S.indicator (joinWeight k) s
      ≤ μ A * ENNReal.ofReal ((1 - s₀) ^ k) := mul_le_mul_right hint _
    _ = μ ((s₀ • w) +ᵥ ((1 - s₀) • A)) := by
        rw [measure_vadd, addHaar_smul_of_nonneg μ (by linarith [hs₀I.2]), hkU, mul_comm]
    _ ≤ μ ((fun u => (u, v)) ⁻¹' C) := measure_mono hsub

/-- **The section-projection lower bound**, for positive section dimension. -/
theorem section_projection_volume_lower_bound (μ : Measure U) (ν : Measure V)
    [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure] {k m : ℕ}
    (hk : 1 ≤ k) (hkU : finrank ℝ U = k) (hmV : finrank ℝ V = m)
    {A : Set U} {B : Set V} (hB : IsCompact B) {C : Set (U × V)} (hC : Convex ℝ C)
    (hCm : MeasurableSet C)
    (hAC : ∀ a ∈ A, (a, (0 : V)) ∈ C) (hBC : ∀ b ∈ B, ∃ u : U, (u, b) ∈ C) :
    μ A * ν B * ENNReal.ofReal
        ((k.factorial * m.factorial : ℝ) / ((k + m).factorial : ℝ))
      ≤ (μ.prod ν) C := by
  have hDm : MeasurableSet (scaleSet B) := (isCompact_scaleSet hB).isClosed.measurableSet
  have hF : Measurable fun p : V × ℝ => (scaleSet B).indicator (fun q => joinWeight k q.2) p :=
    ((measurable_joinWeight k).comp measurable_snd).indicator hDm
  -- the inner integral over `v` at a fixed scale `s`
  have hslice : ∀ s : ℝ, ∫⁻ v, (scaleSet B).indicator (fun q => joinWeight k q.2) (v, s) ∂ν
      = (Icc (0 : ℝ) 1).indicator
          (fun s => joinWeight k s * ENNReal.ofReal (s ^ m) * ν B) s := by
    intro s
    by_cases hs : s ∈ Icc (0 : ℝ) 1
    · rw [indicator_of_mem hs]
      have hset : (fun v => (v, s)) ⁻¹' scaleSet B = s • B := by
        ext v; simp [scaleSet, hs.1, hs.2]
      have : (fun v => (scaleSet B).indicator (fun q => joinWeight k q.2) (v, s))
          = ((fun v => (v, s)) ⁻¹' scaleSet B).indicator (fun _ => joinWeight k s) := by
        funext v
        by_cases hv : (v, s) ∈ scaleSet B
        · rw [indicator_of_mem hv, indicator_of_mem (show v ∈ _ from hv)]
        · rw [indicator_of_notMem hv, indicator_of_notMem (show v ∉ _ from hv)]
      rw [this, lintegral_indicator_const (hDm.preimage (by fun_prop)), hset,
        addHaar_smul_of_nonneg ν hs.1, hmV, mul_assoc]
    · rw [indicator_of_notMem hs]
      have : ∀ v, (scaleSet B).indicator (fun q => joinWeight k q.2) (v, s) = 0 := by
        intro v
        exact indicator_of_notMem (fun h => hs h.1) _
      simp [this]
  have hswap : ∫⁻ v, (∫⁻ s, (scaleSet B).indicator (fun q => joinWeight k q.2) (v, s)) ∂ν
      = ∫⁻ s, (∫⁻ v, (scaleSet B).indicator (fun q => joinWeight k q.2) (v, s) ∂ν) :=
    lintegral_lintegral_swap hF.aemeasurable
  -- the scale integral
  have hbeta : ∫⁻ s in Icc (0 : ℝ) 1, joinWeight k s * ENNReal.ofReal (s ^ m)
      = ENNReal.ofReal ((k.factorial * m.factorial : ℝ) / ((k + m).factorial : ℝ)) := by
    have hcont : Continuous fun s : ℝ => (k : ℝ) * (1 - s) ^ (k - 1) * s ^ m := by fun_prop
    have hnn : 0 ≤ᵐ[volume.restrict (Icc (0 : ℝ) 1)]
        fun s : ℝ => (k : ℝ) * (1 - s) ^ (k - 1) * s ^ m := by
      refine (ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ fun s hs => ?_)
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg k) (pow_nonneg (by linarith [hs.2]) _))
        (pow_nonneg hs.1 _)
    have hpt : ∀ s ∈ Icc (0 : ℝ) 1, joinWeight k s * ENNReal.ofReal (s ^ m)
        = ENNReal.ofReal ((k : ℝ) * (1 - s) ^ (k - 1) * s ^ m) := by
      intro s hs
      unfold joinWeight
      rw [← ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg k)
        (pow_nonneg (by linarith [hs.2]) _))]
    rw [setLIntegral_congr_fun measurableSet_Icc hpt,
      ← ofReal_integral_eq_lintegral_ofReal hcont.integrableOn_Icc hnn,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
    congr 1
    have hrw : (fun s : ℝ => (k : ℝ) * (1 - s) ^ (k - 1) * s ^ m)
        = fun s => (k : ℝ) * ((1 - s) ^ (k - 1) * s ^ m) := by
      funext s; ring
    rw [hrw, intervalIntegral.integral_const_mul, integral_one_sub_pow_mul_pow]
    have hk' : k - 1 + m + 1 = k + m := by omega
    rw [hk']
    have hkf : (k.factorial : ℝ) = k * (k - 1).factorial := by
      conv_lhs => rw [show k = (k - 1) + 1 by omega]
      rw [Nat.factorial_succ]
      push_cast
      rw [Nat.cast_sub hk]
      ring
    rw [hkf]
    ring
  calc μ A * ν B * ENNReal.ofReal
        ((k.factorial * m.factorial : ℝ) / ((k + m).factorial : ℝ))
      = μ A * ∫⁻ v, (∫⁻ s, (scaleSet B).indicator (fun q => joinWeight k q.2) (v, s)) ∂ν := by
        rw [hswap]
        simp_rw [hslice]
        rw [lintegral_indicator measurableSet_Icc]
        simp_rw [mul_comm _ (ν B)]
        rw [lintegral_const_mul' _ _ (hB.measure_lt_top.ne), ← hbeta]
        ring
    _ = ∫⁻ v, μ A * (∫⁻ s, (scaleSet B).indicator (fun q => joinWeight k q.2) (v, s)) ∂ν := by
        rw [lintegral_const_mul _ hF.lintegral_prod_right']
    _ ≤ ∫⁻ v, μ ((fun u => (u, v)) ⁻¹' C) ∂ν :=
        lintegral_mono fun v => projection_fibre_lower_bound μ hk hkU hB hC hAC hBC v
    _ = (μ.prod ν) C := (Measure.prod_apply_symm hCm).symm

/-- **The section-projection lower bound, in every dimension.** If `k = 0`,
every lift of `B` has first coordinate zero, giving the product bound directly. -/
theorem section_projection_volume_lower_bound' (μ : Measure U) (ν : Measure V)
    [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure] {k m : ℕ}
    (hkU : finrank ℝ U = k) (hmV : finrank ℝ V = m)
    {A : Set U} {B : Set V} (hB : IsCompact B) {C : Set (U × V)} (hC : Convex ℝ C)
    (hCm : MeasurableSet C)
    (hAC : ∀ a ∈ A, (a, (0 : V)) ∈ C) (hBC : ∀ b ∈ B, ∃ u : U, (u, b) ∈ C) :
    μ A * ν B * ENNReal.ofReal
        ((k.factorial * m.factorial : ℝ) / ((k + m).factorial : ℝ))
      ≤ (μ.prod ν) C := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have hzero : ∀ x : U, x = 0 := finrank_zero_iff_forall_zero.1 hkU
    have hconst : ENNReal.ofReal
        (((0 : ℕ).factorial * m.factorial : ℝ) / ((0 + m).factorial : ℝ)) = 1 := by
      rw [zero_add, Nat.factorial_zero, Nat.cast_one, one_mul,
        div_self (by positivity), ENNReal.ofReal_one]
    rw [hconst, mul_one]
    have hA : A ⊆ {0} := fun a _ => hzero a
    have hsub : ({0} : Set U) ×ˢ B ⊆ C := by
      rintro ⟨u, v⟩ ⟨-, hv⟩
      rw [hzero u]
      obtain ⟨u, hu⟩ := hBC v hv
      simpa [hzero u] using hu
    calc μ A * ν B ≤ μ {0} * ν B := mul_le_mul_left (measure_mono hA) _
      _ = (μ.prod ν) (({0} : Set U) ×ˢ B) := (Measure.prod_prod _ _).symm
      _ ≤ (μ.prod ν) C := measure_mono hsub
  · exact section_projection_volume_lower_bound μ ν hk hkU hmV hB hC hCm hAC hBC

/-- The join bound is the section-projection bound with zero lifts of `B`. -/
theorem join_volume_lower_bound' (μ : Measure U) (ν : Measure V)
    [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure] {k m : ℕ}
    (hkU : finrank ℝ U = k) (hmV : finrank ℝ V = m)
    {A : Set U} {B : Set V} (hB : IsCompact B) {C : Set (U × V)} (hC : Convex ℝ C)
    (hCm : MeasurableSet C)
    (hAC : ∀ a ∈ A, (a, (0 : V)) ∈ C) (hBC : ∀ b ∈ B, ((0 : U), b) ∈ C) :
    μ A * ν B * ENNReal.ofReal
        ((k.factorial * m.factorial : ℝ) / ((k + m).factorial : ℝ))
      ≤ (μ.prod ν) C :=
  section_projection_volume_lower_bound' μ ν hkU hmV hB hC hCm hAC
    (fun b hb => ⟨0, hBC b hb⟩)

/-- The positive-section-dimension join bound. -/
theorem join_volume_lower_bound (μ : Measure U) (ν : Measure V)
    [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure] {k m : ℕ}
    (hk : 1 ≤ k) (hkU : finrank ℝ U = k) (hmV : finrank ℝ V = m)
    {A : Set U} {B : Set V} (hB : IsCompact B) {C : Set (U × V)} (hC : Convex ℝ C)
    (hCm : MeasurableSet C)
    (hAC : ∀ a ∈ A, (a, (0 : V)) ∈ C) (hBC : ∀ b ∈ B, ((0 : U), b) ∈ C) :
    μ A * ν B * ENNReal.ofReal
        ((k.factorial * m.factorial : ℝ) / ((k + m).factorial : ℝ))
      ≤ (μ.prod ν) C :=
  section_projection_volume_lower_bound μ ν hk hkU hmV hB hC hCm hAC
    (fun b hb => ⟨0, hBC b hb⟩)

end

end LatticeVolumeInterpolation
