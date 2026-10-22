import TheoremThreeOne
import MinimaDifferenceAvoidance
import SeparatedRows

/-!
# The planar floor-product bound

Catalog item `bhw_lattice_conjecture_dimension_two_symmetric`.
The coordinate frame is adapted to the first greedy minimum flag. The
source difference-avoidance lemma then supplies both inputs to the
residue-grouped slice count, as in Malikiosis's induction in Section 3.2.
-/

open Set Module
open scoped Pointwise BigOperators

namespace LatticeVolumeInterpolation

noncomputable section

/-- Adapt the integer lattice coordinates to the first greedy minimum flag.
The second coordinate vanishes on that flag, including repeated minima. -/
theorem exists_unimodular_horizontal_minima_flag
    {K : Set (Fin 2 → ℝ)} (hK : DiscreteMinkowski.IsPaperConvexBody K) :
    ∃ V : (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ),
      (∀ x, V x ∈ standardIntegerLattice 2 ↔ x ∈ standardIntegerLattice 2) ∧
      ∀ z ∈ DiscreteMinkowski.flagSpan K (standardIntegerLattice 2) 1, (V z) 1 = 0 := by
  classical
  have hdim : finrank ℝ (Fin 2 → ℝ) = 2 := Module.finrank_fin_fun ℝ
  let v : Fin 2 → (Fin 2 → ℝ) := fun k =>
    DiscreteMinkowski.flagVector K (standardIntegerLattice 2) k.1
  have hvΛ : ∀ k, v k ∈ standardIntegerLattice 2 := fun k =>
    DiscreteMinkowski.flagVector_mem k.1
      (DiscreteMinkowski.greedyChoice_flagSpan hK (by rw [hdim]; exact k.2))
  have hvind : LinearIndependent ℝ v := linearIndependent_flagVector hK
  choose z hz using fun k => (mem_standardIntegerLattice_iff_castCoords (v k)).1 (hvΛ k)
  have hzind : LinearIndependent ℤ z := by
    rw [Fintype.linearIndependent_iff] at hvind ⊢
    intro g hg k
    have hreal : ∑ j, (g j : ℝ) • v j = 0 := by
      funext l
      have := congrFun hg l
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
      simp only [hz, castCoords]
      exact_mod_cast this
    exact_mod_cast hvind _ hreal k
  obtain ⟨U, hU⟩ := exists_triangularizing 2 z hzind
  obtain ⟨V, hV, hVs, _hdet⟩ := realize_unimodular U
  refine ⟨V, mem_lattice_iff_of_realize V hV hVs, ?_⟩
  have hfirst : (V (v 0)) 1 = 0 := by
    simp only [hz 0, hV, castCoords]
    exact_mod_cast hU 0 1 (by decide)
  intro w hw
  have hspan : DiscreteMinkowski.flagSpan K (standardIntegerLattice 2) 1 =
      Submodule.span ℝ {v 0} := by
    rw [DiscreteMinkowski.flagSpan_succ 0,
      DiscreteMinkowski.flagSpan_zero, bot_sup_eq]
    rfl
  rw [hspan] at hw
  obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hw
  simp [map_smul, Pi.smul_apply, hfirst]

/-- The planar product bound for any positive integer thresholds strictly
above the two critical reciprocal scales. The floor choices are instantiated
separately; no geometric avoidance hypothesis remains. -/
theorem planar_lattice_count_le_of_minima_thresholds
    {K : Set (Fin 2 → ℝ)} (hc : IsCompact K)
    (hK : DiscreteMinkowski.IsPaperConvexBody K)
    {q₁ q₂ : ℕ} (hq₂ : 0 < q₂) (horder : q₂ ≤ q₁)
    (hfirst : 2 / (q₁ : ℝ) <
      DiscreteMinkowski.successiveMinimum K (standardIntegerLattice 2) 1)
    (hsecond : 2 / (q₂ : ℝ) <
      DiscreteMinkowski.successiveMinimum K (standardIntegerLattice 2) 2) :
    (DiscreteMinkowski.latticePoints K (standardIntegerLattice 2)).ncard ≤ q₁ * q₂ := by
  obtain ⟨V, hΛ, hflag⟩ := exists_unimodular_horizontal_minima_flag hK
  have hQ := isPaperConvexBody_image V hK
  have hdim : finrank ℝ (Fin 2 → ℝ) = 2 := Module.finrank_fin_fun ℝ
  have hq₁ : (0 : ℝ) < q₁ := by exact_mod_cast (lt_of_lt_of_le hq₂ horder)
  have hq₂r : (0 : ℝ) < q₂ := by exact_mod_cast hq₂
  have hint : (V '' K).Nonempty := hQ.2.2.mono interior_subset
  have havoid₁ : ∀ x ∈ V '' K, ∀ y ∈ V '' K, x - y ≠ pt (q₁ : ℝ) 0 := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ heq
    let z := V.symm (pt 1 0)
    have hzΛ : z ∈ standardIntegerLattice 2 := by
      apply (hΛ z).mp
      simp only [z, V.apply_symm_apply]
      apply (mem_standardIntegerLattice_iff 2 _).mpr
      refine ⟨![1, 0], ?_⟩
      intro i; fin_cases i <;> simp [pt]
    have hz0 : z ≠ 0 := by
      intro he
      have := congrArg (fun w => (V w) 0) he
      simpa [z, pt] using this
    apply difference_ne_smul_of_first_minimum hK (by rw [hdim]; norm_num)
      hq₁ hfirst hzΛ hz0 hx hy
    apply V.injective
    rw [map_sub, map_smul, show V z = pt 1 0 by simp [z]]
    convert heq using 1
    ext i; fin_cases i <;> simp [pt]
  have havoid₂ : ∀ x ∈ V '' K, ∀ y ∈ V '' K, ∀ u v : ℤ, v ≠ 0 →
      x - y ≠ pt ((q₂ : ℝ) * u) ((q₂ : ℝ) * v) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ u v hv heq
    let z := V.symm (pt (u : ℝ) (v : ℝ))
    have hzΛ : z ∈ standardIntegerLattice 2 := by
      apply (hΛ z).mp
      simp only [z, V.apply_symm_apply]
      apply (mem_standardIntegerLattice_iff 2 _).mpr
      refine ⟨![u, v], ?_⟩
      intro i; fin_cases i <;> simp [pt]
    have hzflag : z ∉ DiscreteMinkowski.flagSpan K (standardIntegerLattice 2) 1 := by
      intro hz
      have he := hflag z hz
      have : (v : ℝ) = 0 := by simpa [z, pt] using he
      exact hv (by exact_mod_cast this)
    apply difference_ne_smul_outside_minima_flag hK (by rw [hdim]; norm_num)
      hq₂r hsecond hzΛ hzflag hx hy
    apply V.injective
    rw [map_sub, map_smul, show V z = pt (u : ℝ) (v : ℝ) by simp [z]]
    convert heq using 1
    ext i; fin_cases i <;> simp [pt]
  have hb := planar_lattice_count_le_of_period_avoidance (isCompact_image V hc)
    hQ.2.1 hint hq₂ horder havoid₁ havoid₂
  rwa [ncard_latticePoints_image V hΛ] at hb

/-- The floored reciprocal gives a positive integer strictly above the
unfloored reciprocal, hence strictly below the critical scale after inversion. -/
theorem floor_reciprocal_minimum_threshold {l : ℝ} (hl : 0 < l) :
    0 < ⌊2 / l + 1⌋₊ ∧ 2 / (⌊2 / l + 1⌋₊ : ℝ) < l := by
  have hx : 0 ≤ 2 / l := (div_pos (by norm_num) hl).le
  have hq : 0 < ⌊2 / l + 1⌋₊ := Nat.floor_pos.mpr (by linarith)
  have hqr : (0 : ℝ) < ⌊2 / l + 1⌋₊ := by exact_mod_cast hq
  have hgt : 2 / l < (⌊2 / l + 1⌋₊ : ℝ) := by
    rw [Nat.floor_add_one hx, Nat.cast_add, Nat.cast_one]
    exact Nat.lt_floor_add_one _
  refine ⟨hq, (div_lt_iff₀ hqr).mpr ?_⟩
  have hmul := (div_lt_iff₀ hl).mp hgt
  nlinarith

/-- The exact planar floor-product bound from the residue-slice proof.
This proof in fact applies to every compact full-dimensional convex body,
since its difference-avoidance inputs use the central symmetral. -/
theorem planar_floor_product_bound
    {K : Set (Fin 2 → ℝ)} (hc : IsCompact K)
    (hK : DiscreteMinkowski.IsPaperConvexBody K) :
    (DiscreteMinkowski.latticePoints K (standardIntegerLattice 2)).ncard ≤
      ⌊2 / DiscreteMinkowski.successiveMinimum K (standardIntegerLattice 2) 1 + 1⌋₊ *
      ⌊2 / DiscreteMinkowski.successiveMinimum K (standardIntegerLattice 2) 2 + 1⌋₊ := by
  have hdim : finrank ℝ (Fin 2 → ℝ) = 2 := Module.finrank_fin_fun ℝ
  have hpos₁ := DiscreteMinkowski.successiveMinimum_pos
    (Λ := standardIntegerLattice 2) hK (i := 1) (by norm_num) (by rw [hdim]; norm_num)
  have hpos₂ := DiscreteMinkowski.successiveMinimum_pos
    (Λ := standardIntegerLattice 2) hK (i := 2) (by norm_num) (by omega)
  have hmono := DiscreteMinkowski.successiveMinimum_mono_of_le_finrank
    (Λ := standardIntegerLattice 2) hK (i := 1) (j := 2) (by norm_num)
    (by omega)
  obtain ⟨_hq₁, hcrit₁⟩ := floor_reciprocal_minimum_threshold hpos₁
  obtain ⟨hq₂, hcrit₂⟩ := floor_reciprocal_minimum_threshold hpos₂
  apply planar_lattice_count_le_of_minima_thresholds hc hK hq₂ ?_ hcrit₁ hcrit₂
  apply Nat.floor_mono
  have hr : 2 / DiscreteMinkowski.successiveMinimum K (standardIntegerLattice 2) 2 ≤
      2 / DiscreteMinkowski.successiveMinimum K (standardIntegerLattice 2) 1 := by
    apply (div_le_div_iff₀ hpos₂ hpos₁).mpr
    nlinarith
  linarith

/-- The precise origin-symmetric planar theorem quoted by Freyer--Lucas.
Its symmetry hypothesis is retained from Betke--Henk--Wills's statement;
the slice proof above additionally checks the nonsymmetric extension. -/
theorem symmetric_planar_floor_product_bound
    {K : Set (Fin 2 → ℝ)} (hc : IsCompact K)
    (hK : DiscreteMinkowski.IsPaperConvexBody K)
    (_hsym : DiscreteMinkowski.IsOriginSymmetric K) :
    (DiscreteMinkowski.latticePoints K (standardIntegerLattice 2)).ncard ≤
      ⌊2 / DiscreteMinkowski.successiveMinimum K (standardIntegerLattice 2) 1 + 1⌋₊ *
      ⌊2 / DiscreteMinkowski.successiveMinimum K (standardIntegerLattice 2) 2 + 1⌋₊ :=
  planar_floor_product_bound hc hK

end
end LatticeVolumeInterpolation
