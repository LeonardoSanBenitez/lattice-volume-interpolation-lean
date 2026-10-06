import ReverseSchymura

/-!
# The projection of a lattice along a lattice subspace is discrete

Catalog item `projection_of_lattice_is_lattice` (Sec. 2): for a lattice `Λ ⊆ ℝ^n` and `X ⊆ Λ`,
`Λ | span(X)^⊥` is a lattice. The paper states it without proof. Here: the projection of a
discrete `Λ` onto `L^⊥`, `L = span(X)`, meets every bounded set in finitely many points
(`finite_projMap_inter_bounded`), and it spans `L^⊥` when `Λ` spans `ℝ^n`
(`span_projMap_eq_top`).

The argument: a lattice vector `λ` is its projection plus an `l ∈ L`; writing `l` in an
independent subset `Y ⊆ X` spanning `L` and subtracting the integer parts of its coordinates
leaves a lattice vector `λ - μ` of bounded norm with the same projection, and a bounded set
contains finitely many lattice vectors.
-/

open Set Module Metric
open scoped Pointwise

namespace LatticeVolumeInterpolation

noncomputable section

variable {n : ℕ}

/-- `x` minus its orthogonal projection onto `L^⊥` lies in `L`. -/
theorem sub_projMap_mem (L : Submodule ℝ (Fin n → ℝ)) (x : Fin n → ℝ) :
    x - (toEucl n).symm (projMap L x : EuclideanSpace ℝ (Fin n)) ∈ L := by
  set Le := L.map (toEucl n).toLinearMap
  have hproj : (projMap L x : EuclideanSpace ℝ (Fin n)) = Leᗮ.starProjection (toEucl n x) := rfl
  have hmem : toEucl n x - Leᗮ.starProjection (toEucl n x) ∈ Le := by
    have := Submodule.sub_starProjection_mem_orthogonal (K := Leᗮ) (toEucl n x)
    rwa [Submodule.orthogonal_orthogonal] at this
  obtain ⟨y, hy, hyeq⟩ := Submodule.mem_map.1 hmem
  have : x - (toEucl n).symm (projMap L x : EuclideanSpace ℝ (Fin n)) = y := by
    apply (toEucl n).injective
    rw [map_sub, LinearEquiv.apply_symm_apply, ← hproj] at *
    exact hyeq.symm
  rw [this]; exact hy

/-- **The projected lattice is discrete**: it meets every bounded subset of `L^⊥` in finitely
many points. -/
theorem finite_projMap_inter_bounded (Λ : Submodule ℤ (Fin n → ℝ)) [DiscreteTopology Λ]
    {X : Set (Fin n → ℝ)} (hX : X ⊆ Λ)
    {B : Set ((Submodule.span ℝ X).map (toEucl n).toLinearMap)ᗮ} (hB : Bornology.IsBounded B) :
    (projMap (Submodule.span ℝ X) '' (Λ : Set (Fin n → ℝ)) ∩ B).Finite := by
  classical
  set L := Submodule.span ℝ X
  obtain ⟨Y, hYX, hYspan, hYind⟩ := exists_linearIndependent ℝ X
  have hYfin : Y.Finite := hYind.setFinite
  set Yf := hYfin.toFinset
  have hYfspan : Submodule.span ℝ (Yf : Set (Fin n → ℝ)) = L := by
    rw [hYfin.coe_toFinset, hYspan]
  set S := ∑ y ∈ Yf, ‖y‖
  obtain ⟨R, hR⟩ := hB.subset_closedBall 0
  set e := (toEucl n).symm.toContinuousLinearEquiv
  set R' := ‖(e : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin n → ℝ))‖ * R + S
  have hfin : (((Λ : Set (Fin n → ℝ)) ∩ closedBall 0 R')).Finite :=
    DiscreteMinkowski.finite_inter_lattice isBounded_closedBall Λ |>.subset
      (fun z hz => ⟨hz.2, hz.1⟩)
  refine (hfin.image (projMap L)).subset ?_
  rintro _ ⟨⟨w₀, hw, rfl⟩, hwB⟩
  -- reduce the `L`-component modulo the lattice spanned by `Y`
  have hl : w₀ - (toEucl n).symm (projMap L w₀ : EuclideanSpace ℝ (Fin n)) ∈
      Submodule.span ℝ (Yf : Set (Fin n → ℝ)) := (le_of_eq hYfspan.symm) (sub_projMap_mem L w₀)
  obtain ⟨c, -, hc⟩ := (Submodule.mem_span_finset).1 hl
  set μ := ∑ y ∈ Yf, (⌊c y⌋ : ℤ) • y
  have hμΛ : μ ∈ Λ := Submodule.sum_mem _ fun y hy =>
    Submodule.smul_mem _ _ (hYX ((hYfin.mem_toFinset).1 hy) |> hX)
  have hμL : μ ∈ L := by
    rw [← hYfspan]
    exact Submodule.sum_mem _ fun y hy =>
      Submodule.smul_of_tower_mem _ _ (Submodule.subset_span hy)
  refine ⟨w₀ - μ, ⟨Λ.sub_mem hw hμΛ, ?_⟩, ?_⟩
  · -- the norm bound
    have hdecomp : w₀ - μ = (toEucl n).symm (projMap L w₀ : EuclideanSpace ℝ (Fin n)) +
        ∑ y ∈ Yf, (c y - ⌊c y⌋) • y := by
      have : ∑ y ∈ Yf, (c y - ⌊c y⌋) • y = ∑ y ∈ Yf, c y • y - μ := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [sub_smul, Int.cast_smul_eq_zsmul]
      rw [this, hc]; abel
    rw [mem_closedBall, dist_zero_right, hdecomp]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · have h1 := (e : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin n → ℝ)).le_opNorm
        (projMap L w₀ : EuclideanSpace ℝ (Fin n))
      have h2 : ‖(projMap L w₀ : EuclideanSpace ℝ (Fin n))‖ ≤ R := by
        have := hR hwB
        rwa [mem_closedBall, dist_zero_right] at this
      calc ‖(toEucl n).symm (projMap L w₀ : EuclideanSpace ℝ (Fin n))‖
          = ‖(e : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin n → ℝ))
              (projMap L w₀ : EuclideanSpace ℝ (Fin n))‖ := rfl
        _ ≤ _ := h1
        _ ≤ _ := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_)
      rw [norm_smul, Real.norm_eq_abs]
      have h0 : 0 ≤ c y - ⌊c y⌋ := by linarith [Int.floor_le (c y)]
      have h1 : c y - ⌊c y⌋ ≤ 1 := by linarith [Int.lt_floor_add_one (c y)]
      rw [abs_of_nonneg h0]
      calc (c y - ⌊c y⌋) * ‖y‖ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ = ‖y‖ := one_mul _
  · -- same projection, since `μ ∈ L = ker`
    have hker : projMap L μ = 0 := by
      rw [← LinearMap.mem_ker, ker_projMap]; exact hμL
    rw [map_sub, hker, sub_zero]

/-- **The projected lattice spans `L^⊥`** when `Λ` spans `ℝ^n`: the projection is onto. -/
theorem span_projMap_eq_top (L : Submodule ℝ (Fin n → ℝ)) {S : Set (Fin n → ℝ)}
    (hS : Submodule.span ℝ S = ⊤) : Submodule.span ℝ (projMap L '' S) = ⊤ := by
  have hsurj : Function.Surjective (projMap L) := by
    intro y
    refine ⟨(toEucl n).symm (y : EuclideanSpace ℝ (Fin n)), ?_⟩
    apply Subtype.ext
    change (L.map (toEucl n).toLinearMap)ᗮ.starProjection
      (toEucl n ((toEucl n).symm (y : EuclideanSpace ℝ (Fin n)))) = _
    rw [LinearEquiv.apply_symm_apply, Submodule.starProjection_eq_self_iff.2 y.2]
  rw [Submodule.span_image, hS, Submodule.map_top, LinearMap.range_eq_top.2 hsurj]

end

end LatticeVolumeInterpolation
