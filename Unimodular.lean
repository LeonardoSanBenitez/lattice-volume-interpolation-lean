import Triangularize
import StandardLattice
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Unimodular changes of coordinates

Catalog item `unimodular_invariance_of_paper_functionals` (Sec. 3, first sentence of the proof
of Theorem 3.1): a unimodular change of coordinates `U` preserves the volume, the lattice point
enumerator and every successive minimum. The paper asserts this in one sentence.

`realize_unimodular` turns a `ℤ`-linear automorphism of `ℤ^n` into a real linear automorphism
`V` of `ℝ^n` with `|det V| = 1` that maps `ℤ^n` onto itself and agrees with the integer map on
integer points. For any such `V` and any `K`:

* `vol(V K) = vol(K)`, by the change of variables `vol(V K) = |det V| vol(K)`;
* `G(V K) = G(K)`, because `V` restricts to a bijection of `ℤ^n`;
* `cs(V K) = V cs(K)` and `|V x|_{V cs(K)} = |x|_{cs(K)}`, so `V` carries the lattice points of
  `r cs(K)` onto those of `r cs(V K)` and every `λ_i` is unchanged.
-/

open MeasureTheory Set Module
open scoped Pointwise

namespace LatticeVolumeInterpolation

noncomputable section

variable {n : ℕ}

/-- The real points with integer coordinates `z`. -/
def castCoords (z : Fin n → ℤ) : Fin n → ℝ := fun i => (z i : ℝ)

theorem mem_standardIntegerLattice_iff_castCoords (x : Fin n → ℝ) :
    x ∈ standardIntegerLattice n ↔ ∃ z : Fin n → ℤ, x = castCoords z := by
  rw [mem_standardIntegerLattice_iff]
  constructor
  · rintro ⟨z, hz⟩; exact ⟨z, funext hz⟩
  · rintro ⟨z, rfl⟩; exact ⟨z, fun _ => rfl⟩

/-- The real matrix of an integer linear map acts on integer points as the map does. -/
theorem toLin'_map_castCoords (f : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ)) (z : Fin n → ℤ) :
    Matrix.toLin' ((LinearMap.toMatrix' f).map (Int.castRingHom ℝ)) (castCoords z) =
      castCoords (f z) := by
  funext i
  have h2 : castCoords z = fun x => ((z x : ℤ) : ℝ) := rfl
  have h3 : castCoords (f z) i = ((f z i : ℤ) : ℝ) := rfl
  rw [Matrix.toLin'_apply, h2, h3, ← LinearMap.toMatrix'_mulVec f z]
  have := RingHom.map_mulVec (Int.castRingHom ℝ) (LinearMap.toMatrix' f) z i
  simpa [Function.comp_def] using this.symm

/-- **A `ℤ`-automorphism of `ℤ^n` as a real unimodular map.** -/
theorem realize_unimodular (U : (Fin n → ℤ) ≃ₗ[ℤ] (Fin n → ℤ)) :
    ∃ V : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ),
      (∀ z, V (castCoords z) = castCoords (U z)) ∧
      (∀ z, V.symm (castCoords z) = castCoords (U.symm z)) ∧
      |LinearMap.det (V : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))| = 1 := by
  set A := LinearMap.toMatrix' (U : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ)) with hA
  set B := LinearMap.toMatrix' (U.symm : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ)) with hB
  have hAB : A * B = 1 := by
    rw [hA, hB, ← LinearMap.toMatrix'_comp]
    have : (U : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ)) ∘ₗ U.symm = LinearMap.id := by
      ext x; simp
    rw [this, LinearMap.toMatrix'_id]
  have hBA : B * A = 1 := by
    rw [hA, hB, ← LinearMap.toMatrix'_comp]
    have : (U.symm : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ)) ∘ₗ U = LinearMap.id := by
      ext x; simp
    rw [this, LinearMap.toMatrix'_id]
  set Ar := A.map (Int.castRingHom ℝ)
  set Br := B.map (Int.castRingHom ℝ)
  have hABr : Ar * Br = 1 := by
    rw [← Matrix.map_mul, hAB, Matrix.map_one _ (by simp) (by simp)]
  have hBAr : Br * Ar = 1 := by
    rw [← Matrix.map_mul, hBA, Matrix.map_one _ (by simp) (by simp)]
  set V : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) := LinearEquiv.ofLinear (Matrix.toLin' Ar)
    (Matrix.toLin' Br) (by rw [← Matrix.toLin'_mul, hABr, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, hBAr, Matrix.toLin'_one]) with hV
  refine ⟨V, fun z => toLin'_map_castCoords _ z, fun z => toLin'_map_castCoords _ z, ?_⟩
  have hdetA : A.det = 1 ∨ A.det = -1 := by
    refine Int.eq_one_or_neg_one_of_mul_eq_one (v := B.det) ?_
    rw [← Matrix.det_mul, hAB, Matrix.det_one]
  have hdet : LinearMap.det (V : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) = (A.det : ℝ) := by
    change LinearMap.det (Matrix.toLin' Ar) = _
    rw [LinearMap.det_toLin']
    change ((Int.castRingHom ℝ).mapMatrix A).det = (Int.castRingHom ℝ) A.det
    rw [RingHom.map_det]
  rw [hdet]
  rcases hdetA with h | h <;> simp [h]

variable (V : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ))

/-- A real map that is integral on integer points in both directions maps `ℤ^n` onto itself. -/
theorem mem_lattice_iff_of_realize {U : (Fin n → ℤ) ≃ₗ[ℤ] (Fin n → ℤ)}
    (hV : ∀ z, V (castCoords z) = castCoords (U z))
    (hVs : ∀ z, V.symm (castCoords z) = castCoords (U.symm z))
    (x : Fin n → ℝ) : V x ∈ standardIntegerLattice n ↔ x ∈ standardIntegerLattice n := by
  simp only [mem_standardIntegerLattice_iff_castCoords]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨U.symm w, ?_⟩
    rw [← hVs, ← hw, LinearEquiv.symm_apply_apply]
  · rintro ⟨z, rfl⟩
    exact ⟨U z, hV z⟩

variable (hΛ : ∀ x, V x ∈ standardIntegerLattice n ↔ x ∈ standardIntegerLattice n)
include hΛ

theorem image_latticePoints (K : Set (Fin n → ℝ)) :
    V '' DiscreteMinkowski.latticePoints K (standardIntegerLattice n) =
      DiscreteMinkowski.latticePoints (V '' K) (standardIntegerLattice n) := by
  ext y
  simp only [DiscreteMinkowski.latticePoints_apply, mem_image, mem_inter_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨x, ⟨hxK, hxΛ⟩, rfl⟩
    exact ⟨⟨x, hxK, rfl⟩, (hΛ x).2 hxΛ⟩
  · rintro ⟨⟨x, hxK, rfl⟩, hyΛ⟩
    exact ⟨x, ⟨hxK, (hΛ x).1 hyΛ⟩, rfl⟩

/-- **`G(V K) = G(K)`.** -/
theorem ncard_latticePoints_image (K : Set (Fin n → ℝ)) :
    (DiscreteMinkowski.latticePoints (V '' K) (standardIntegerLattice n)).ncard =
      (DiscreteMinkowski.latticePoints K (standardIntegerLattice n)).ncard := by
  rw [← image_latticePoints V hΛ, Set.ncard_image_of_injective _ V.injective]

omit hΛ in
theorem halfDifferenceBody_image (K : Set (Fin n → ℝ)) :
    DiscreteMinkowski.halfDifferenceBody (V '' K) =
      V '' DiscreteMinkowski.halfDifferenceBody K := by
  simp only [DiscreteMinkowski.halfDifferenceBody_apply]
  rw [image_smul_set]
  congr 1
  ext y
  simp only [mem_sub, mem_image]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨a - b, ⟨a, ha, b, hb, rfl⟩, map_sub V a b⟩
  · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
    exact ⟨V a, ⟨a, ha, rfl⟩, V b, ⟨b, hb, rfl⟩, (map_sub V a b).symm⟩

omit hΛ in
/-- A linear automorphism carries the gauge along. -/
theorem gauge_image_apply (D : Set (Fin n → ℝ)) (x : Fin n → ℝ) :
    gauge (V '' D) (V x) = gauge D x := by
  unfold gauge
  congr 1
  ext r
  simp only [mem_setOf_eq]
  refine and_congr_right fun _ => ?_
  rw [← image_smul_set, V.injective.mem_set_image]

theorem scaledLatticeSpan_image (K : Set (Fin n → ℝ)) (r : ℝ) :
    DiscreteMinkowski.scaledLatticeSpan (V '' K) (standardIntegerLattice n) r =
      (DiscreteMinkowski.scaledLatticeSpan K (standardIntegerLattice n) r).map
        (V : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) := by
  rw [DiscreteMinkowski.scaledLatticeSpan, DiscreteMinkowski.scaledLatticeSpan,
    Submodule.map_span]
  congr 1
  rw [halfDifferenceBody_image, ← image_smul_set]
  ext y
  simp only [mem_inter_iff, mem_image, SetLike.mem_coe, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hyΛ⟩
    exact ⟨x, ⟨hx, (hΛ x).1 hyΛ⟩, rfl⟩
  · rintro ⟨x, ⟨hx, hxΛ⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, (hΛ x).2 hxΛ⟩

/-- **Every successive minimum is unchanged:** `λ_i(V K) = λ_i(K)`. -/
theorem successiveMinimum_image (K : Set (Fin n → ℝ)) (i : ℕ) :
    DiscreteMinkowski.successiveMinimum (V '' K) (standardIntegerLattice n) i =
      DiscreteMinkowski.successiveMinimum K (standardIntegerLattice n) i := by
  rw [DiscreteMinkowski.successiveMinimum_eq_sInf, DiscreteMinkowski.successiveMinimum_eq_sInf]
  congr 1
  ext r
  simp only [DiscreteMinkowski.minimaSet, mem_setOf_eq]
  refine and_congr_right fun _ => ?_
  rw [scaledLatticeSpan_image V hΛ K r, LinearEquiv.finrank_map_eq]

omit hΛ in
/-- **`vol(V K) = vol(K)`** for `|det V| = 1`. -/
theorem volume_image_of_det (hdet : |LinearMap.det (V : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))| = 1)
    (K : Set (Fin n → ℝ)) : volume (V '' K) = volume K := by
  rw [show (V '' K) = (V : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) '' K from rfl,
    Measure.addHaar_image_linearMap, hdet, ENNReal.ofReal_one, one_mul]

omit hΛ in
theorem isPaperConvexBody_image {K : Set (Fin n → ℝ)}
    (hK : DiscreteMinkowski.IsPaperConvexBody K) :
    DiscreteMinkowski.IsPaperConvexBody (V '' K) := by
  set W := (LinearEquiv.toContinuousLinearEquiv V)
  have hW : ∀ x, W x = V x := fun _ => rfl
  refine ⟨?_, hK.2.1.linear_image (V : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)), ?_⟩
  · have := W.lipschitz.isBounded_image hK.1
    simpa [hW] using this
  · obtain ⟨x, hx⟩ := hK.2.2
    refine ⟨V x, ?_⟩
    have h := W.toHomeomorph.image_interior K
    have : (W : (Fin n → ℝ) → (Fin n → ℝ)) '' K = V '' K := by ext; simp [hW]
    rw [← this]
    rw [show (W.toHomeomorph : (Fin n → ℝ) → (Fin n → ℝ)) = W from rfl] at h
    rw [← h]
    exact ⟨x, hx, rfl⟩

omit hΛ in
theorem isCompact_image {K : Set (Fin n → ℝ)} (hK : IsCompact K) : IsCompact (V '' K) :=
  hK.image (LinearEquiv.toContinuousLinearEquiv V).continuous

end

end LatticeVolumeInterpolation
