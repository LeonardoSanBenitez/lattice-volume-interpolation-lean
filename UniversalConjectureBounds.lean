import PaperConjectures
import MinimaDifferenceAvoidance
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Full-dimensional lattice intersections and the conditional universal bounds

Catalog items `universal_bound_from_conjecture_upper` and
`universal_bound_from_conjecture_lower`, the unnumbered universal estimates
after Theorem 1.3, derived from Eqs. (1.5) and (1.7).

Full dimension is expressed by the affine span of the lattice intersection.
It is not replaced by an assumption on the successive minima.
-/

open Set Module MeasureTheory AffineSubspace
open scoped BigOperators Pointwise

namespace LatticeVolumeInterpolation

theorem last_minimum_le_two_of_full_lattice_intersection {n : ℕ}
    {K : Set (Fin n → ℝ)}
    (hfull : affineSpan ℝ (K ∩ (standardIntegerLattice n : Set (Fin n → ℝ))) = ⊤) :
    DiscreteMinkowski.successiveMinimum K (standardIntegerLattice n) n ≤ 2 := by
  let S := K ∩ (standardIntegerLattice n : Set (Fin n → ℝ))
  have hspan : vectorSpan ℝ S = ⊤ :=
    vectorSpan_eq_top_of_affineSpan_eq_top ℝ _ _ hfull
  have hsub : vectorSpan ℝ S ≤ DiscreteMinkowski.scaledLatticeSpan K (standardIntegerLattice n) 2 := by
    rw [vectorSpan_def]
    apply Submodule.span_le.mpr
    rintro z ⟨x, hx, y, hy, rfl⟩
    apply Submodule.subset_span
    refine ⟨?_, (standardIntegerLattice n).sub_mem hx.2 hy.2⟩
    have hh := mem_smul_halfDifference_of_scaled_difference hx.1 hy.1
      (by norm_num : (1 : ℝ) ≠ 0) (by simp : x - y = (1 : ℝ) • (x - y))
    simpa only [div_one, vsub_eq_sub] using hh
  have heq : DiscreteMinkowski.scaledLatticeSpan K (standardIntegerLattice n) 2 = ⊤ := by
    apply top_unique
    rwa [hspan] at hsub
  apply csInf_le (DiscreteMinkowski.bddBelow_minimaSet K (standardIntegerLattice n) n)
  refine ⟨by norm_num, ?_⟩
  rw [heq, finrank_top, Module.finrank_fin_fun]

theorem last_minimum_le_one_of_symmetric_full_lattice_intersection {n : ℕ}
    {K : Set (Fin n → ℝ)} (hv : Convex ℝ K) (hsym : DiscreteMinkowski.IsOriginSymmetric K)
    (hfull : affineSpan ℝ (K ∩ (standardIntegerLattice n : Set (Fin n → ℝ))) = ⊤) :
    DiscreteMinkowski.successiveMinimum K (standardIntegerLattice n) n ≤ 1 := by
  let S := K ∩ (standardIntegerLattice n : Set (Fin n → ℝ))
  have hspan : vectorSpan ℝ S = ⊤ :=
    vectorSpan_eq_top_of_affineSpan_eq_top ℝ _ _ hfull
  have hsub : vectorSpan ℝ S ≤ Submodule.span ℝ S := by
    rw [vectorSpan_def]
    apply Submodule.span_le.mpr
    rintro z ⟨x, hx, y, hy, rfl⟩
    exact Submodule.sub_mem _ (Submodule.subset_span hx) (Submodule.subset_span hy)
  have heq : DiscreteMinkowski.scaledLatticeSpan K (standardIntegerLattice n) 1 = ⊤ := by
    rw [DiscreteMinkowski.scaledLatticeSpan, DiscreteMinkowski.halfDifferenceBody_eq_self hv hsym,
      one_smul]
    apply top_unique
    rwa [hspan] at hsub
  apply csInf_le (DiscreteMinkowski.bddBelow_minimaSet K (standardIntegerLattice n) n)
  refine ⟨by norm_num, ?_⟩
  rw [heq, finrank_top, Module.finrank_fin_fun]

private theorem prod_index_factors_eq_factorial (n : ℕ) :
    (∏ i : Fin n, (1 + (i.1 + 1 : ℝ))) = ((n + 1).factorial : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    ring

/-- The paper's Blichfeldt-type consequence of Eq. (1.5). -/
theorem universal_upper_bound_of_ratio_conjecture {n : ℕ}
    (hconj : BHWRatioUpperConjecture n) {K : Set (Fin n → ℝ)} (hK : IsConvexBody K)
    (hfull : affineSpan ℝ (K ∩ (standardIntegerLattice n : Set (Fin n → ℝ))) = ⊤) :
    ((DiscreteMinkowski.latticePoints K (standardIntegerLattice n)).ncard : ℝ) ≤
      ((n + 1).factorial : ℝ) * (volume K).toReal := by
  have hb := (isConvexBody_iff K).mp hK
  have hlast := last_minimum_le_two_of_full_lattice_intersection hfull
  have hi : ∀ i : Fin n,
      DiscreteMinkowski.successiveMinimum K (standardIntegerLattice n) (i.1 + 1) ≤ 2 := by
    intro i
    have hh := DiscreteMinkowski.successiveMinimum_mono_of_le_finrank
      (Λ := standardIntegerLattice n) hb.2 (i := i.1 + 1) (j := n)
      (by omega) (by rw [Module.finrank_fin_fun])
    exact hh.trans hlast
  have hprod : (∏ i : Fin n, (1 + (i.1 + 1 : ℝ) *
      DiscreteMinkowski.successiveMinimum K (standardIntegerLattice n) (i.1 + 1) / 2)) ≤
      ((n + 1).factorial : ℝ) := by
    rw [← prod_index_factors_eq_factorial]
    apply Finset.prod_le_prod
    · intro i _
      have hh := DiscreteMinkowski.successiveMinimum_nonneg K (standardIntegerLattice n) (i.1 + 1)
      positivity
    · intro i _
      have hh := hi i
      have hicoe : (0 : ℝ) ≤ (i.1 + 1 : ℝ) := by positivity
      nlinarith
  calc
    _ ≤ (volume K).toReal * _ := hconj K hK
    _ ≤ (volume K).toReal * ((n + 1).factorial : ℝ) :=
      mul_le_mul_of_nonneg_left hprod ENNReal.toReal_nonneg
    _ = _ := mul_comm _ _

/-- The paper's van der Corput-type consequence of Eq. (1.7). -/
theorem universal_lower_bound_of_ratio_conjecture {n : ℕ}
    (hconj : BHWSymmetricRatioLowerConjecture n) {K : Set (Fin n → ℝ)}
    (hK : IsConvexBody K) (hsym : DiscreteMinkowski.IsOriginSymmetric K)
    (hfull : affineSpan ℝ (K ∩ (standardIntegerLattice n : Set (Fin n → ℝ))) = ⊤) :
    (2 : ℝ)⁻¹ ^ n * (volume K).toReal ≤
      ((DiscreteMinkowski.latticePoints (interior K) (standardIntegerLattice n)).ncard : ℝ) := by
  have hb := (isConvexBody_iff K).mp hK
  have hlast := last_minimum_le_one_of_symmetric_full_lattice_intersection hb.2.2.1 hsym hfull
  have hi : ∀ i : Fin n,
      DiscreteMinkowski.successiveMinimum K (standardIntegerLattice n) (i.1 + 1) ≤ 1 := by
    intro i
    have hh := DiscreteMinkowski.successiveMinimum_mono_of_le_finrank
      (Λ := standardIntegerLattice n) hb.2 (i := i.1 + 1) (j := n)
      (by omega) (by rw [Module.finrank_fin_fun])
    exact hh.trans hlast
  have hprod : (2 : ℝ)⁻¹ ^ n ≤ ∏ i : Fin n,
      (1 - DiscreteMinkowski.successiveMinimum K (standardIntegerLattice n) (i.1 + 1) / 2) := by
    have hh : (∏ _i : Fin n, (2 : ℝ)⁻¹) ≤ ∏ i : Fin n,
        (1 - DiscreteMinkowski.successiveMinimum K (standardIntegerLattice n) (i.1 + 1) / 2) := by
      apply Finset.prod_le_prod
      · intro i _; norm_num
      · intro i _; have hh := hi i; norm_num; linarith
    simpa using hh
  calc
    _ = (volume K).toReal * (2 : ℝ)⁻¹ ^ n := mul_comm _ _
    _ ≤ (volume K).toReal * _ := mul_le_mul_of_nonneg_left hprod ENNReal.toReal_nonneg
    _ ≤ _ := hconj K hK hsym (by linarith)

end LatticeVolumeInterpolation
