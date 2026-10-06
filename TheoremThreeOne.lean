import ClaimOne
import Unimodular
import ShakingInterior

/-!
# Theorem 3.1: the anti-blocking companion of a convex body

Catalog item `theorem_3_1_anti_blocking_reduction`. For every `K ∈ K^n` there is an
anti-blocking convex body `A ⊆ ℝ^n_{≥0}` with

1. `vol(K) = vol(A)`,
2. `G(K) ≤ G(A)`,
3. `G(int K) ≥ G(int A)` and
4. `λ_i(K) ≥ λ_i(A)` for all `i ∈ [n]`.

`theorem_3_1` proves all four conclusions; conclusion 3 uses Lemma 3.2 vi)
(`ShakingInterior.lean`).

The proof is the paper's. Take independent lattice vectors `v_i` with `|v_i|_{cs(K)} = λ_i(K)`:
the minimal flag of the dependency, whose vectors attain the minima
(`gauge_flagVector_le_successiveMinimum`). A unimodular change of coordinates makes their matrix
upper triangular (`exists_triangularizing`, `realize_unimodular`) and changes none of the four
functionals (`Unimodular.lean`). Shaking successively along `e_1, ..., e_n` then gives the
anti-blocking body (Claim 2) with no larger minima (Claim 1), the same volume and no fewer
lattice points (Lemma 3.2 ii), v)).
-/

open MeasureTheory Set Module
open scoped Pointwise

namespace LatticeVolumeInterpolation

noncomputable section

variable {n : ℕ}

/-- An independent family whose matrix is upper triangular has a non-zero diagonal. -/
theorem triangular_diag_ne_zero {u : Fin n → Fin n → ℝ} (hu : LinearIndependent ℝ u)
    (htri : ∀ i l : Fin n, i < l → u i l = 0) (i : Fin n) : u i i ≠ 0 := by
  classical
  intro hii
  set J : Finset (Fin n) := Finset.univ.filter fun l => l < i with hJ
  set b : {k // k ∈ Finset.Iic i} → (Fin n → ℝ) := fun k => u k.1 with hb
  have hbind : LinearIndependent ℝ b :=
    hu.comp (fun k : {k // k ∈ Finset.Iic i} => k.1) (fun k l h => Subtype.ext h)
  have hsupp : Submodule.span ℝ (Set.range b) ≤ supportedOn J := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩ l hl
    simp only [hJ, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hl
    have hk : k.1 ≤ i := Finset.mem_Iic.1 k.2
    rcases hl.eq_or_lt with hil | hlt
    · subst hil
      rcases hk.eq_or_lt with hki | hki
      · simp only [hb]; rw [hki]; exact hii
      · exact htri k.1 i hki
    · exact htri k.1 l (lt_of_le_of_lt hk hlt)
  have h1 := finrank_le_card_of_le_supportedOn _ J hsupp
  rw [finrank_span_eq_card hbind, Fintype.card_coe, Fin.card_Iic] at h1
  have h2 : J.card ≤ i.1 := by
    have : J = Finset.Iio i := by ext l; simp [hJ]
    rw [this, Fin.card_Iio]
  omega

/-- The minimal flag vectors of a convex body are linearly independent. -/
theorem linearIndependent_flagVector {K : Set (Fin n → ℝ)}
    (hKb : DiscreteMinkowski.IsPaperConvexBody K) :
    LinearIndependent ℝ (fun k : Fin n =>
      DiscreteMinkowski.flagVector K (standardIntegerLattice n) k.1) := by
  have hdim : finrank ℝ (Fin n → ℝ) = n := Module.finrank_fin_fun ℝ
  refine linearIndependent_of_top_le_span_of_card_eq_finrank ?_ (by rw [Fintype.card_fin, hdim])
  have htop := DiscreteMinkowski.flagSpan_top (Λ := standardIntegerLattice n) hKb
  rw [hdim] at htop
  rw [← htop]
  exact DiscreteMinkowski.flagSpan_le_span
    (S := Set.range fun k : Fin n => DiscreteMinkowski.flagVector K (standardIntegerLattice n) k.1)
    n fun m hm => ⟨⟨m, hm⟩, rfl⟩

/-- Lemma 3.2 vi) along the successive shakings: `G(int K_k) ≤ G(int K)`. -/
theorem ncard_latticePoints_interior_shakeUpTo_le {K : Set (Fin n → ℝ)} (hKc : IsCompact K)
    (hKb : DiscreteMinkowski.IsPaperConvexBody K) :
    ∀ k, (DiscreteMinkowski.latticePoints (interior (shakeUpTo K k))
      (standardIntegerLattice n)).ncard ≤
      (DiscreteMinkowski.latticePoints (interior K) (standardIntegerLattice n)).ncard
  | 0 => le_rfl
  | k + 1 => by
    by_cases h : k < n
    · rw [shakeUpTo_succ_of_lt K h]
      have hb := isPaperConvexBody_shakeUpTo hKc hKb k
      exact (ncard_latticePoints_interior_coordShaking_le (isCompact_shakeUpTo hKc k) hb.2.1
        hb.2.2 _).trans (ncard_latticePoints_interior_shakeUpTo_le hKc hKb k)
    · rw [shakeUpTo_succ_of_le K (not_lt.1 h)]
      exact ncard_latticePoints_interior_shakeUpTo_le hKc hKb k

/-- A linear automorphism carries interiors along. -/
theorem interior_image_linearEquiv (V : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) (K : Set (Fin n → ℝ)) :
    interior (V '' K) = V '' interior K := by
  set W := LinearEquiv.toContinuousLinearEquiv V
  have h := W.toHomeomorph.image_interior K
  have hW : ∀ S : Set (Fin n → ℝ), (W.toHomeomorph : (Fin n → ℝ) → (Fin n → ℝ)) '' S = V '' S :=
    fun S => rfl
  rw [hW, hW] at h
  exact h.symm

/-- **Theorem 3.1.** -/
theorem theorem_3_1 {K : Set (Fin n → ℝ)} (hKc : IsCompact K)
    (hKb : DiscreteMinkowski.IsPaperConvexBody K) :
    ∃ A : Set (Fin n → ℝ), IsCompact A ∧ DiscreteMinkowski.IsPaperConvexBody A ∧
      IsAntiBlocking A ∧ volume A = volume K ∧
      (DiscreteMinkowski.latticePoints K (standardIntegerLattice n)).ncard ≤
        (DiscreteMinkowski.latticePoints A (standardIntegerLattice n)).ncard ∧
      (DiscreteMinkowski.latticePoints (interior A) (standardIntegerLattice n)).ncard ≤
        (DiscreteMinkowski.latticePoints (interior K) (standardIntegerLattice n)).ncard ∧
      ∀ i : Fin n,
        DiscreteMinkowski.successiveMinimum A (standardIntegerLattice n) (i.1 + 1) ≤
          DiscreteMinkowski.successiveMinimum K (standardIntegerLattice n) (i.1 + 1) := by
  classical
  have hdim : finrank ℝ (Fin n → ℝ) = n := Module.finrank_fin_fun ℝ
  set v : Fin n → (Fin n → ℝ) := fun k =>
    DiscreteMinkowski.flagVector K (standardIntegerLattice n) k.1 with hv
  have hvΛ : ∀ k, v k ∈ standardIntegerLattice n := fun k =>
    DiscreteMinkowski.flagVector_mem k.1
      (DiscreteMinkowski.greedyChoice_flagSpan hKb (by rw [hdim]; exact k.2))
  have hvg : ∀ k, gauge (DiscreteMinkowski.halfDifferenceBody K) (v k) ≤
      DiscreteMinkowski.successiveMinimum K (standardIntegerLattice n) (k.1 + 1) := fun k =>
    gauge_flagVector_le_successiveMinimum hKb (by rw [hdim]; exact k.2)
  have hvind : LinearIndependent ℝ v := linearIndependent_flagVector hKb
  -- integer coordinates, independent over `ℤ`
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
  obtain ⟨U, hU⟩ := exists_triangularizing n z hzind
  obtain ⟨V, hV, hVs, hdet⟩ := realize_unimodular U
  have hΛ := mem_lattice_iff_of_realize V hV hVs
  set K' := V '' K with hK'
  have hK'c : IsCompact K' := isCompact_image V hKc
  have hK'b : DiscreteMinkowski.IsPaperConvexBody K' := isPaperConvexBody_image V hKb
  set u : Fin n → (Fin n → ℝ) := fun k => V (v k) with hu
  have huΛ : ∀ k, u k ∈ standardIntegerLattice n := fun k => (hΛ (v k)).2 (hvΛ k)
  have htri : ∀ i l : Fin n, i < l → u i l = 0 := by
    intro i l hil
    simp only [hu, hz, hV, castCoords]
    exact_mod_cast hU i l hil
  have huind : LinearIndependent ℝ u := hvind.map' (V : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (LinearMap.ker_eq_bot.2 V.injective)
  have hdiag : ∀ i, u i i ≠ 0 := triangular_diag_ne_zero huind htri
  have hug : ∀ k, gauge (DiscreteMinkowski.halfDifferenceBody K') (u k) ≤
      DiscreteMinkowski.successiveMinimum K' (standardIntegerLattice n) (k.1 + 1) := by
    intro k
    rw [successiveMinimum_image V hΛ, hK', halfDifferenceBody_image, hu,
      gauge_image_apply]
    exact hvg k
  refine ⟨shakeUpTo K' n, isCompact_shakeUpTo hK'c n, isPaperConvexBody_shakeUpTo hK'c hK'b n,
    isAntiBlocking_shakeUpTo hK'c hK'b.2.1, ?_, ?_, ?_, ?_⟩
  · rw [volume_shakeUpTo hK'c hK'b.2.1, hK', volume_image_of_det V hdet]
  · rw [← ncard_latticePoints_image V hΛ K]
    exact ncard_latticePoints_le_shakeUpTo hK'c n
  · rw [← ncard_latticePoints_image V hΛ (interior K), ← interior_image_linearEquiv V K]
    exact ncard_latticePoints_interior_shakeUpTo_le hK'c hK'b n
  · intro i
    rw [← successiveMinimum_image V hΛ K]
    exact successiveMinimum_shakeUpTo_le hK'c hK'b u huΛ htri hdiag hug i

end

end LatticeVolumeInterpolation
