import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.EuclideanDomain.Int

/-!
# A unimodular change of coordinates that makes independent integer vectors triangular

Catalog item `hermite_normal_form_adapted_basis` (Sec. 3, first sentence of the proof of
Theorem 3.1): for linearly independent `v_1, ..., v_n ∈ ℤ^n` there is a unimodular `U` with
`[U v_1, ..., U v_n]` upper triangular. The paper cites the Hermite normal form (Schrijver,
Sec. 4.1, applied to the transpose); Mathlib does not have it, and only this consequence is
used, so it is proved directly: `U` is an automorphism of the `ℤ`-module `ℤ^n` with
`(U v_i)_l = 0` whenever `i < l` (indices from `0`).

The proof is by induction on `n`. Mathlib's Smith normal form of the rank-one submodule
`span_ℤ {v_0}` gives a basis of `ℤ^n` in which `v_0` is a multiple of one basis vector;
reordering that basis to put the vector first makes `U_1 v_0` a multiple of `e_0`. The tails
of `U_1 v_1, ..., U_1 v_{n-1}` are again independent, so the induction hypothesis
triangularizes them, and the two changes of coordinates combine.
-/

open Module

namespace LatticeVolumeInterpolation

/-- **Triangularization over `ℤ`.** -/
theorem exists_triangularizing :
    ∀ (n : ℕ) (v : Fin n → (Fin n → ℤ)), LinearIndependent ℤ v →
      ∃ U : (Fin n → ℤ) ≃ₗ[ℤ] (Fin n → ℤ), ∀ i l : Fin n, i < l → U (v i) l = 0
  | 0, _, _ => ⟨LinearEquiv.refl ℤ _, fun i => i.elim0⟩
  | m + 1, v, hv => by
    classical
    have hv0 : v 0 ≠ 0 := hv.ne_zero 0
    set N : Submodule ℤ (Fin (m + 1) → ℤ) := Submodule.span ℤ {v 0} with hN
    obtain ⟨r, S⟩ := N.smithNormalForm (Pi.basisFun ℤ (Fin (m + 1)))
    -- `N` has rank one, so the Smith basis of `N` has one vector
    have hrank : finrank ℤ N = 1 := by
      have hli : LinearIndependent ℤ (fun _ : Fin 1 => v 0) :=
        linearIndependent_unique_iff.2 hv0
      have := finrank_span_eq_card hli
      rwa [Set.range_const, Fintype.card_fin] at this
    have hr : r = 1 := by
      have := finrank_eq_card_basis S.bN
      rw [hrank, Fintype.card_fin] at this
      exact this.symm
    subst hr
    set k₀ : Fin (m + 1) := S.f 0 with hk₀
    -- `v 0` is a multiple of the basis vector `bM k₀`
    obtain ⟨c, hc⟩ : ∃ c : ℤ, v 0 = c • S.bM k₀ := by
      have hmem : v 0 ∈ N := Submodule.subset_span rfl
      have hrep := S.bN.sum_repr ⟨v 0, hmem⟩
      rw [Fin.sum_univ_one] at hrep
      refine ⟨S.bN.repr ⟨v 0, hmem⟩ 0 * S.a 0, ?_⟩
      have h := congrArg Subtype.val hrep
      simp only [Submodule.coe_smul] at h
      rw [S.snf 0, smul_smul] at h
      exact h.symm
    -- reorder the basis so that `bM k₀` comes first
    set σ : Equiv.Perm (Fin (m + 1)) := Equiv.swap 0 k₀ with hσ
    set bM' := S.bM.reindex σ with hbM'
    have hbM'0 : bM' 0 = S.bM k₀ := by
      simp [hbM', hσ, Basis.reindex_apply, Equiv.swap_apply_left]
    set U₁ := bM'.equivFun with hU₁
    have hU₁v0 : U₁ (v 0) = c • Pi.single 0 1 := by
      rw [hc, map_smul, ← hbM'0, hU₁, Basis.equivFun_apply, Basis.repr_self,
        Finsupp.single_eq_pi_single]
    -- the tails of the other vectors are independent
    set w : Fin m → (Fin m → ℤ) := fun i => Fin.tail (U₁ (v i.succ)) with hw
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hv0 (by rw [hc, zero_smul])
    have hw_ind : LinearIndependent ℤ w := by
      rw [Fintype.linearIndependent_iff] at hv ⊢
      intro g hg i
      set d := (∑ j, g j • U₁ (v j.succ)) 0 with hd
      have htail : Fin.tail (∑ j, g j • U₁ (v j.succ)) = 0 := by
        funext l
        have := congrFun hg l
        simpa [hw, Fin.tail, Finset.sum_apply] using this
      have hsum : ∑ j, g j • U₁ (v j.succ) = d • Pi.single 0 1 := by
        funext l
        refine Fin.cases ?_ (fun l => ?_) l
        · simp [hd]
        · have := congrFun htail l
          simp only [Fin.tail, Pi.zero_apply] at this
          simpa [Finset.sum_apply] using this
      -- a vanishing combination of all the `v`
      set G : Fin (m + 1) → ℤ := Fin.cons (-d) (fun j => c * g j) with hG
      have hG0 : ∑ j, G j • v j = 0 := by
        apply U₁.injective
        rw [map_zero, map_sum, Fin.sum_univ_succ]
        simp only [hG, Fin.cons_zero, Fin.cons_succ, map_smul, hU₁v0]
        have : ∑ j : Fin m, (c * g j) • U₁ (v j.succ) = c • (d • Pi.single 0 1) := by
          rw [← hsum, Finset.smul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [smul_smul]
        rw [this, smul_smul, smul_smul, neg_mul, neg_smul, mul_comm, neg_add_cancel]
      have := hv G hG0 i.succ
      simp only [hG, Fin.cons_succ] at this
      exact (mul_eq_zero.1 this).resolve_left hc0
    obtain ⟨U', hU'⟩ := exists_triangularizing m w hw_ind
    -- combine: keep the first coordinate, apply `U'` to the tail
    set U₂ : (Fin (m + 1) → ℤ) ≃ₗ[ℤ] (Fin (m + 1) → ℤ) :=
      ((Fin.consLinearEquiv ℤ (fun _ : Fin (m + 1) => ℤ)).symm.trans
        ((LinearEquiv.refl ℤ ℤ).prodCongr U')).trans
        (Fin.consLinearEquiv ℤ (fun _ : Fin (m + 1) => ℤ)) with hU₂
    have hU₂apply : ∀ x : Fin (m + 1) → ℤ, U₂ x = Fin.cons (x 0) (U' (Fin.tail x)) := by
      intro x
      rfl
    refine ⟨U₁.trans U₂, fun i l hil => ?_⟩
    rw [LinearEquiv.trans_apply, hU₂apply]
    obtain ⟨l, rfl⟩ : ∃ l' : Fin m, l = l'.succ := by
      refine ⟨l.pred (fun h => ?_), (Fin.succ_pred _ _).symm⟩
      rw [h] at hil; exact absurd hil (Fin.not_lt_zero i)
    rw [Fin.cons_succ]
    refine Fin.cases ?_ (fun i hil => ?_) i hil
    · intro _
      have : Fin.tail (U₁ (v 0)) = 0 := by
        funext l'; simp [hU₁v0, Fin.tail]
      rw [this, map_zero]; rfl
    · exact hU' i l (Fin.succ_lt_succ_iff.1 hil)

end LatticeVolumeInterpolation
