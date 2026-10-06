import PropOneSix
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Data.Set.Card.Arithmetic

/-!
# Theorem 1.3 and Claim 3: a reverse of Schymura's inequality

Catalog items `claim_3_translation_projection_bound` and `theorem_1_3_reverse_schymura`.

The paper's Claim 3: for an `n`-dimensional lattice `Λ`, independent `b_1, ..., b_n ∈ Λ`, a
convex bounded `K` and `t = ∑ α_i b_i`,

  `G_Λ(K + t) ≤ ∑_{I ⊆ supp(t)} G_{Λ | L_I^⊥}(K | L_I^⊥)`,  `L_I = span{b_i : i ∈ I}`.

**Projections as quotients.** Orthogonal projection onto `L^⊥` is a bijection of `L^⊥` onto
`E / L`, carrying `K | L^⊥` and `Λ | L^⊥` to the images of `K` and `Λ`; so the count
`G_{Λ|L^⊥}(K|L^⊥)` is the number of classes mod `L` that contain a point of `K` and a point of
`Λ`. The induction is carried out with these counts, relative to an already quotiented subspace
`M`: then the paper's "induction hypothesis applied to `K|b_j^⊥`, `Λ|b_j^⊥`" is the same
statement for `M ⊔ ℝ b_j`, and `(M ⊔ ℝ b_j) ⊔ L_I = M ⊔ L_{I ∪ {j}}` is an equality of subspaces
rather than an isomorphism. Counts are `encard`, so an infinite count is `⊤` and never breaks an
inequality.

**The one-direction step**, the paper's (4.4): `G(K + α b) ≤ G(K) + G(K | b^⊥)`. On each line
parallel to `b` the body is an interval `J` and the lattice a coset of a subgroup `H ≤ ℝ`;
translating `J` adds at most one point of the coset (`encard_shift_coset_le`). The paper
argues this for the integers, where it is the statement that equal-length intervals contain
counts differing by at most one; here `H` is cyclic or dense, and the dense case is handled
directly, so no discreteness of projected lattices is needed.
-/

open MeasureTheory Set Module
open scoped ENNReal Pointwise

namespace LatticeVolumeInterpolation

noncomputable section

/-- A dense subset of `ℝ` meets every non-degenerate open interval in infinitely many points. -/
theorem infinite_Ioo_inter_of_dense {D : Set ℝ} (hD : Dense D) {a b : ℝ} (hab : a < b) :
    (Ioo a b ∩ D).Infinite := by
  intro hfin
  rcases (Ioo a b ∩ D).eq_empty_or_nonempty with hemp | hne
  · obtain ⟨c, hcD, hac, hcb⟩ := hD.exists_between hab
    exact (Set.eq_empty_iff_forall_notMem.1 hemp) c ⟨⟨hac, hcb⟩, hcD⟩
  · set F := hfin.toFinset
    have hFne : F.Nonempty := by simpa [F] using hne
    set m := F.min' hFne
    have hm : m ∈ Ioo a b ∩ D := (hfin.mem_toFinset).1 (F.min'_mem hFne)
    obtain ⟨c, hcD, hac, hcm⟩ := hD.exists_between hm.1.1
    have hcmem : c ∈ F := (hfin.mem_toFinset).2 ⟨⟨hac, hcm.trans hm.1.2⟩, hcD⟩
    exact absurd (F.min'_le c hcmem) (not_le.2 hcm)

/-- **One dimension.** Translating a convex `J ⊆ ℝ` by `α` adds at most one point of a coset
`s₀ + H` of an additive subgroup `H ≤ ℝ`. -/
theorem encard_shift_coset_le {J : Set ℝ} (hJ : Convex ℝ J) (H : AddSubgroup ℝ) (s₀ α : ℝ) :
    ({x | x - α ∈ J} ∩ {x | x - s₀ ∈ H}).encard ≤ (J ∩ {x | x - s₀ ∈ H}).encard + 1 := by
  have hord := convex_iff_ordConnected.1 hJ
  rcases AddSubgroup.dense_or_cyclic H with hdense | ⟨g, hg⟩
  · -- dense: either `J` is a point or empty, or the right side is infinite
    by_cases hsub : J.Subsingleton
    · have : ({x | x - α ∈ J} ∩ {x | x - s₀ ∈ H}).Subsingleton := by
        intro x hx y hy
        have := hsub hx.1 hy.1
        linarith
      calc _ ≤ 1 := Set.encard_le_one_iff_subsingleton.2 this
        _ ≤ _ := le_add_self
    · obtain ⟨a, ha, b, hb, hab⟩ := Set.not_subsingleton_iff.1 hsub
      wlog hlt : a < b generalizing a b
      · exact this b hb a ha (Ne.symm hab) (lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hab))
      have hcoset : Dense {x : ℝ | x - s₀ ∈ H} := by
        intro y
        rw [Metric.mem_closure_iff]
        intro ε hε
        obtain ⟨c, hcH, hc1, hc2⟩ := hdense.exists_between
          (show y - s₀ - ε < y - s₀ + ε by linarith)
        refine ⟨c + s₀, by simpa using hcH, ?_⟩
        rw [Real.dist_eq, abs_lt]; constructor <;> linarith
      have hinf : (J ∩ {x | x - s₀ ∈ H}).Infinite :=
        (infinite_Ioo_inter_of_dense hcoset hlt).mono
          (inter_subset_inter_left _ (Ioo_subset_Icc_self.trans (hord.out ha hb)))
      rw [hinf.encard_eq]
      simp
  · -- cyclic: `H = ℤ g`; make `g ≥ 0`
    wlog hg0 : 0 ≤ g generalizing g
    · refine this (-g) ?_ (by linarith)
      rw [hg, ← AddSubgroup.zmultiples_eq_closure, ← AddSubgroup.zmultiples_eq_closure,
        AddSubgroup.zmultiples_neg]
    rw [← AddSubgroup.zmultiples_eq_closure] at hg
    have hmemH : ∀ y, y ∈ H ↔ ∃ k : ℤ, y = k * g := by
      intro y; rw [hg, AddSubgroup.mem_zmultiples_iff]
      constructor
      · rintro ⟨k, rfl⟩; exact ⟨k, by simp⟩
      · rintro ⟨k, rfl⟩; exact ⟨k, by simp⟩
    rcases hg0.eq_or_lt with hg00 | hgpos
    · -- `H = 0`: the coset is a single point
      have : ({x | x - α ∈ J} ∩ {x | x - s₀ ∈ H}).Subsingleton := by
        intro x hx y hy
        obtain ⟨k, hk⟩ := (hmemH _).1 hx.2
        obtain ⟨l, hl⟩ := (hmemH _).1 hy.2
        rw [← hg00, mul_zero] at hk hl
        linarith
      calc _ ≤ 1 := Set.encard_le_one_iff_subsingleton.2 this
        _ ≤ _ := le_add_self
    -- reduce the shift to `β ∈ [0, g)`
    set q : ℤ := ⌊α / g⌋
    set β := α - q * g with hβ
    have hβ0 : 0 ≤ β := by
      have := Int.floor_le (α / g)
      rw [hβ]; have := mul_le_mul_of_nonneg_right this hgpos.le
      rw [div_mul_cancel₀ _ hgpos.ne'] at this; linarith
    have hβg : β < g := by
      have := Int.lt_floor_add_one (α / g)
      rw [hβ]; have := mul_lt_mul_of_pos_right this hgpos
      rw [div_mul_cancel₀ _ hgpos.ne', add_mul, one_mul] at this; linarith
    set P := {x : ℝ | x - s₀ ∈ H}
    have hPshift : ∀ x (k : ℤ), x ∈ P ↔ x + k * g ∈ P := by
      intro x k
      simp only [P, mem_setOf_eq, hmemH]
      constructor
      · rintro ⟨l, hl⟩; exact ⟨l + k, by push_cast; linarith⟩
      · rintro ⟨l, hl⟩; exact ⟨l - k, by push_cast; linarith⟩
    -- translating by `q g` identifies the two shifted sets
    set A := {x : ℝ | x - β ∈ J} ∩ P
    have hbij : {x | x - α ∈ J} ∩ P = (fun x => x + q * g) '' A := by
      ext x
      simp only [mem_inter_iff, mem_setOf_eq, mem_image, A]
      constructor
      · rintro ⟨hx, hxP⟩
        refine ⟨x - q * g, ⟨?_, ?_⟩, by ring⟩
        · rw [hβ] at *; convert hx using 1; ring
        · have := (hPshift (x - q * g) q).2; simp only [sub_add_cancel] at this; exact this hxP
      · rintro ⟨y, ⟨hy, hyP⟩, rfl⟩
        refine ⟨?_, (hPshift y q).1 hyP⟩
        rw [hβ] at hy; convert hy using 1; ring
    rw [hbij, (add_left_injective _).injOn.encard_image]
    -- all but the lowest point of `A` move down by `g` into `J ∩ P`
    set A' := {x ∈ A | x - g ∈ A}
    have hmaps : MapsTo (fun x => x - g) A' (J ∩ P) := by
      rintro x ⟨⟨hxJ, hxP⟩, ⟨hx'J, -⟩⟩
      refine ⟨?_, ?_⟩
      · refine hord.out hx'J hxJ ⟨?_, ?_⟩ <;> linarith
      · have := (hPshift (x - g) 1).2; simp only [Int.cast_one, one_mul, sub_add_cancel] at this
        exact this hxP
    have h1 : A'.encard ≤ (J ∩ P).encard :=
      Set.encard_le_encard_of_injOn hmaps (sub_left_injective).injOn
    have h2 : (A \ A').encard ≤ 1 := by
      rw [Set.encard_le_one_iff]
      intro x y hx hy
      by_contra hxy
      wlog hlt : x < y generalizing x y
      · exact this y x hy hx (Ne.symm hxy) (lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hxy))
      -- `y - g` lies between `x` and `y`, so it is in `A`
      obtain ⟨k, hk⟩ := (hmemH _).1 hx.1.2
      obtain ⟨l, hl⟩ := (hmemH _).1 hy.1.2
      have hkl : (k : ℝ) < l := by
        have : (k : ℝ) * g < l * g := by linarith
        exact lt_of_mul_lt_mul_right this hgpos.le
      have hkl' : (k : ℝ) + 1 ≤ l := by exact_mod_cast Int.add_one_le_of_lt (by exact_mod_cast hkl)
      have hyg : x ≤ y - g := by nlinarith
      apply hy.2
      refine ⟨hy.1, ?_, ?_⟩
      · have hxJ : x - β ∈ J := hx.1.1
        have hyJ : y - β ∈ J := hy.1.1
        change y - g - β ∈ J
        exact hord.out hxJ hyJ ⟨by linarith, by linarith⟩
      · have := (hPshift (y - g) 1).2; simp only [Int.cast_one, one_mul, sub_add_cancel] at this
        exact this hy.1.2
    have hsplit : A.encard ≤ (A \ A').encard + A'.encard := by
      calc A.encard = ((A \ A') ∪ A').encard := by
            rw [Set.sdiff_union_of_subset (fun x hx => hx.1)]
        _ ≤ _ := Set.encard_union_le _ _
    calc A.encard ≤ (A \ A').encard + A'.encard := hsplit
      _ ≤ 1 + (J ∩ P).encard := add_le_add h2 h1
      _ = (J ∩ P).encard + 1 := add_comm _ _

end

end LatticeVolumeInterpolation
