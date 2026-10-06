import PropOneSix
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

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

section Quotient

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The number of classes mod `M` that contain a point of `K` and a point of `Λ`: the count
`G_{Λ|M^⊥}(K|M^⊥)` of the paper, written with the quotient by `M`. -/
def classCount (M : Submodule ℝ E) (Λ : AddSubgroup E) (K : Set E) : ℕ∞ :=
  (M.mkQ '' K ∩ M.mkQ '' (Λ : Set E)).encard

/-- On a line `c₀ + ℝ v` of `E / M`, a translate of a convex set adds at most one class. -/
theorem encard_line_shift_le {Q : Type*} [AddCommGroup Q] [Module ℝ Q] {C : Set Q}
    (hC : Convex ℝ C) (L : AddSubgroup Q) (c₀ v : Q) (hv : v ≠ 0) (α : ℝ) :
    ((fun s : ℝ => c₀ + s • v) '' {s | c₀ + s • v ∈ α • {v} + C ∧ c₀ + s • v ∈ L}).encard ≤
      ((fun s : ℝ => c₀ + s • v) '' {s | c₀ + s • v ∈ C ∧ c₀ + s • v ∈ L}).encard + 1 := by
  have hinj : Function.Injective fun s : ℝ => c₀ + s • v := by
    intro s t h
    simpa using smul_left_injective ℝ hv (add_left_cancel h)
  rw [hinj.injOn.encard_image, hinj.injOn.encard_image]
  set J := {s : ℝ | c₀ + s • v ∈ C}
  have hJ : Convex ℝ J := by
    intro s hs t ht a b ha hb hab
    have := hC hs ht ha hb hab
    simp only [J, mem_setOf_eq] at this ⊢
    convert this using 1
    rw [smul_add, smul_add, smul_smul, smul_smul, ← add_add_add_comm, ← add_smul, hab, one_smul,
      ← add_smul]
    simp [smul_eq_mul]
  rcases ({s : ℝ | c₀ + s • v ∈ L}).eq_empty_or_nonempty with hemp | ⟨s₁, hs₁⟩
  · have h0 : ∀ s : ℝ, c₀ + s • v ∉ L := fun s hs => (Set.eq_empty_iff_forall_notMem.1 hemp) s hs
    simp [h0]
  set H : AddSubgroup ℝ := L.comap (LinearMap.toSpanSingleton ℝ Q v).toAddMonoidHom
  have hcoset : ∀ s : ℝ, c₀ + s • v ∈ L ↔ s - s₁ ∈ H := by
    intro s
    simp only [H, AddSubgroup.mem_comap, LinearMap.toAddMonoidHom_coe,
      LinearMap.toSpanSingleton_apply]
    constructor
    · intro hs
      have := L.sub_mem hs hs₁
      convert this using 1; rw [sub_smul]; abel
    · intro hs
      have := L.add_mem hs₁ hs
      convert this using 1; rw [sub_smul]; abel
  have hshift : ∀ s : ℝ, c₀ + s • v ∈ α • ({v} : Set Q) + C ↔ s - α ∈ J := by
    intro s
    simp only [J, mem_setOf_eq, Set.smul_set_singleton, Set.singleton_add]
    constructor
    · rintro ⟨w, hw, hws⟩
      have hws' : α • v + w = c₀ + s • v := hws
      have hweq : w = c₀ + s • v - α • v := by rw [← hws']; abel
      have : c₀ + (s - α) • v = w := by rw [hweq, sub_smul]; abel
      rw [this]; exact hw
    · intro h
      exact ⟨_, h, by rw [sub_smul]; abel_nf⟩
  have h := encard_shift_coset_le hJ H s₁ α
  have e1 : {s : ℝ | c₀ + s • v ∈ α • ({v} : Set Q) + C ∧ c₀ + s • v ∈ L} =
      {x | x - α ∈ J} ∩ {x | x - s₁ ∈ H} := by
    ext s; simp only [mem_setOf_eq, mem_inter_iff, hcoset, hshift]
  have e2 : {s : ℝ | c₀ + s • v ∈ C ∧ c₀ + s • v ∈ L} = J ∩ {x | x - s₁ ∈ H} := by
    ext s; simp only [mem_setOf_eq, mem_inter_iff, hcoset, J]
  rw [e1, e2]
  exact h

end Quotient

section Step

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Two classes mod `M` lie over the same class mod `M ⊔ ℝ b` exactly when they differ by a
multiple of the class of `b`. -/
theorem factor_eq_iff (M : Submodule ℝ E) (b : E) (c c₀ : E ⧸ M) :
    Submodule.factor (le_sup_left : M ≤ M ⊔ Submodule.span ℝ {b}) c =
        Submodule.factor (le_sup_left : M ≤ M ⊔ Submodule.span ℝ {b}) c₀ ↔
      ∃ s : ℝ, c = c₀ + s • M.mkQ b := by
  obtain ⟨x, rfl⟩ := M.mkQ_surjective c
  obtain ⟨x₀, rfl⟩ := M.mkQ_surjective c₀
  rw [Submodule.factor_mk, Submodule.factor_mk]
  simp only [Submodule.mkQ_apply]
  rw [Submodule.Quotient.eq]
  constructor
  · intro h
    obtain ⟨m, hm, w, hw, hmw⟩ := Submodule.mem_sup.1 h
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.1 hw
    refine ⟨s, ?_⟩
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_add, Submodule.Quotient.eq]
    have : x - (x₀ + s • b) = m := by
      rw [show x - (x₀ + s • b) = (x - x₀) - s • b by abel, ← hmw]; abel
    rw [this]; exact hm
  · rintro ⟨s, hs⟩
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_add, Submodule.Quotient.eq] at hs
    have : x - x₀ = (x - (x₀ + s • b)) + s • b := by abel
    rw [this]
    exact Submodule.add_mem_sup hs (Submodule.mem_span_singleton.2 ⟨s, rfl⟩)

/-- **The one-direction step of Claim 3**, the paper's (4.4):
`G(K + α b) ≤ G(K) + G(K | b^⊥)`, relative to an already quotiented subspace `M`. -/
theorem classCount_translate_le (M : Submodule ℝ E) (Λ : AddSubgroup E) {K : Set E}
    (hK : Convex ℝ K) (b : E) (α : ℝ) :
    classCount M Λ ((fun x => x + α • b) '' K) ≤
      classCount M Λ K + classCount (M ⊔ Submodule.span ℝ {b}) Λ K := by
  classical
  set π := M.mkQ
  set N := M ⊔ Submodule.span ℝ {b}
  set ρ := Submodule.factor (le_sup_left : M ≤ N)
  have hρπ : ∀ x, ρ (π x) = N.mkQ x := fun x => Submodule.factor_mk _ x
  set v := π b
  set C := π '' K
  set L : AddSubgroup (E ⧸ M) := Λ.map π.toAddMonoidHom
  have hLmem : ∀ c, c ∈ (L : Set (E ⧸ M)) ↔ c ∈ π '' (Λ : Set E) := by
    intro c; simp [L]
  have hC : Convex ℝ C := hK.linear_image π
  set S1 := π '' ((fun x => x + α • b) '' K) ∩ π '' (Λ : Set E)
  set S0 := π '' K ∩ π '' (Λ : Set E)
  set T := N.mkQ '' K ∩ N.mkQ '' (Λ : Set E)
  have hS1 : π '' ((fun x => x + α • b) '' K) = α • ({v} : Set (E ⧸ M)) + C := by
    ext c
    simp only [mem_image, Set.smul_set_singleton, Set.singleton_add, C, v]
    constructor
    · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      exact ⟨π k, ⟨k, hk, rfl⟩, by rw [map_add, map_smul, add_comm]⟩
    · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      exact ⟨k + α • b, ⟨k, hk, rfl⟩, by rw [map_add, map_smul, add_comm]⟩
  change S1.encard ≤ S0.encard + T.encard
  by_cases hT : T.Finite
  swap
  · rw [Set.Infinite.encard_eq hT]; simp
  set Tf := hT.toFinset
  -- every class of `S1` lies over a class of `T`
  have hcover : S1 ⊆ ⋃ d ∈ Tf, S1 ∩ ρ ⁻¹' {d} := by
    intro c hc
    refine mem_iUnion₂.2 ⟨ρ c, (hT.mem_toFinset).2 ⟨?_, ?_⟩, hc, rfl⟩
    · obtain ⟨_, ⟨k, hk, rfl⟩, rfl⟩ := hc.1
      refine ⟨k, hk, ?_⟩
      rw [hρπ, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
      have : k - (k + α • b) = -(α • b) := by abel
      rw [this, neg_mem_iff]
      exact Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self b))
    · obtain ⟨l, hl, rfl⟩ := hc.2
      exact ⟨l, hl, (hρπ l).symm⟩
  -- the per-fibre bound
  have hfibre : ∀ d, (S1 ∩ ρ ⁻¹' {d}).encard ≤ (S0 ∩ ρ ⁻¹' {d}).encard + 1 := by
    intro d
    rcases (S1 ∩ ρ ⁻¹' {d}).eq_empty_or_nonempty with he | ⟨c₀, hc₀⟩
    · rw [he, Set.encard_empty]; exact zero_le
    have hd : d = ρ c₀ := hc₀.2.symm
    subst hd
    have hfib : ∀ c, c ∈ ρ ⁻¹' {ρ c₀} ↔ ∃ s : ℝ, c = c₀ + s • v := fun c =>
      factor_eq_iff M b c c₀
    by_cases hv : v = 0
    · -- the fibre is a single class
      have hsub : (S1 ∩ ρ ⁻¹' {ρ c₀}).Subsingleton := by
        intro c hc c' hc'
        obtain ⟨s, hs⟩ := (hfib c).1 hc.2
        obtain ⟨s', hs'⟩ := (hfib c').1 hc'.2
        rw [hs, hs', hv, smul_zero, smul_zero]
      exact (Set.encard_le_one_iff_subsingleton.2 hsub).trans le_add_self
    · have e1 : S1 ∩ ρ ⁻¹' {ρ c₀} = (fun s : ℝ => c₀ + s • v) ''
          {s | c₀ + s • v ∈ α • ({v} : Set (E ⧸ M)) + C ∧ c₀ + s • v ∈ L} := by
        ext c
        simp only [mem_inter_iff, mem_image, mem_setOf_eq, hfib, S1, hS1]
        constructor
        · rintro ⟨⟨h1, h2⟩, s, rfl⟩; exact ⟨s, ⟨h1, h2⟩, rfl⟩
        · rintro ⟨s, ⟨h1, h2⟩, rfl⟩; exact ⟨⟨h1, h2⟩, s, rfl⟩
      have e0 : S0 ∩ ρ ⁻¹' {ρ c₀} = (fun s : ℝ => c₀ + s • v) ''
          {s | c₀ + s • v ∈ C ∧ c₀ + s • v ∈ L} := by
        ext c
        simp only [mem_inter_iff, mem_image, mem_setOf_eq, hfib, S0, C]
        constructor
        · rintro ⟨⟨h1, h2⟩, s, rfl⟩; exact ⟨s, ⟨h1, h2⟩, rfl⟩
        · rintro ⟨s, ⟨h1, h2⟩, rfl⟩; exact ⟨⟨h1, h2⟩, s, rfl⟩
      rw [e1, e0]
      exact encard_line_shift_le hC L c₀ v hv α
  -- sum over the finitely many fibres
  have hdisj : (Tf : Set (E ⧸ N)).PairwiseDisjoint fun d => S0 ∩ ρ ⁻¹' {d} := by
    intro d _ d' _ hdd'
    refine Set.disjoint_left.2 fun c hc hc' => hdd' ?_
    rw [← hc.2, ← hc'.2]
  have hsum0 : ∑ d ∈ Tf, (S0 ∩ ρ ⁻¹' {d}).encard ≤ S0.encard := by
    have h := (Tf.finite_toSet).encard_biUnion hdisj
    rw [finsum_mem_coe_finset] at h
    rw [← h]
    exact Set.encard_le_encard (iUnion₂_subset fun d _ => inter_subset_left)
  calc S1.encard ≤ (⋃ d ∈ Tf, S1 ∩ ρ ⁻¹' {d}).encard := Set.encard_le_encard hcover
    _ ≤ ∑ d ∈ Tf, (S1 ∩ ρ ⁻¹' {d}).encard := Finset.set_encard_biUnion_le Tf _
    _ ≤ ∑ d ∈ Tf, ((S0 ∩ ρ ⁻¹' {d}).encard + 1) := Finset.sum_le_sum fun d _ => hfibre d
    _ = ∑ d ∈ Tf, (S0 ∩ ρ ⁻¹' {d}).encard + Tf.card := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ S0.encard + T.encard := by
        refine add_le_add hsum0 (le_of_eq ?_)
        rw [← Set.encard_coe_eq_coe_finsetCard, hT.coe_toFinset]

end Step

section ClaimThree

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem convex_image_add {K : Set E} (hK : Convex ℝ K) (t : E) :
    Convex ℝ ((fun x => x + t) '' K) := by
  have : (fun x => x + t) '' K = t +ᵥ K := by
    rw [← Set.image_vadd]; congr 1; funext x; rw [vadd_eq_add, add_comm]
  rw [this]; exact hK.vadd t

theorem span_image_insert {m : ℕ} (b : Fin m → E) (j : Fin m) (I : Finset (Fin m)) :
    Submodule.span ℝ (b '' ↑(insert j I)) =
      Submodule.span ℝ {b j} ⊔ Submodule.span ℝ (b '' ↑I) := by
  rw [Finset.coe_insert, Set.image_insert_eq, Submodule.span_insert]

/-- **Claim 3**, relative to an already quotiented subspace `M`: for a convex `K`, any
`b_1, ..., b_m`, and `t = ∑ α_i b_i` with `α` supported on `s`,
`G_M(K + t) ≤ ∑_{I ⊆ s} G_{M ⊔ L_I}(K)`. The induction on `s` is the paper's induction on
`|supp(t)|`; applying the hypothesis "to `K|b_j^⊥, Λ|b_j^⊥`" is applying it at `M ⊔ ℝ b_j`. -/
theorem claim_3_relative (Λ : AddSubgroup E) {K : Set E} (hK : Convex ℝ K) {m : ℕ}
    (b : Fin m → E) (s : Finset (Fin m)) :
    ∀ (M : Submodule ℝ E) (α : Fin m → ℝ), (∀ i, i ∉ s → α i = 0) →
      classCount M Λ ((fun x => x + ∑ i, α i • b i) '' K) ≤
        ∑ I ∈ s.powerset, classCount (M ⊔ Submodule.span ℝ (b '' ↑I)) Λ K := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro M α hα
    have h0 : ∑ i, α i • b i = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [hα i (Finset.notMem_empty i), zero_smul]
    simp only [h0, add_zero, Set.image_id', Finset.powerset_empty, Finset.sum_singleton,
      Finset.coe_empty, Set.image_empty, Submodule.span_empty, sup_bot_eq]
    exact le_rfl
  | insert j s hj ih =>
    intro M α hα
    set α' := Function.update α j 0 with hα'
    have hα's : ∀ i, i ∉ s → α' i = 0 := by
      intro i hi
      by_cases h : i = j
      · subst h; simp [hα']
      · rw [hα', Function.update_of_ne h]; exact hα i (by simp [h, hi])
    have ht : ∑ i, α i • b i = ∑ i, α' i • b i + α j • b j := by
      have : ∀ i, α i • b i = α' i • b i + (if i = j then α j • b j else 0) := by
        intro i
        by_cases h : i = j
        · subst h; simp [hα']
        · simp [hα', h]
      rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_add_distrib, Finset.sum_ite_eq']
      simp
    set K' := (fun x => x + ∑ i, α' i • b i) '' K
    have hK' : Convex ℝ K' := convex_image_add hK _
    have himg : (fun x => x + ∑ i, α i • b i) '' K = (fun x => x + α j • b j) '' K' := by
      rw [Set.image_image, ht]
      congr 1; funext x; abel
    rw [himg]
    have hstep := classCount_translate_le M Λ hK' (b j) (α j)
    have ih1 := ih M α' hα's
    have ih2 := ih (M ⊔ Submodule.span ℝ {b j}) α' hα's
    rw [Finset.sum_powerset_insert hj]
    calc classCount M Λ ((fun x => x + α j • b j) '' K')
        ≤ classCount M Λ K' + classCount (M ⊔ Submodule.span ℝ {b j}) Λ K' := hstep
      _ ≤ ∑ I ∈ s.powerset, classCount (M ⊔ Submodule.span ℝ (b '' ↑I)) Λ K +
          ∑ I ∈ s.powerset, classCount (M ⊔ Submodule.span ℝ (b '' ↑(insert j I))) Λ K := by
        refine add_le_add ih1 (ih2.trans (le_of_eq (Finset.sum_congr rfl fun I _ => ?_)))
        rw [span_image_insert, ← sup_assoc]

/-- Classes mod `⊥` are points: `G_⊥(K) = #(K ∩ Λ)`. -/
theorem classCount_bot (Λ : AddSubgroup E) (K : Set E) :
    classCount (⊥ : Submodule ℝ E) Λ K = (K ∩ (Λ : Set E)).encard := by
  have hinj : Function.Injective (⊥ : Submodule ℝ E).mkQ := by
    rw [← LinearMap.ker_eq_bot, Submodule.ker_mkQ]
  rw [classCount, ← Set.image_inter hinj, hinj.injOn.encard_image]

/-- **Claim 3**, in the paper's form: for linearly independent `b_1, ..., b_m` and
`t = ∑ α_i b_i`, `G_Λ(K + t) ≤ ∑_{I ⊆ supp(t)} G_{Λ|L_I^⊥}(K | L_I^⊥)`, the projected counts
written as counts of classes mod `L_I = span{b_i : i ∈ I}`. -/
theorem claim_3 (Λ : AddSubgroup E) {K : Set E} (hK : Convex ℝ K) {m : ℕ} (b : Fin m → E)
    (α : Fin m → ℝ) :
    (((fun x => x + ∑ i, α i • b i) '' K) ∩ (Λ : Set E)).encard ≤
      ∑ I ∈ (Finset.univ.filter fun i => α i ≠ 0).powerset,
        classCount (Submodule.span ℝ (b '' ↑I)) Λ K := by
  classical
  have h := claim_3_relative Λ hK b (Finset.univ.filter fun i => α i ≠ 0) ⊥ α
    (fun i hi => by simpa using hi)
  rw [classCount_bot] at h
  simpa only [bot_sup_eq] using h

end ClaimThree

variable {n : ℕ}

/-- **Theorem 1.3, Eq. (1.12).** For `K ∈ K^n` and linearly independent `b_1, ..., b_n`,
`vol(K) ≤ ∑_{I ⊆ [n]} G_{ℤ^n | L_I^⊥}(int K | L_I^⊥)`, with `L_I = span{b_i : i ∈ I}` and the
projected counts written as counts of classes mod `L_I`. The paper assumes `b_i ∈ ℤ^n`, which
makes the projected lattices discrete; the inequality itself does not need it (a count that is
infinite only makes the right side `⊤`). -/
theorem theorem_1_3 {K : Set (Fin n → ℝ)} (hKc : IsCompact K)
    (hKb : DiscreteMinkowski.IsPaperConvexBody K) (b : Fin n → (Fin n → ℝ))
    (hb : LinearIndependent ℝ b) :
    volume K ≤ ∑ I : Finset (Fin n),
      ((classCount (Submodule.span ℝ (b '' ↑I)) (standardIntegerLattice n).toAddSubgroup
        (interior K) : ℕ∞) : ℝ≥0∞) := by
  classical
  have hdim : finrank ℝ (Fin n → ℝ) = n := Module.finrank_fin_fun ℝ
  set Λ := (standardIntegerLattice n).toAddSubgroup
  obtain ⟨t, ht⟩ := van_der_corput isOpen_interior.measurableSet
    (hKb.1.subset interior_subset)
  -- coordinates of `t` in the basis `b`
  obtain ⟨α, hα⟩ : ∃ α : Fin n → ℝ, t = ∑ i, α i • b i := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨0, Subsingleton.elim _ _⟩
    · haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
      set B := basisOfLinearIndependentOfCardEqFinrank hb (by rw [Fintype.card_fin, hdim])
      refine ⟨B.repr t, ?_⟩
      conv_lhs => rw [← B.sum_repr t]
      simp [B]
  subst hα
  have hfin : (DiscreteMinkowski.latticePoints ((fun y => y + ∑ i, α i • b i) '' interior K)
      (standardIntegerLattice n)).Finite :=
    DiscreteMinkowski.finite_inter_lattice
      (by
        have := (hKb.1.subset interior_subset).vadd (∑ i, α i • b i)
        convert this using 1
        rw [← Set.image_vadd]; congr 1; funext y; rw [vadd_eq_add, add_comm]) _
  have hc3 := claim_3 Λ hKb.2.1.interior b α
  have hsub : (Finset.univ.filter fun i => α i ≠ 0).powerset ⊆ Finset.univ := Finset.subset_univ _
  have hc3' := hc3.trans (Finset.sum_le_sum_of_subset hsub)
  have hEq : (fun x => x + ∑ i, α i • b i) '' interior K ∩ (Λ : Set (Fin n → ℝ)) =
      DiscreteMinkowski.latticePoints ((fun y => y + ∑ i, α i • b i) '' interior K)
        (standardIntegerLattice n) := rfl
  rw [hEq] at hc3'
  rw [← volume_interior_eq hKb.2.1]
  refine ht.trans ?_
  rw [← hfin.cast_ncard_eq] at hc3'
  have := ENat.toENNReal_le.2 hc3'
  rw [ENat.toENNReal_coe] at this
  refine this.trans (le_of_eq ?_)
  exact map_sum ENat.toENNRealRingHom _ _

section Bridge

/-- **Counting through any linear map with kernel `L` is counting classes mod `L`.** -/
theorem encard_image_inter_eq_classCount {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (P : E →ₗ[ℝ] F) (L : Submodule ℝ E)
    (hP : LinearMap.ker P = L) (Λ : AddSubgroup E) (S : Set E) :
    (P '' S ∩ P '' (Λ : Set E)).encard = classCount L Λ S := by
  set φ := L.liftQ P (le_of_eq hP.symm)
  have hφinj : Function.Injective φ :=
    LinearMap.ker_eq_bot.1 (L.ker_liftQ_eq_bot P _ (le_of_eq hP))
  have himg : ∀ T : Set E, P '' T = φ '' (L.mkQ '' T) := by
    intro T; rw [Set.image_image]; rfl
  rw [himg, himg, ← Set.image_inter hφinj, hφinj.injOn.encard_image]
  rfl

/-- `ℝ^n` with its standard Euclidean structure. -/
abbrev toEucl (n : ℕ) : (Fin n → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm.toLinearEquiv

/-- The orthogonal projection of `ℝ^n` onto `L^⊥`, for the standard Euclidean structure. -/
def projMap (L : Submodule ℝ (Fin n → ℝ)) :
    (Fin n → ℝ) →ₗ[ℝ] (L.map (toEucl n).toLinearMap)ᗮ :=
  (L.map (toEucl n).toLinearMap)ᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ (toEucl n).toLinearMap

/-- The paper's projected count `G_{ℤ^n | L^⊥}(S | L^⊥)`: the number of points of the orthogonal
projection of `S` onto `L^⊥` that lie in the orthogonal projection of `ℤ^n`. -/
def projCount (L : Submodule ℝ (Fin n → ℝ)) (S : Set (Fin n → ℝ)) : ℕ∞ :=
  (projMap L '' S ∩ projMap L '' (standardIntegerLattice n : Set (Fin n → ℝ))).encard

theorem ker_projMap (L : Submodule ℝ (Fin n → ℝ)) : LinearMap.ker (projMap L) = L := by
  ext x
  simp only [LinearMap.mem_ker, projMap, LinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.coe_coe, Submodule.orthogonalProjectionOnto_eq_zero_iff,
    Submodule.orthogonal_orthogonal]
  rw [Submodule.mem_map_equiv]
  exact Iff.rfl

/-- **Notation bridge**: the paper's projected count is the class count mod `L`. -/
theorem projCount_eq_classCount (L : Submodule ℝ (Fin n → ℝ)) (S : Set (Fin n → ℝ)) :
    projCount L S = classCount L (standardIntegerLattice n).toAddSubgroup S := by
  have hco : ((standardIntegerLattice n).toAddSubgroup : Set (Fin n → ℝ)) =
      (standardIntegerLattice n : Set (Fin n → ℝ)) := rfl
  have h := encard_image_inter_eq_classCount (projMap L) L (ker_projMap L)
    (standardIntegerLattice n).toAddSubgroup S
  rw [hco] at h
  rw [projCount, h]

/-- **Theorem 1.3, Eq. (1.12), in the paper's notation**:
`vol(K) ≤ ∑_{I ⊆ [n]} G_{ℤ^n | L_I^⊥}(int K | L_I^⊥)`. -/
theorem theorem_1_3_paper {K : Set (Fin n → ℝ)} (hKc : IsCompact K)
    (hKb : DiscreteMinkowski.IsPaperConvexBody K) (b : Fin n → (Fin n → ℝ))
    (hb : LinearIndependent ℝ b) :
    volume K ≤ ∑ I : Finset (Fin n),
      ((projCount (Submodule.span ℝ (b '' ↑I)) (interior K) : ℕ∞) : ℝ≥0∞) := by
  simp_rw [projCount_eq_classCount]
  exact theorem_1_3 hKc hKb b hb

end Bridge

end

end LatticeVolumeInterpolation
