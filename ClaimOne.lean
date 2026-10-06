import ShakingIterate

/-!
# Claim 1: the successive minima do not increase under the successive shakings

Catalog item `claim_1_block_triangular_basis`, and conclusion iv) of Theorem 3.1.

Suppose `u_0, ..., u_{n-1}` are lattice vectors whose matrix is upper triangular with non-zero
diagonal (`(u_i)_l = 0` for `l > i`, `(u_i)_i ≠ 0`) and `|u_i|_{cs(K)} ≤ λ_{i+1}(K)`. The paper's
Claim 1 keeps, after the first `k` shakings, a basis of the block form
`diag(D_k, T_{n-k})`; here that basis is written out: `w_k(i)` is `u_i` with every coordinate
`l < k`, `l ≠ i`, set to zero. For `i < k` this is `(u_i)_i e_i` (the diagonal block), and for
`i ≥ k` it is `u_i` with its first `k` coordinates removed (the triangular block). Shaking along
`e_k` sends `w_k(i)` to `w_{k+1}(i)`: for `i ≠ k` by projecting onto `e_k^⊥` (Lemma 3.2 iv)),
and for `i = k`, where `w_k(k) = (u_k)_k e_k`, by Lemma 3.2 iii). Neither step increases the
gauge, so `|w_k(i)|_{cs(K_k)} ≤ λ_{i+1}(K)` for all `k` (`claim_1`). At `k = n` the vectors are
non-zero multiples of the distinct axes, which gives `λ_i(K_n) ≤ λ_i(K)`.
-/

open Set Module MeasureTheory
open scoped Pointwise

namespace LatticeVolumeInterpolation

noncomputable section

variable {n : ℕ}

/-- `u` with every coordinate `l < k`, `l ≠ i`, set to zero. -/
def claimVector (u : Fin n → Fin n → ℝ) (k : ℕ) (i : Fin n) : Fin n → ℝ :=
  fun l => if l.1 < k ∧ l ≠ i then 0 else u i l

theorem claimVector_succ_of_ne (u : Fin n → Fin n → ℝ) {k : ℕ} (h : k < n) {i : Fin n}
    (hi : i ≠ ⟨k, h⟩) :
    claimVector u (k + 1) i = Function.update (claimVector u k i) ⟨k, h⟩ 0 := by
  funext l
  by_cases hl : l = ⟨k, h⟩
  · subst hl; simp [claimVector, Ne.symm hi]
  · have hlk : l.1 ≠ k := fun e => hl (Fin.ext e)
    simp only [claimVector, Function.update_of_ne hl]
    congr 1
    apply propext
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩

theorem claimVector_succ_self (u : Fin n → Fin n → ℝ) {k : ℕ} (h : k < n) :
    claimVector u (k + 1) ⟨k, h⟩ = claimVector u k ⟨k, h⟩ := by
  funext l
  simp only [claimVector]
  congr 1
  apply propext
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by have : l.1 ≠ k := fun e => h2 (Fin.ext e); omega, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩

/-- For a triangular family, `w_k(k) = (u_k)_k e_k`. -/
theorem claimVector_self_eq_smul (u : Fin n → Fin n → ℝ)
    (htri : ∀ i l : Fin n, i < l → u i l = 0) {k : ℕ} (h : k < n) :
    claimVector u k ⟨k, h⟩ = u ⟨k, h⟩ ⟨k, h⟩ • (Pi.single ⟨k, h⟩ (1 : ℝ) : Fin n → ℝ) := by
  funext l
  by_cases hl : l = ⟨k, h⟩
  · subst hl; simp [claimVector]
  · rw [Pi.smul_apply, Pi.single_eq_of_ne hl, smul_zero]
    simp only [claimVector]
    split_ifs with hc
    · rfl
    · have hlk : l.1 ≠ k := fun e => hl (Fin.ext e)
      have hgt : k < l.1 := by
        by_contra hle
        exact hc ⟨by omega, hl⟩
      exact htri ⟨k, h⟩ l hgt

/-- **Claim 1.** Along the successive shakings the gauge of `w_k(i)` stays at most `λ_{i+1}(K)`. -/
theorem claim_1 {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (hKb : DiscreteMinkowski.IsPaperConvexBody K) (u : Fin n → Fin n → ℝ)
    (htri : ∀ i l : Fin n, i < l → u i l = 0) {μ : Fin n → ℝ}
    (hgauge : ∀ i, gauge (DiscreteMinkowski.halfDifferenceBody K) (u i) ≤ μ i) :
    ∀ k, ∀ i, gauge (DiscreteMinkowski.halfDifferenceBody (shakeUpTo K k)) (claimVector u k i) ≤
      μ i
  | 0 => fun i => by
    have : claimVector u 0 i = u i := by funext l; simp [claimVector]
    rw [this]; exact hgauge i
  | k + 1 => fun i => by
    by_cases h : k < n
    · have hKk := isCompact_shakeUpTo hK k
      have hKbk := isPaperConvexBody_shakeUpTo hK hKb k
      rw [shakeUpTo_succ_of_lt K h]
      by_cases hi : i = ⟨k, h⟩
      · subst hi
        rw [claimVector_succ_self, claimVector_self_eq_smul u htri h]
        have h1 := gauge_coordShaking_smul_single_le hKk hKbk ⟨k, h⟩ (u ⟨k, h⟩ ⟨k, h⟩)
        have h2 := claim_1 hK hKb u htri hgauge k ⟨k, h⟩
        rw [claimVector_self_eq_smul u htri h] at h2
        exact h1.trans h2
      · rw [claimVector_succ_of_ne u h hi]
        exact (gauge_coordShaking_update_le hKk hKbk ⟨k, h⟩ _).trans
          (claim_1 hK hKb u htri hgauge k i)
    · have hkn : n ≤ k := not_lt.1 h
      rw [shakeUpTo_succ_of_le K hkn]
      have : claimVector u (k + 1) i = claimVector u k i := by
        funext l
        simp only [claimVector]
        congr 1
        apply propext
        constructor
        · rintro ⟨-, h2⟩; exact ⟨by have := l.2; omega, h2⟩
        · rintro ⟨-, h2⟩; exact ⟨by omega, h2⟩
      rw [this]
      exact claim_1 hK hKb u htri hgauge k i

/-- After all `n` shakings, `w_n(i) = (u_i)_i e_i`. -/
theorem claimVector_n_eq_smul (u : Fin n → Fin n → ℝ) (i : Fin n) :
    claimVector u n i = u i i • (Pi.single i (1 : ℝ) : Fin n → ℝ) := by
  funext l
  by_cases hl : l = i
  · subst hl; simp [claimVector]
  · rw [Pi.smul_apply, Pi.single_eq_of_ne hl, smul_zero]
    simp [claimVector, l.2, hl]

/-- **Theorem 3.1 iv) in the triangular case:** `λ_{i+1}(K_n) ≤ λ_{i+1}(K)`. -/
theorem successiveMinimum_shakeUpTo_le {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (hKb : DiscreteMinkowski.IsPaperConvexBody K) (u : Fin n → Fin n → ℝ)
    (hΛ : ∀ i, u i ∈ standardIntegerLattice n)
    (htri : ∀ i l : Fin n, i < l → u i l = 0) (hdiag : ∀ i, u i i ≠ 0)
    (hgauge : ∀ i, gauge (DiscreteMinkowski.halfDifferenceBody K) (u i) ≤
      DiscreteMinkowski.successiveMinimum K (standardIntegerLattice n) (i.1 + 1))
    (i : Fin n) :
    DiscreteMinkowski.successiveMinimum (shakeUpTo K n) (standardIntegerLattice n) (i.1 + 1) ≤
      DiscreteMinkowski.successiveMinimum K (standardIntegerLattice n) (i.1 + 1) := by
  classical
  set lam := fun k : Fin n =>
    DiscreteMinkowski.successiveMinimum K (standardIntegerLattice n) (k.1 + 1)
  have hdim : finrank ℝ (Fin n → ℝ) = n := Module.finrank_fin_fun ℝ
  have hAb := isPaperConvexBody_shakeUpTo hK hKb n
  have hcl := claim_1 hK hKb u htri hgauge n
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hlampos : 0 < lam i :=
    DiscreteMinkowski.successiveMinimum_pos hKb (by omega) (by rw [hdim]; exact i.2)
  refine DiscreteMinkowski.successiveMinimum_le_of_finrank_gauge_lt hAb (by linarith) ?_
  set b : {k // k ∈ Finset.Iic i} → (Fin n → ℝ) := fun k => claimVector u n k.1 with hb
  have hbind : LinearIndependent ℝ b := by
    have hsingle : LinearIndependent ℝ
        (fun k : {k // k ∈ Finset.Iic i} => (Pi.single k.1 (1 : ℝ) : Fin n → ℝ)) := by
      have hinj : Function.Injective (fun k : {k // k ∈ Finset.Iic i} => k.1) :=
        fun k l hkl => Subtype.ext hkl
      simpa [Function.comp_def] using (Pi.basisFun ℝ (Fin n)).linearIndependent.comp _ hinj
    have := hsingle.units_smul (fun k => Units.mk0 (u k.1 k.1) (hdiag k.1))
    convert this using 1
    funext k
    simp [hb, claimVector_n_eq_smul u, Units.smul_def]
  have hspan : Submodule.span ℝ (Set.range b) ≤ Submodule.span ℝ
      {x : Fin n → ℝ | x ∈ (standardIntegerLattice n : Set (Fin n → ℝ)) ∧
        gauge (DiscreteMinkowski.halfDifferenceBody (shakeUpTo K n)) x < lam i + ε} := by
    refine Submodule.span_mono ?_
    rintro _ ⟨k, rfl⟩
    refine ⟨?_, ?_⟩
    · obtain ⟨z, hz⟩ := (mem_standardIntegerLattice_iff n (u k.1)).1 (hΛ k.1)
      refine (mem_standardIntegerLattice_iff n _).2
        ⟨fun l => if l = k.1 then z l else 0, fun l => ?_⟩
      simp only [hb, claimVector_n_eq_smul u, Pi.smul_apply, smul_eq_mul]
      by_cases hl : l = k.1
      · subst hl; simp [hz]
      · simp [hl]
    · have hk : k.1 ≤ i := Finset.mem_Iic.1 k.2
      have hmono : lam k.1 ≤ lam i :=
        DiscreteMinkowski.successiveMinimum_mono_of_le_finrank hKb (by
          have : k.1.1 ≤ i.1 := hk; omega) (by rw [hdim]; exact i.2)
      have := hcl k.1
      change gauge _ (claimVector u n k.1) < lam i + ε
      linarith
  have hcard := finrank_span_eq_card hbind
  rw [Fintype.card_coe, Fin.card_Iic] at hcard
  calc i.1 + 1 = finrank ℝ (Submodule.span ℝ (Set.range b)) := hcard.symm
    _ ≤ _ := Submodule.finrank_mono hspan

end

end LatticeVolumeInterpolation
