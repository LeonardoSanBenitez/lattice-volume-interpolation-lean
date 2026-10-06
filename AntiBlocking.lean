import JoinVolume
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Anti-blocking bodies and the Rogers-Shephard inequality in their case

Catalog items `anti_blocking_body` (Sec. 3) and `rogers_shephard_section_projection`
(Eq. (4.1)).

A set `K ⊆ ℝ^n_{≥0}` is **anti-blocking** when it is closed under coordinatewise decrease
inside the orthant: `x ∈ K`, `0 ≤ y ≤ x` coordinatewise imply `y ∈ K`.

For `I ⊆ [n]` let `L_I = span{e_i : i ∈ I}`. Coordinates split `ℝ^n` as
`ℝ^I × ℝ^{[n] \ I}`, which is `L_I × L_I^⊥` with Lebesgue measure on each factor; under this
identification

* `K ∩ L_I` is `sectionOn I K = {u : ℝ^I | (u, 0) ∈ K}`, and
* the orthogonal projection `K | L_I^⊥` is `projectionOff I K`, the image of `K` under
  forgetting the coordinates in `I`.

Eq. (4.1) is `vol_k(K ∩ L_I) vol_{n-k}(K | L_I^⊥) ≤ binom(n, k) vol(K)` for `|I| = k`. The paper
applies it only to an anti-blocking body, which is proved here
(`rogers_shephard_antiBlocking`). For such a body the projection equals the section
`K ∩ L_I^⊥`, both sections lie in `K`, and `K` contains the join of the two, whose volume is
at least `vol_k vol_{n-k} / binom(n, k)` by `join_volume_lower_bound'`. This replaces the
appeal to Rogers and Shephard's general theorem, which is not used.
-/

open MeasureTheory Set Module
open scoped ENNReal

namespace LatticeVolumeInterpolation

noncomputable section

variable {n : ℕ}

/-- **Anti-blocking** (Sec. 3): contained in the non-negative orthant, and closed under
coordinatewise decrease inside it. -/
def IsAntiBlocking (K : Set (Fin n → ℝ)) : Prop :=
  (∀ x ∈ K, ∀ i, 0 ≤ x i) ∧
    ∀ x ∈ K, ∀ y : Fin n → ℝ, (∀ i, 0 ≤ y i) → (∀ i, y i ≤ x i) → y ∈ K

/-- The coordinate splitting `ℝ^n ≃ ℝ^I × ℝ^{[n] \ I}`, measure preserving. -/
abbrev coordSplit (I : Finset (Fin n)) :=
  MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ) (· ∈ I)

/-- `K ∩ L_I`, in the coordinates of `L_I`. -/
def sectionOn (I : Finset (Fin n)) (K : Set (Fin n → ℝ)) : Set ({i // i ∈ I} → ℝ) :=
  {u | (coordSplit I).symm (u, 0) ∈ K}

/-- `K ∩ L_I^⊥`, in the coordinates of `L_I^⊥`. -/
def sectionOff (I : Finset (Fin n)) (K : Set (Fin n → ℝ)) : Set ({i // i ∉ I} → ℝ) :=
  {v | (coordSplit I).symm (0, v) ∈ K}

/-- `K | L_I^⊥`, the orthogonal projection onto `L_I^⊥`, in its coordinates. -/
def projectionOff (I : Finset (Fin n)) (K : Set (Fin n → ℝ)) : Set ({i // i ∉ I} → ℝ) :=
  (fun x => (coordSplit I x).2) '' K

theorem coordSplit_symm_apply (I : Finset (Fin n)) (u : {i // i ∈ I} → ℝ)
    (v : {i // i ∉ I} → ℝ) (i : Fin n) :
    (coordSplit I).symm (u, v) i = if h : i ∈ I then u ⟨i, h⟩ else v ⟨i, h⟩ := rfl

/-- For an anti-blocking body the projection onto `L_I^⊥` is the section by `L_I^⊥`. -/
theorem projectionOff_eq_sectionOff {K : Set (Fin n → ℝ)} (hK : IsAntiBlocking K)
    (I : Finset (Fin n)) : projectionOff I K = sectionOff I K := by
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine hK.2 x hx _ (fun i => ?_) (fun i => ?_)
    · rw [coordSplit_symm_apply]
      split_ifs
      · exact le_rfl
      · exact hK.1 x hx i
    · rw [coordSplit_symm_apply]
      split_ifs
      · exact hK.1 x hx i
      · exact le_rfl
  · intro hv
    refine ⟨_, hv, ?_⟩
    funext i
    simp [coordSplit, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, i.2]

theorem coordSplit_symm_apply' (I : Finset (Fin n))
    (p : ({i // i ∈ I} → ℝ) × ({i // i ∉ I} → ℝ)) (i : Fin n) :
    (coordSplit I).symm p i = if h : i ∈ I then p.1 ⟨i, h⟩ else p.2 ⟨i, h⟩ := rfl

theorem coordSplit_symm_add_smul (I : Finset (Fin n)) (a b : ℝ)
    (p q : ({i // i ∈ I} → ℝ) × ({i // i ∉ I} → ℝ)) :
    (coordSplit I).symm (a • p + b • q) =
      a • (coordSplit I).symm p + b • (coordSplit I).symm q := by
  funext i
  simp only [coordSplit_symm_apply', Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

/-- **Eq. (4.1) for an anti-blocking body.** For a compact convex anti-blocking `K` and
`I ⊆ [n]` with `|I| = k`,
`vol_k(K ∩ L_I) · vol_{n-k}(K | L_I^⊥) ≤ binom(n, k) · vol(K)`. -/
theorem rogers_shephard_antiBlocking {K : Set (Fin n → ℝ)} (hKc : IsCompact K)
    (hKconv : Convex ℝ K) (hK : IsAntiBlocking K) (I : Finset (Fin n)) :
    volume (sectionOn I K) * volume (projectionOff I K) ≤
      (n.choose I.card : ℝ≥0∞) * volume K := by
  classical
  set e := coordSplit I with he
  set C : Set (({i // i ∈ I} → ℝ) × ({i // i ∉ I} → ℝ)) := e.symm ⁻¹' K with hC
  have hpres : MeasurePreserving e volume (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    convert volume_preserving_piEquivPiSubtypeProd (fun _ : Fin n => ℝ) (· ∈ I) using 1
    · rfl
    · congr!
  have hCm : MeasurableSet C := hKc.isClosed.measurableSet.preimage e.symm.measurable
  have hvolK : volume K = (volume.prod volume) C := by
    rw [← hpres.measure_preimage hCm.nullMeasurableSet]
    congr 1
    ext x
    simp [hC]
  have hCconv : Convex ℝ C := by
    intro p hp q hq a b ha hb hab
    change e.symm (a • p + b • q) ∈ K
    rw [coordSplit_symm_add_smul]
    exact hKconv hp hq ha hb hab
  have hBcpt : IsCompact (sectionOff I K) := by
    rw [← projectionOff_eq_sectionOff hK I]
    refine hKc.image ?_
    exact continuous_pi fun i => continuous_apply i.1
  have hk : finrank ℝ ({i // i ∈ I} → ℝ) = I.card := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  have hm : finrank ℝ ({i // i ∉ I} → ℝ) = n - I.card := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_subtype_compl, Fintype.card_coe,
      Fintype.card_fin]
  have hjoin := join_volume_lower_bound' (volume : Measure ({i // i ∈ I} → ℝ))
    (volume : Measure ({i // i ∉ I} → ℝ)) hk hm hBcpt hCconv hCm
    (A := sectionOn I K) (fun a ha => ha) (fun b hb => hb)
  rw [← hvolK] at hjoin
  rw [projectionOff_eq_sectionOff hK I]
  have hkn : I.card ≤ n := by
    simpa using I.card_le_univ
  have hsum : I.card + (n - I.card) = n := Nat.add_sub_cancel' hkn
  rw [hsum] at hjoin
  -- `k! (n-k)! / n! = 1 / binom(n, k)`
  have hchoose : (n.choose I.card : ℝ) * (I.card.factorial * (n - I.card).factorial) =
      n.factorial := by
    exact_mod_cast (by rw [← mul_assoc]; exact Nat.choose_mul_factorial_mul_factorial hkn)
  have hcpos : (0 : ℝ) < n.choose I.card := by exact_mod_cast Nat.choose_pos hkn
  have hconst : ENNReal.ofReal
      ((I.card.factorial * (n - I.card).factorial : ℝ) / (n.factorial : ℝ)) =
        ((n.choose I.card : ℝ≥0∞))⁻¹ := by
    have hx : (I.card.factorial * (n - I.card).factorial : ℝ) / (n.factorial : ℝ) =
        ((n.choose I.card : ℕ) : ℝ)⁻¹ := by
      rw [← hchoose]
      have hf : (I.card.factorial * (n - I.card).factorial : ℝ) ≠ 0 := by positivity
      field_simp
    rw [hx, ENNReal.ofReal_inv_of_pos hcpos, ENNReal.ofReal_natCast]
  rw [hconst] at hjoin
  have hc0 : (n.choose I.card : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.choose_pos hkn).ne'
  have hctop : (n.choose I.card : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  calc volume (sectionOn I K) * volume (sectionOff I K)
      = (n.choose I.card : ℝ≥0∞) *
          (volume (sectionOn I K) * volume (sectionOff I K) * (n.choose I.card : ℝ≥0∞)⁻¹) := by
        rw [mul_comm (n.choose I.card : ℝ≥0∞), mul_assoc _ ((n.choose I.card : ℝ≥0∞))⁻¹,
          ENNReal.inv_mul_cancel hc0 hctop, mul_one]
    _ ≤ (n.choose I.card : ℝ≥0∞) * volume K := mul_le_mul_right hjoin _

end

end LatticeVolumeInterpolation
