import CoordinateMinima
import CoveringRadius
import Mathlib.Algebra.Order.Round

/-!
# Real half-side lengths for coordinate boxes

Catalog item `covering_radius_bound_not_comparable`, the unnumbered
elongated-box comparison after Proposition 1.6.

The thin-box comparison needs continuous real lengths, rather than only
integer boxes or a discrete subsequence of dilations.
-/

open Set Module
open scoped Pointwise BigOperators

namespace LatticeVolumeInterpolation

def rectangularBox {n : ℕ} (w : Fin n → ℝ) : Set (Fin n → ℝ) := Icc (-w) w

theorem halfDifferenceBody_rectangularBox {n : ℕ} (w : Fin n → ℝ) :
    DiscreteMinkowski.halfDifferenceBody (rectangularBox w) = rectangularBox w := by
  apply DiscreteMinkowski.halfDifferenceBody_eq_self (convex_Icc _ _)
  change -rectangularBox w = rectangularBox w
  ext x
  rw [Set.mem_neg]
  change (-w ≤ -x ∧ -x ≤ w) ↔ (-w ≤ x ∧ x ≤ w)
  constructor <;> intro hx <;> constructor
  · intro i; simpa using neg_le_neg (hx.2 i)
  · intro i; simpa using neg_le_neg (hx.1 i)
  · intro i; simpa using neg_le_neg (hx.2 i)
  · intro i; simpa using neg_le_neg (hx.1 i)

theorem mem_smul_rectangularBox_iff {n : ℕ} {w : Fin n → ℝ} {r : ℝ}
    (hr : 0 < r) (x : Fin n → ℝ) :
    x ∈ r • rectangularBox w ↔ ∀ i, -(r * w i) ≤ x i ∧ x i ≤ r * w i := by
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hr.ne']
  change (-w ≤ r⁻¹ • x ∧ r⁻¹ • x ≤ w) ↔ _
  constructor
  · intro hx i
    have hl := mul_le_mul_of_nonneg_left (hx.1 i) hr.le
    have hu := mul_le_mul_of_nonneg_left (hx.2 i) hr.le
    simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul] at hl hu
    rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul] at hl hu
    constructor <;> linarith
  · intro hx
    constructor <;> intro i
    · have hh := mul_le_mul_of_nonneg_left (hx i).1 (inv_nonneg.mpr hr.le)
      simpa only [mul_neg, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul,
        Pi.neg_apply, Pi.smul_apply, smul_eq_mul] using hh
    · have hh := mul_le_mul_of_nonneg_left (hx i).2 (inv_nonneg.mpr hr.le)
      simpa only [← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul,
        Pi.smul_apply, smul_eq_mul] using hh

theorem rectangularBox_lattice_coordinate_zero {n : ℕ} {w : Fin n → ℝ} {r : ℝ}
    (hr : 0 < r) {x : Fin n → ℝ} (hx : x ∈ r • rectangularBox w)
    (hz : x ∈ standardIntegerLattice n) {i : Fin n} (hi : r * w i < 1) : x i = 0 := by
  have hb := (mem_smul_rectangularBox_iff hr x).mp hx i
  obtain ⟨p, hp⟩ := (mem_standardIntegerLattice_iff n x).mp hz
  have hpl : (-1 : ℤ) < p i := by exact_mod_cast (show (-1 : ℝ) < (p i : ℝ) by rw [← hp i]; linarith)
  have hpu : p i < (1 : ℤ) := by exact_mod_cast (show (p i : ℝ) < 1 by rw [← hp i]; linarith)
  have hp0 : p i = 0 := by omega
  simpa only [hp0, Int.cast_zero] using hp i

theorem successiveMinimum_rectangularBox {n : ℕ} (w : Fin n → ℝ)
    (hw : ∀ j, 0 < w j) (hmono : Antitone w) (i : Fin n) :
    DiscreteMinkowski.successiveMinimum (rectangularBox w) (standardIntegerLattice n)
      (i.1 + 1) = (w i)⁻¹ := by
  let e : Fin (i.1 + 1) ↪ Fin n := ⟨Fin.castLE i.2, Fin.castLE_injective i.2⟩
  have hupper : (w i)⁻¹ ∈ DiscreteMinkowski.minimaSet (rectangularBox w) (standardIntegerLattice n) (i.1 + 1) := by
    refine ⟨inv_pos.mpr (hw i), ?_⟩
    rw [DiscreteMinkowski.scaledLatticeSpan, halfDifferenceBody_rectangularBox]
    apply finrank_span_ge_of_coordinateUnitVectors e
    intro j
    refine ⟨(mem_smul_rectangularBox_iff (inv_pos.mpr (hw i)) _).mpr ?_,
      coordinateUnitVector_mem_standardIntegerLattice n (e j)⟩
    intro k
    have hnon : 0 ≤ (w i)⁻¹ * w k := mul_nonneg (inv_nonneg.mpr (hw i).le) (hw k).le
    by_cases hk : k = e j
    · subst k
      have hji : e j ≤ i := Fin.le_iff_val_le_val.mpr (Nat.le_of_lt_succ j.2)
      have ht : 1 ≤ (w i)⁻¹ * w (e j) := by
        calc
          1 = (w i)⁻¹ * w i := (inv_mul_cancel₀ (hw i).ne').symm
          _ ≤ _ := mul_le_mul_of_nonneg_left (hmono hji) (inv_nonneg.mpr (hw i).le)
      simpa only [coordinateUnitVector, Pi.single_eq_same] using
        (show -((w i)⁻¹ * w (e j)) ≤ 1 ∧ 1 ≤ (w i)⁻¹ * w (e j) from ⟨by linarith, ht⟩)
    · simp only [coordinateUnitVector, Pi.single_eq_of_ne hk]
      exact ⟨by linarith, hnon⟩
  apply le_antisymm (csInf_le (DiscreteMinkowski.bddBelow_minimaSet _ _ _) hupper)
  apply le_csInf ⟨_, hupper⟩
  intro r hr
  by_contra hh
  have hsmall : r * w i < 1 := by
    have hh' : r < (w i)⁻¹ := lt_of_not_ge hh
    calc
      r * w i < (w i)⁻¹ * w i := mul_lt_mul_of_pos_right hh' (hw i)
      _ = 1 := inv_mul_cancel₀ (hw i).ne'
  have hsub : DiscreteMinkowski.scaledLatticeSpan (rectangularBox w) (standardIntegerLattice n) r ≤
      Pi.spanSubset ℝ {j : Fin n | j < i} := by
    rw [DiscreteMinkowski.scaledLatticeSpan, halfDifferenceBody_rectangularBox]
    apply Submodule.span_le.mpr
    rintro x ⟨hx, hz⟩
    apply Pi.mem_spanSubset_iff.mpr
    intro j hj
    exact rectangularBox_lattice_coordinate_zero hr.1 hx hz
      ((mul_le_mul_of_nonneg_left (hmono (le_of_not_gt hj)) hr.1.le).trans_lt hsmall)
  have hdim : finrank ℝ (Pi.spanSubset ℝ {j : Fin n | j < i}) = i.1 := by
    rw [Pi.dim_spanSubset]
    have he : {j : Fin n | j < i} = (↑(Finset.Iio i) : Set (Fin n)) := by ext j; simp
    rw [he, Set.ncard_coe_finset, Fin.card_Iio]
  have hle := Submodule.finrank_mono hsub
  rw [hdim] at hle
  have hge := hr.2
  omega

theorem coveringRadius_rectangularBox_eq_one {n : ℕ} (w : Fin n → ℝ)
    (hw : ∀ i, (1 / 2 : ℝ) ≤ w i) (j : Fin n) (hj : w j = 1 / 2) :
    coveringRadius (rectangularBox w) = 1 := by
  have hmem : (1 : ℝ) ∈ coveringSet (rectangularBox w) := by
    refine ⟨by norm_num, fun y => ?_⟩
    let z : Fin n → ℝ := fun i => (⌊y i + 1 / 2⌋ : ℝ)
    refine ⟨z, (mem_standardIntegerLattice_iff n z).mpr ⟨fun i => ⌊y i + 1 / 2⌋, fun _ => rfl⟩, ?_⟩
    apply (mem_smul_rectangularBox_iff (by norm_num) _).mpr
    intro i
    have hl := Int.floor_le (y i + 1 / 2)
    have hu := Int.lt_floor_add_one (y i + 1 / 2)
    change -(1 * w i) ≤ y i - (⌊y i + 1 / 2⌋ : ℝ) ∧
      y i - (⌊y i + 1 / 2⌋ : ℝ) ≤ 1 * w i
    constructor <;> linarith [hw i]
  have hlow : ∀ r ∈ coveringSet (rectangularBox w), 1 ≤ r := by
    rintro r ⟨hr0, hr⟩
    by_contra hh
    have hr1 : r < 1 := lt_of_not_ge hh
    obtain ⟨z, hz, hres⟩ := hr (fun _ => (1 / 2 : ℝ))
    have hb := (mem_smul_rectangularBox_iff hr0 _).mp hres j
    obtain ⟨p, hp⟩ := (mem_standardIntegerLattice_iff n z).mp hz
    simp only [Pi.sub_apply, hp, hj] at hb
    by_cases hp0 : p j ≤ 0
    · have hpR : (p j : ℝ) ≤ 0 := by exact_mod_cast hp0
      linarith [hb.2]
    · have hpR : (1 : ℝ) ≤ p j := by exact_mod_cast (show 1 ≤ p j by omega)
      linarith [hb.1]
  exact le_antisymm (csInf_le ⟨0, fun _ hh => hh.1.le⟩ hmem) (le_csInf ⟨1, hmem⟩ hlow)

end LatticeVolumeInterpolation
