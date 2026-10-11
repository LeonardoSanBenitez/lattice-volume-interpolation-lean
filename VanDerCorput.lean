import StandardLattice
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Algebra.Module.ZLattice.Basic

/-!
# van der Corput's theorem

Catalog item `van_der_corput_theorem` (Theorem 2.1, Eq. (2.1)): for a Jordan-measurable
`M ⊆ ℝ^n` there is `t ∈ ℝ^n` with `vol(M) ≤ G(M + t)`. The paper quotes it from Gruber and
Lekkerkerker; it is proved here by the standard averaging argument. With `F = [0, 1)^n`, a
fundamental domain of `ℤ^n` of volume `1`,

  `vol(M) = ∑_{z ∈ ℤ^n} vol(M ∩ (z + F)) = ∫_F #{z ∈ ℤ^n : z + x ∈ M} dx`

(`lintegral_translateCount`), so the count is at least `vol(M)` at some `x ∈ F`, and `t = -x`
works. The same identity gives the upper bound of Proposition 1.6.

The hypothesis is weaker than the paper's: `M` bounded and Lebesgue measurable, which every
Jordan-measurable set is.
-/

open MeasureTheory Set Module
open scoped ENNReal Pointwise

namespace LatticeVolumeInterpolation

noncomputable section

variable {n : ℕ}

/-- The half-open unit cube `[0, 1)^n`, a fundamental domain of `ℤ^n`. -/
abbrev unitCubeIco (n : ℕ) : Set (Fin n → ℝ) := ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin n))

theorem volume_unitCubeIco (n : ℕ) : volume (unitCubeIco n) = 1 := by
  rw [unitCubeIco, ZSpan.fundamentalDomain_pi_basisFun, Real.volume_pi_Ico]
  simp

theorem measurableSet_unitCubeIco (n : ℕ) : MeasurableSet (unitCubeIco n) :=
  ZSpan.fundamentalDomain_measurableSet _

/-- The lattice vectors `z` with `z + x ∈ M`. -/
def translateSet (M : Set (Fin n → ℝ)) (x : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {z | z ∈ standardIntegerLattice n ∧ z + x ∈ M}

/-- **The count of lattice translates integrates to the volume.**
`∫_{[0,1)^n} #{z ∈ ℤ^n : z + x ∈ M} dx = vol(M)`. -/
theorem lintegral_translateCount {M : Set (Fin n → ℝ)} (hM : MeasurableSet M) :
    ∫⁻ x in unitCubeIco n, ((translateSet M x).encard : ℝ≥0∞) = volume M := by
  classical
  set b := Pi.basisFun ℝ (Fin n)
  set L := Submodule.span ℤ (Set.range b)
  have hF : IsAddFundamentalDomain L (unitCubeIco n) volume :=
    ZSpan.isAddFundamentalDomain b volume
  have hLΛ : ∀ x : Fin n → ℝ, x ∈ L ↔ x ∈ standardIntegerLattice n := by
    intro x; rw [standardIntegerLattice_eq_span]
  haveI : VAddInvariantMeasure L (Fin n → ℝ) volume :=
    (inferInstance : VAddInvariantMeasure L.toAddSubgroup (Fin n → ℝ) volume)
  have hvadd : ∀ (g : L) (x : Fin n → ℝ), g +ᵥ x = (g : Fin n → ℝ) + x := fun _ _ => rfl
  set one : (Fin n → ℝ) → ℝ≥0∞ := fun _ => 1 with hone
  have hmeas : ∀ g : L, Measurable fun x : Fin n → ℝ => M.indicator one (g +ᵥ x) :=
    fun g => (measurable_const.indicator hM).comp (measurable_const_vadd g)
  -- the count as a sum over the lattice
  have hcount : ∀ x, ((translateSet M x).encard : ℝ≥0∞) =
      ∑' g : L, M.indicator one (g +ᵥ x) := by
    intro x
    have himg : (fun g : L => (g : Fin n → ℝ)) ''
        ((fun g : L => (g : Fin n → ℝ)) ⁻¹' translateSet M x) = translateSet M x := by
      refine Set.image_preimage_eq_of_subset fun y hy => ?_
      exact ⟨⟨y, (hLΛ y).2 hy.1⟩, rfl⟩
    have hE : ((fun g : L => (g : Fin n → ℝ)) ⁻¹' translateSet M x).encard =
        (translateSet M x).encard := by
      conv_rhs => rw [← himg]
      rw [Subtype.val_injective.injOn.encard_image]
    rw [← hE, ← ENNReal.tsum_set_one,
      tsum_subtype ((fun g : L => (g : Fin n → ℝ)) ⁻¹' translateSet M x) (fun _ => (1 : ℝ≥0∞))]
    refine tsum_congr fun g => ?_
    simp only [Set.indicator_apply, mem_preimage, translateSet, mem_setOf_eq, hvadd, hone]
    simp [(hLΛ g).1 g.2]
  simp_rw [hcount]
  rw [← lintegral_indicator_one hM, hF.lintegral_eq_tsum'',
    lintegral_tsum fun g => (hmeas g).aemeasurable]
  rfl

/-- The translate set is the set of lattice points of `M - x`. -/
theorem translateSet_eq_latticePoints (M : Set (Fin n → ℝ)) (x : Fin n → ℝ) :
    translateSet M x =
      DiscreteMinkowski.latticePoints ((fun y => y + -x) '' M) (standardIntegerLattice n) := by
  ext z
  simp only [translateSet, mem_setOf_eq, DiscreteMinkowski.latticePoints_apply, mem_inter_iff,
    mem_image, SetLike.mem_coe]
  constructor
  · rintro ⟨hz, hzM⟩
    exact ⟨⟨z + x, hzM, by abel⟩, hz⟩
  · rintro ⟨⟨y, hy, rfl⟩, hz⟩
    exact ⟨hz, by convert hy using 1; abel⟩

theorem translateSet_finite {M : Set (Fin n → ℝ)} (hMb : Bornology.IsBounded M)
    (x : Fin n → ℝ) : (translateSet M x).Finite := by
  rw [translateSet_eq_latticePoints]
  refine DiscreteMinkowski.finite_inter_lattice ?_ _
  have : (fun y => y + -x) '' M = -x +ᵥ M := by
    rw [← Set.image_vadd]
    congr 1
    funext y
    rw [vadd_eq_add, add_comm]
  rw [this]
  exact hMb.vadd (-x)

/-- **van der Corput's theorem**, Eq. (2.1). -/
theorem van_der_corput {M : Set (Fin n → ℝ)} (hM : MeasurableSet M)
    (hMb : Bornology.IsBounded M) :
    ∃ t : Fin n → ℝ, volume M ≤
      ((DiscreteMinkowski.latticePoints ((fun y => y + t) '' M)
        (standardIntegerLattice n)).ncard : ℝ≥0∞) := by
  have hint := lintegral_translateCount hM
  have hMtop : volume M ≠ ⊤ := hMb.measure_lt_top.ne
  obtain ⟨x, -, hx⟩ := exists_setLAverage_le (μ := volume) (s := unitCubeIco n)
    (f := fun x => ((translateSet M x).encard : ℝ≥0∞))
    (by rw [volume_unitCubeIco]; exact one_ne_zero)
    (measurableSet_unitCubeIco n).nullMeasurableSet (by rw [hint]; exact hMtop)
  rw [setLAverage_eq, hint, volume_unitCubeIco, div_one] at hx
  refine ⟨-x, hx.trans (le_of_eq ?_)⟩
  rw [← (translateSet_finite hMb x).cast_ncard_eq, ENat.toENNReal_coe,
    translateSet_eq_latticePoints]

end

end LatticeVolumeInterpolation
