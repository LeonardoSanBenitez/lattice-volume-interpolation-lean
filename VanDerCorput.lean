import Davenport
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Algebra.Module.ZLattice.Basic

/-!
# van der Corput's theorem

Catalog item `van_der_corput_theorem` (Theorem 2.1, Eq. (2.1)): for a Jordan-measurable
`M ⊆ ℝ^n` there is `t ∈ ℝ^n` with `vol(M) ≤ G(M + t)`. The paper quotes it from Gruber and
Lekkerkerker; it is proved here by the standard averaging argument. With `F = [0, 1)^n`, a
fundamental domain of `ℤ^n` of volume `1`,

  `vol(M) = ∑_{z ∈ ℤ^n} vol(M ∩ (z + F)) = ∫_F #{z ∈ ℤ^n : z + x ∈ M} dx`,

so the count is at least `vol(M)` at some `x ∈ F`, and `t = -x` works.

The hypothesis is weaker than the paper's: `M` bounded and Lebesgue measurable, which every
Jordan-measurable set is.
-/

open MeasureTheory Set Module
open scoped ENNReal Pointwise

namespace LatticeVolumeInterpolation

noncomputable section

variable {n : ℕ}

/-- **van der Corput's theorem**, Eq. (2.1). -/
theorem van_der_corput {M : Set (Fin n → ℝ)} (hM : MeasurableSet M)
    (hMb : Bornology.IsBounded M) :
    ∃ t : Fin n → ℝ, volume M ≤
      ((DiscreteMinkowski.latticePoints ((fun y => y + t) '' M)
        (standardIntegerLattice n)).ncard : ℝ≥0∞) := by
  classical
  set b := Pi.basisFun ℝ (Fin n)
  set L := Submodule.span ℤ (Set.range b)
  set F := ZSpan.fundamentalDomain b
  have hF : IsAddFundamentalDomain L F volume := ZSpan.isAddFundamentalDomain b volume
  have hFvol : volume F = 1 := by
    rw [show F = Set.pi univ fun _ : Fin n => Ico (0 : ℝ) 1 from
      ZSpan.fundamentalDomain_pi_basisFun, Real.volume_pi_Ico]
    simp
  have hFm : MeasurableSet F := ZSpan.fundamentalDomain_measurableSet b
  have hLΛ : ∀ x : Fin n → ℝ, x ∈ L ↔ x ∈ standardIntegerLattice n := by
    intro x; rw [standardIntegerLattice_eq_span]
  haveI : VAddInvariantMeasure L (Fin n → ℝ) volume :=
    (inferInstance : VAddInvariantMeasure L.toAddSubgroup (Fin n → ℝ) volume)
  have hvadd : ∀ (g : L) (x : Fin n → ℝ), g +ᵥ x = (g : Fin n → ℝ) + x := fun _ _ => rfl
  set one : (Fin n → ℝ) → ℝ≥0∞ := fun _ => 1 with hone
  -- the number of lattice translates of `x` that land in `M`
  set N : (Fin n → ℝ) → ℝ≥0∞ := fun x => ∑' g : L, M.indicator one (g +ᵥ x) with hN
  have hmeas : ∀ g : L, Measurable fun x : Fin n → ℝ => M.indicator one (g +ᵥ x) :=
    fun g => (measurable_const.indicator hM).comp (measurable_const_vadd g)
  have hint : ∫⁻ x in F, N x = volume M := by
    rw [← lintegral_indicator_one hM, hF.lintegral_eq_tsum'',
      lintegral_tsum fun g => (hmeas g).aemeasurable]
    rfl
  have hMtop : volume M ≠ ⊤ := hMb.measure_lt_top.ne
  obtain ⟨x, -, hx⟩ := exists_setLAverage_le (μ := volume) (s := F) (f := N)
    (by rw [hFvol]; exact one_ne_zero) hFm.nullMeasurableSet (by rw [hint]; exact hMtop)
  rw [setLAverage_eq, hint, hFvol, div_one] at hx
  refine ⟨-x, hx.trans (le_of_eq ?_)⟩
  -- identify the count with `G(M - x)`
  set P := DiscreteMinkowski.latticePoints ((fun y => y + -x) '' M) (standardIntegerLattice n)
  have himage : (fun y => y + -x) '' M = -x +ᵥ M := by
    rw [← Set.image_vadd]
    congr 1
    funext y
    rw [vadd_eq_add, add_comm]
  have hPfin : P.Finite := DiscreteMinkowski.finite_inter_lattice
    (by rw [himage]; exact hMb.vadd (-x)) _
  have hmemP : ∀ g : L, (g : Fin n → ℝ) ∈ P ↔ g +ᵥ x ∈ M := by
    intro g
    simp only [P, DiscreteMinkowski.latticePoints_apply, mem_inter_iff, mem_image,
      SetLike.mem_coe, hvadd]
    constructor
    · rintro ⟨⟨y, hy, hyg⟩, -⟩
      have : y = (g : Fin n → ℝ) + x := by rw [← hyg]; abel
      rwa [this] at hy
    · intro h
      exact ⟨⟨_, h, by abel⟩, (hLΛ g).1 g.2⟩
  have hN' : N x = (((fun g : L => (g : Fin n → ℝ)) ⁻¹' P).encard : ℝ≥0∞) := by
    rw [hN, ← ENNReal.tsum_set_one,
      tsum_subtype ((fun g : L => (g : Fin n → ℝ)) ⁻¹' P) (fun _ => (1 : ℝ≥0∞))]
    beta_reduce
    refine tsum_congr fun g => ?_
    simp only [Set.indicator_apply, mem_preimage, hmemP, hone]
  have himg : (fun g : L => (g : Fin n → ℝ)) '' ((fun g : L => (g : Fin n → ℝ)) ⁻¹' P) = P := by
    refine Set.image_preimage_eq_of_subset fun y hy => ?_
    exact ⟨⟨y, (hLΛ y).2 hy.2⟩, rfl⟩
  have hE : ((fun g : L => (g : Fin n → ℝ)) ⁻¹' P).encard = P.encard := by
    conv_rhs => rw [← himg]
    rw [Subtype.val_injective.injOn.encard_image]
  rw [hN', hE, ← hPfin.cast_ncard_eq, ENat.toENNReal_coe]

end

end LatticeVolumeInterpolation
