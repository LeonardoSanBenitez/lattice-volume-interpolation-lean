import AntiBlocking

/-!
# The general Rogers--Shephard section-projection bound

Catalog item `rogers_shephard_section_projection`, Eq. (4.1). For a compact
convex body and any coordinate subspace, the product of the origin-section volume
and complementary projection volume is at most the binomial coefficient times
the body's volume. The projection need not itself lie in the body.

For each projected point choose any lift in the body. Convexity embeds a translated
copy of a scaled origin section into the intermediate fibre. Translation does not
change its volume. Integrating these lower bounds and the Beta weight proves the
exact constant. No measurable choice of lifts is needed: only the pointwise fibre
inequality is integrated. The argument also handles an empty section and the two
zero-dimensional endpoint factors.
-/

open MeasureTheory Set Module
open scoped ENNReal

namespace LatticeVolumeInterpolation

noncomputable section

variable {n : ℕ}

/-- **Eq. (4.1)** for an arbitrary compact convex body. -/
theorem rogers_shephard_section_projection {K : Set (Fin n → ℝ)} (hKc : IsCompact K)
    (hKconv : Convex ℝ K) (I : Finset (Fin n)) :
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
  have hBcpt : IsCompact (projectionOff I K) := by
    refine hKc.image ?_
    exact continuous_pi fun i => continuous_apply i.1
  have hk : finrank ℝ ({i // i ∈ I} → ℝ) = I.card := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  have hm : finrank ℝ ({i // i ∉ I} → ℝ) = n - I.card := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_subtype_compl, Fintype.card_coe,
      Fintype.card_fin]
  have hjoin := section_projection_volume_lower_bound' (volume : Measure ({i // i ∈ I} → ℝ))
    (volume : Measure ({i // i ∉ I} → ℝ)) hk hm hBcpt hCconv hCm
    (A := sectionOn I K) (fun a ha => ha) (fun b hb => by
      obtain ⟨x, hx, rfl⟩ := hb
      refine ⟨(coordSplit I x).1, ?_⟩
      change (coordSplit I).symm (coordSplit I x) ∈ K
      simpa using hx)
  rw [← hvolK] at hjoin
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
  calc volume (sectionOn I K) * volume (projectionOff I K)
      = (n.choose I.card : ℝ≥0∞) *
          (volume (sectionOn I K) * volume (projectionOff I K) * (n.choose I.card : ℝ≥0∞)⁻¹) := by
        rw [mul_comm (n.choose I.card : ℝ≥0∞), mul_assoc _ ((n.choose I.card : ℝ≥0∞))⁻¹,
          ENNReal.inv_mul_cancel hc0 hctop, mul_one]
    _ ≤ (n.choose I.card : ℝ≥0∞) * volume K := mul_le_mul_right hjoin _

end

end LatticeVolumeInterpolation
