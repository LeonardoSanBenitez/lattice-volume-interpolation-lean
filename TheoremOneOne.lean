import AntiBlockingUpperBound
import MinimaAntiBlocking

/-!
# Theorem 1.1, Eq. (1.8)

Catalog item `theorem_1_1_upper_bound`: for `K ∈ K^n`,

  `G(K) ≤ vol(K) ∏_{i=1}^n (1 + n λ_i(K) / 2)`.

This file proves it for anti-blocking bodies (`theorem_1_1_upper_antiBlocking`), by the
paper's route after its first reduction: Lemma 3.3 renumbers the coordinates so that
`(2/λ_i) e_i ∈ K`, and `upper_bound_antiBlocking` (Eq. (4.1), the simplex in `K ∩ L_I` and
Davenport's inequality) gives the bound with `s_i = 2/λ_i`. The reduction of a general body to
an anti-blocking one is Theorem 3.1.
-/

open MeasureTheory Set Module
open scoped ENNReal

namespace LatticeVolumeInterpolation

noncomputable section

variable {n : ℕ}

/-- **Eq. (1.8) for a compact anti-blocking convex body.** -/
theorem theorem_1_1_upper_antiBlocking {K : Set (Fin n → ℝ)} (hKc : IsCompact K)
    (hKb : DiscreteMinkowski.IsPaperConvexBody K) (hK : IsAntiBlocking K) :
    ((DiscreteMinkowski.latticePoints K (standardIntegerLattice n)).ncard : ℝ≥0∞) ≤
      volume K * ENNReal.ofReal (∏ i : Fin n, (1 + (n : ℝ) *
        DiscreteMinkowski.successiveMinimum K (standardIntegerLattice n) (i.1 + 1) / 2)) := by
  classical
  obtain ⟨σ, hσ⟩ := lemma_3_3 hKc hKb hK
  set lam : Fin n → ℝ := fun i =>
    DiscreteMinkowski.successiveMinimum K (standardIntegerLattice n) (i.1 + 1) with hlam
  have hdim : finrank ℝ (Fin n → ℝ) = n := Module.finrank_fin_fun ℝ
  have hpos : ∀ i, 0 < lam i := fun i =>
    DiscreteMinkowski.successiveMinimum_pos hKb (by omega) (by rw [hdim]; exact i.2)
  set s : Fin n → ℝ := fun j => 2 / lam (σ.symm j) with hs
  have hspos : ∀ j, 0 < s j := fun j => div_pos two_pos (hpos _)
  have hmem : ∀ j, Pi.single j (s j) ∈ K := by
    intro j
    have h := (hσ (σ.symm j)).2
    rw [Equiv.apply_symm_apply] at h
    have heq : (Pi.single j (s j) : Fin n → ℝ) = (2 / lam (σ.symm j)) • Pi.single j (1 : ℝ) := by
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    rw [heq]
    exact h
  have hbound := upper_bound_antiBlocking hKc hKb.2.1 hK hspos hmem
  have hprod : ∏ j, (1 + (n : ℝ) / s j) = ∏ i : Fin n, (1 + (n : ℝ) * lam i / 2) := by
    rw [← Equiv.prod_comp σ (fun j => 1 + (n : ℝ) / s j)]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [hs, Equiv.symm_apply_apply]
    have := (hpos i).ne'
    field_simp
  rw [hprod] at hbound
  exact hbound

end

end LatticeVolumeInterpolation
