import TheoremOneOne
import TheoremThreeOne
import Mathlib.Algebra.Module.ZLattice.Covolume

/-!
# Theorem 1.1, Eq. (1.8), and Corollary 1.2

Catalog items `theorem_1_1_upper_bound` and `corollary_1_2`.

**Theorem 1.1, Eq. (1.8).** For `K ∈ K^n`, `G(K) ≤ vol(K) ∏_{i=1}^n (1 + n λ_i(K)/2)`.
By Theorem 3.1 there is an anti-blocking `A` with the same volume, at least as many lattice
points and no larger minima; Eq. (1.8) holds for `A` (`theorem_1_1_upper_antiBlocking`), and its
right-hand side increases with every `λ_i`.

**Corollary 1.2.** `G(K) ≤ ∏_{i=1}^n (2/λ_i(K) + n)`, by substituting the upper bound of
Minkowski's second theorem, `vol(K) ∏ λ_i ≤ 2^n det(ℤ^n) = 2^n`, into Eq. (1.8). It is stated as
`DiscreteMinkowski.FreyerLucasBound`, the proposition that the formalization of Tointon's paper
states for this paper's result and does not prove.
-/

open MeasureTheory Set Module
open scoped ENNReal

namespace LatticeVolumeInterpolation

noncomputable section

variable {n : ℕ}

/-- **Theorem 1.1, Eq. (1.8).** -/
theorem theorem_1_1_upper {K : Set (Fin n → ℝ)} (hKc : IsCompact K)
    (hKb : DiscreteMinkowski.IsPaperConvexBody K) :
    ((DiscreteMinkowski.latticePoints K (standardIntegerLattice n)).ncard : ℝ≥0∞) ≤
      volume K * ENNReal.ofReal (∏ i : Fin n, (1 + (n : ℝ) *
        DiscreteMinkowski.successiveMinimum K (standardIntegerLattice n) (i.1 + 1) / 2)) := by
  obtain ⟨A, hAc, hAb, hAab, hvol, hcount, hmin⟩ := theorem_3_1 hKc hKb
  have hA := theorem_1_1_upper_antiBlocking hAc hAb hAab
  rw [hvol] at hA
  have hprod : ∏ i : Fin n, (1 + (n : ℝ) *
      DiscreteMinkowski.successiveMinimum A (standardIntegerLattice n) (i.1 + 1) / 2) ≤
      ∏ i : Fin n, (1 + (n : ℝ) *
        DiscreteMinkowski.successiveMinimum K (standardIntegerLattice n) (i.1 + 1) / 2) := by
    refine Finset.prod_le_prod (fun i _ => ?_) (fun i _ => ?_)
    · have := DiscreteMinkowski.successiveMinimum_nonneg A (standardIntegerLattice n) (i.1 + 1)
      positivity
    · have := hmin i
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith
  calc ((DiscreteMinkowski.latticePoints K (standardIntegerLattice n)).ncard : ℝ≥0∞)
      ≤ ((DiscreteMinkowski.latticePoints A (standardIntegerLattice n)).ncard : ℝ≥0∞) := by
        exact_mod_cast hcount
    _ ≤ _ := hA
    _ ≤ _ := mul_le_mul_right (ENNReal.ofReal_le_ofReal hprod) _

/-- A `ℤ`-basis of `ℤ^n` whose vectors are the standard basis vectors of `ℝ^n`. -/
def standardLatticeBasis (n : ℕ) : Basis (Fin n) ℤ (standardIntegerLattice n) :=
  (Pi.basisFun ℤ (Fin n)).map
    (LinearEquiv.ofInjective (intToRealCoordinates n) (intToRealCoordinates_injective n))

theorem standardLatticeBasis_apply (i : Fin n) :
    ((standardLatticeBasis n i : standardIntegerLattice n) : Fin n → ℝ) =
      Pi.single i (1 : ℝ) := by
  funext l
  rw [standardLatticeBasis, Basis.map_apply, Pi.basisFun_apply]
  erw [LinearEquiv.ofInjective_apply]
  by_cases h : l = i
  · subst h; simp [intToRealCoordinates]
  · simp [intToRealCoordinates, Pi.single_eq_of_ne h]

/-- **The standard lattice has covolume `1`.** -/
theorem covolume_standardIntegerLattice (n : ℕ) :
    ZLattice.covolume (standardIntegerLattice n) = 1 := by
  rw [ZLattice.covolume_eq_det _ (standardLatticeBasis n)]
  have : Matrix.of ((↑) ∘ standardLatticeBasis n) = (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i l
    simp [standardLatticeBasis_apply, Matrix.one_apply, Pi.single_apply, eq_comm]
  rw [this, Matrix.det_one, abs_one]

/-- **Corollary 1.2**, `G(K) ≤ ∏ (2/λ_i + n)`, in the dependency's statement. -/
theorem corollary_1_2 {K : Set (Fin n → ℝ)} (hKc : IsCompact K)
    (hKb : DiscreteMinkowski.IsPaperConvexBody K) :
    DiscreteMinkowski.FreyerLucasBound K (standardIntegerLattice n) := by
  unfold DiscreteMinkowski.FreyerLucasBound
  have hdim : finrank ℝ (Fin n → ℝ) = n := Module.finrank_fin_fun ℝ
  rw [hdim, ← Fin.prod_univ_eq_prod_range
    (fun i => 2 / DiscreteMinkowski.successiveMinimum K (standardIntegerLattice n) (i + 1) +
      (n : ℝ)) n]
  set lam : Fin n → ℝ := fun i =>
    DiscreteMinkowski.successiveMinimum K (standardIntegerLattice n) (i.1 + 1) with hlam
  have hpos : ∀ i, 0 < lam i := fun i =>
    DiscreteMinkowski.successiveMinimum_pos hKb (by omega) (by rw [hdim]; exact i.2)
  have hKtop : volume K ≠ ⊤ := hKc.measure_lt_top.ne
  -- Eq. (1.8) with the volume as a real number
  have h18 := theorem_1_1_upper hKc hKb
  have hP : 0 ≤ ∏ i : Fin n, (1 + (n : ℝ) * lam i / 2) :=
    Finset.prod_nonneg fun i _ => by have := hpos i; positivity
  have hreal : ((DiscreteMinkowski.latticePoints K (standardIntegerLattice n)).ncard : ℝ) ≤
      (volume K).toReal * ∏ i : Fin n, (1 + (n : ℝ) * lam i / 2) := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top hKtop ENNReal.ofReal_ne_top) h18
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hP, ENNReal.toReal_natCast] at this
  -- Minkowski's second theorem: `vol(K) ∏ λ_i ≤ 2^n`
  have hmink : (volume K).toReal * ∏ i : Fin n, lam i ≤ 2 ^ n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one, pow_zero]
      have : (volume (Set.univ : Set (Fin 0 → ℝ))) = 1 := by
        rw [volume_pi, Measure.pi_of_empty]; simp
      have hle := measure_mono (μ := volume) (Set.subset_univ K)
      rw [this] at hle
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hle)
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have := DiscreteMinkowski.minkowski_second_theorem volume hKb (standardIntegerLattice (m + 1))
        m (by rw [hdim])
      rw [covolume_standardIntegerLattice, mul_one,
        ← Fin.prod_univ_eq_prod_range
          (fun i => DiscreteMinkowski.successiveMinimum K (standardIntegerLattice (m + 1)) (i + 1))
          (m + 1)] at this
      exact this
  -- regroup: `1 + nλ/2 = (λ/2)(2/λ + n)`
  have hfac : ∏ i : Fin n, (1 + (n : ℝ) * lam i / 2) =
      (∏ i : Fin n, lam i) / 2 ^ n * ∏ i : Fin n, (2 / lam i + (n : ℝ)) := by
    rw [div_mul_eq_mul_div, ← Finset.prod_mul_distrib, eq_div_iff (by positivity),
      ← Fin.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    have := (hpos i).ne'
    field_simp
  have hQ : 0 ≤ ∏ i : Fin n, (2 / lam i + (n : ℝ)) :=
    Finset.prod_nonneg fun i _ => by have := hpos i; positivity
  calc ((DiscreteMinkowski.latticePoints K (standardIntegerLattice n)).ncard : ℝ)
      ≤ (volume K).toReal * ∏ i : Fin n, (1 + (n : ℝ) * lam i / 2) := hreal
    _ = ((volume K).toReal * ∏ i : Fin n, lam i) / 2 ^ n *
          ∏ i : Fin n, (2 / lam i + (n : ℝ)) := by rw [hfac]; ring
    _ ≤ 2 ^ n / 2 ^ n * ∏ i : Fin n, (2 / lam i + (n : ℝ)) := by
        gcongr
    _ = ∏ i : Fin n, (2 / lam i + (n : ℝ)) := by rw [div_self (by positivity), one_mul]

end

end LatticeVolumeInterpolation
