import SimplexLattice
import CoordinateMinima

/-! Direct successive-minimum calculation for the standard simplex. -/

open scoped BigOperators Pointwise

namespace LatticeVolumeInterpolation

/-- The paper's standard simplex `T_n = conv {0,e₁,...,eₙ}` in inequality form. -/
abbrev realStandardSimplex (n : ℕ) : Set (Fin n → ℝ) :=
  realDilatedStandardSimplex n 1

theorem zero_mem_realStandardSimplex (n : ℕ) :
    (0 : Fin n → ℝ) ∈ realStandardSimplex n := by
  constructor
  · simp
  · simp

theorem coordinateUnitVector_mem_realStandardSimplex (n : ℕ) (i : Fin n) :
    coordinateUnitVector n i ∈ realStandardSimplex n := by
  constructor
  · intro j
    simp only [coordinateUnitVector, Pi.single_apply]
    split_ifs <;> norm_num
  · simp [coordinateUnitVector]

/-- Every coordinate of a point of `T_n` lies in `[0,1]`. -/
theorem realStandardSimplex_coordinate_bounds {n : ℕ} {x : Fin n → ℝ}
    (hx : x ∈ realStandardSimplex n) (i : Fin n) : 0 ≤ x i ∧ x i ≤ 1 := by
  refine ⟨hx.1 i, ?_⟩
  calc
    x i ≤ ∑ j, x j := Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)
    _ ≤ 1 := by simpa only [Nat.cast_one] using hx.2

/-- Below scale `2`, every standard-lattice point of the central symmetral of `T_n` is zero. -/
theorem latticePoint_eq_zero_of_mem_smul_halfDifference_realStandardSimplex {n : ℕ}
    {r : ℝ} (hr : 0 < r) (hrtwo : r < 2) {x : Fin n → ℝ}
    (hxbody : x ∈ r • DiscreteMinkowski.halfDifferenceBody (realStandardSimplex n))
    (hxlattice : x ∈ standardIntegerLattice n) : x = 0 := by
  obtain ⟨y, hy, rfl⟩ := hxbody
  rw [DiscreteMinkowski.halfDifferenceBody_apply] at hy
  obtain ⟨d, hd, rfl⟩ := hy
  obtain ⟨a, ha, b, hb, rfl⟩ := hd
  obtain ⟨z, hz⟩ := (mem_standardIntegerLattice_iff n (r • ((2 : ℝ)⁻¹ • (a - b)))).mp
    hxlattice
  funext i
  have hai := realStandardSimplex_coordinate_bounds ha i
  have hbi := realStandardSimplex_coordinate_bounds hb i
  have hlow : -(1 : ℝ) < (r • ((2 : ℝ)⁻¹ • (a - b))) i := by
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    norm_num
    nlinarith
  have hupp : (r • ((2 : ℝ)⁻¹ • (a - b))) i < 1 := by
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    norm_num
    nlinarith
  have hzi : z i = 0 := by
    have hlowz : (-1 : ℤ) < z i := by
      rw [hz i] at hlow
      exact_mod_cast hlow
    have huppz : z i < (1 : ℤ) := by
      rw [hz i] at hupp
      exact_mod_cast hupp
    omega
  simpa [hz i, hzi]

/-- At scale `2`, the first `i+1` coordinate vectors witness rank at least `i+1`. -/
theorem finrank_scaledLatticeSpan_realStandardSimplex_two {n : ℕ} (i : Fin n) :
    i.1 + 1 ≤ Module.finrank ℝ (DiscreteMinkowski.scaledLatticeSpan
      (realStandardSimplex n) (standardIntegerLattice n) 2) := by
  rw [DiscreteMinkowski.scaledLatticeSpan]
  let e : Fin (i.1 + 1) ↪ Fin n :=
    ⟨Fin.castLE i.2, Fin.castLE_injective i.2⟩
  apply finrank_span_ge_of_coordinateUnitVectors e
  intro j
  constructor
  · simpa using DiscreteMinkowski.sub_mem_two_smul_halfDifferenceBody
      (coordinateUnitVector_mem_realStandardSimplex n (e j))
      (zero_mem_realStandardSimplex n)
  · exact coordinateUnitVector_mem_standardIntegerLattice n (e j)

/-- The paper's elementary equality `λ_i(T_n)=2`, with its one-based index represented by
`i.1 + 1` for `i : Fin n`. -/
theorem successiveMinimum_realStandardSimplex_eq_two {n : ℕ} (i : Fin n) :
    DiscreteMinkowski.successiveMinimum (realStandardSimplex n)
      (standardIntegerLattice n) (i.1 + 1) = 2 := by
  rw [DiscreteMinkowski.successiveMinimum_eq_sInf]
  apply le_antisymm
  · exact csInf_le (DiscreteMinkowski.bddBelow_minimaSet _ _ _)
      ⟨by norm_num, finrank_scaledLatticeSpan_realStandardSimplex_two i⟩
  · apply le_csInf
    · exact ⟨2, by norm_num, finrank_scaledLatticeSpan_realStandardSimplex_two i⟩
    · intro r hrset
      by_contra hnot
      have hrtwo : r < 2 := lt_of_not_ge hnot
      have hsubset :
          (r • DiscreteMinkowski.halfDifferenceBody (realStandardSimplex n)) ∩
              (standardIntegerLattice n : Set (Fin n → ℝ)) ⊆ {0} := by
        rintro x ⟨hxbody, hxlattice⟩
        exact latticePoint_eq_zero_of_mem_smul_halfDifference_realStandardSimplex
          hrset.1 hrtwo hxbody hxlattice
      have hspan : DiscreteMinkowski.scaledLatticeSpan (realStandardSimplex n)
          (standardIntegerLattice n) r = ⊥ := by
        rw [DiscreteMinkowski.scaledLatticeSpan]
        apply le_antisymm
        · apply Submodule.span_le.mpr
          intro x hx
          simpa using hsubset hx
        · exact bot_le
      change 0 < r ∧ i.1 + 1 ≤ Module.finrank ℝ
        (DiscreteMinkowski.scaledLatticeSpan (realStandardSimplex n)
          (standardIntegerLattice n) r) at hrset
      rw [hspan] at hrset
      simp at hrset

/-- Every coordinate of a point of the integer dilate `m T_n` lies in `[0,m]`. -/
theorem realDilatedStandardSimplex_coordinate_bounds {n m : ℕ} {x : Fin n → ℝ}
    (hx : x ∈ realDilatedStandardSimplex n m) (i : Fin n) :
    0 ≤ x i ∧ x i ≤ m := by
  refine ⟨hx.1 i, ?_⟩
  calc
    x i ≤ ∑ j, x j := Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)
    _ ≤ (m : ℝ) := hx.2

theorem zero_mem_realDilatedStandardSimplex (n m : ℕ) :
    (0 : Fin n → ℝ) ∈ realDilatedStandardSimplex n m := by
  constructor
  · simp
  · simp

theorem scaled_coordinateUnitVector_mem_realDilatedStandardSimplex (n m : ℕ) (i : Fin n) :
    (m : ℝ) • coordinateUnitVector n i ∈ realDilatedStandardSimplex n m := by
  classical
  constructor
  · intro j
    simp only [Pi.smul_apply, coordinateUnitVector, Pi.single_apply, smul_eq_mul]
    split_ifs <;> positivity
  · calc
      (∑ j, ((m : ℝ) • coordinateUnitVector n i) j) = (m : ℝ) := by
        rw [Finset.sum_eq_single i]
        · simp [coordinateUnitVector]
        · intro j _hj hji
          simp [coordinateUnitVector, hji]
        · simp
      _ ≤ (m : ℝ) := le_rfl

/-- If `r m < 2`, the central symmetral of `m T_n` contains no nonzero standard-lattice
point at scale `r`. -/
theorem latticePoint_eq_zero_of_mem_smul_halfDifference_realDilatedStandardSimplex
    {n m : ℕ} {r : ℝ} (hr : 0 < r) (hrsmall : r * m < 2) {x : Fin n → ℝ}
    (hxbody : x ∈ r • DiscreteMinkowski.halfDifferenceBody
      (realDilatedStandardSimplex n m))
    (hxlattice : x ∈ standardIntegerLattice n) : x = 0 := by
  obtain ⟨y, hy, rfl⟩ := hxbody
  rw [DiscreteMinkowski.halfDifferenceBody_apply] at hy
  obtain ⟨d, hd, rfl⟩ := hy
  obtain ⟨a, ha, b, hb, rfl⟩ := hd
  obtain ⟨z, hz⟩ := (mem_standardIntegerLattice_iff n (r • ((2 : ℝ)⁻¹ • (a - b)))).mp
    hxlattice
  funext i
  have hai := realDilatedStandardSimplex_coordinate_bounds ha i
  have hbi := realDilatedStandardSimplex_coordinate_bounds hb i
  have hlow : -(1 : ℝ) < (r • ((2 : ℝ)⁻¹ • (a - b))) i := by
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    norm_num
    nlinarith
  have hupp : (r • ((2 : ℝ)⁻¹ • (a - b))) i < 1 := by
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    norm_num
    nlinarith
  have hzi : z i = 0 := by
    have hlowz : (-1 : ℤ) < z i := by
      rw [hz i] at hlow
      exact_mod_cast hlow
    have huppz : z i < (1 : ℤ) := by
      rw [hz i] at hupp
      exact_mod_cast hupp
    omega
  simpa [hz i, hzi]

/-- At the critical scale `2/m`, the first `i+1` coordinate vectors witness the required
rank in the central symmetral of `m T_n`. -/
theorem finrank_scaledLatticeSpan_realDilatedStandardSimplex_two_div {n m : ℕ}
    (hm : 0 < m) (i : Fin n) :
    i.1 + 1 ≤ Module.finrank ℝ (DiscreteMinkowski.scaledLatticeSpan
      (realDilatedStandardSimplex n m) (standardIntegerLattice n) (2 / m)) := by
  rw [DiscreteMinkowski.scaledLatticeSpan]
  let e : Fin (i.1 + 1) ↪ Fin n :=
    ⟨Fin.castLE i.2, Fin.castLE_injective i.2⟩
  apply finrank_span_ge_of_coordinateUnitVectors e
  intro j
  constructor
  · have hscaled := DiscreteMinkowski.sub_mem_two_smul_halfDifferenceBody
      (scaled_coordinateUnitVector_mem_realDilatedStandardSimplex n m (e j))
      (zero_mem_realDilatedStandardSimplex n m)
    obtain ⟨y, hy, hyeq⟩ := hscaled
    refine ⟨y, hy, ?_⟩
    ext k
    have hk := congrFun hyeq k
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.zero_apply, sub_zero, smul_eq_mul] at hk ⊢
    have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
    calc
      2 / (m : ℝ) * y k = (2 * y k) / m := by ring
      _ = ((m : ℝ) * coordinateUnitVector n (e j) k) / m := by rw [hk]
      _ = coordinateUnitVector n (e j) k := by field_simp
  · exact coordinateUnitVector_mem_standardIntegerLattice n (e j)

/-- Integer scaling of the paper's simplex equality: `λ_i(mT_n)=2/m`. -/
theorem successiveMinimum_realDilatedStandardSimplex_eq_two_div {n m : ℕ}
    (hm : 0 < m) (i : Fin n) :
    DiscreteMinkowski.successiveMinimum (realDilatedStandardSimplex n m)
      (standardIntegerLattice n) (i.1 + 1) = 2 / m := by
  rw [DiscreteMinkowski.successiveMinimum_eq_sInf]
  have hcritical : (0 : ℝ) < 2 / m := by positivity
  have hrank := finrank_scaledLatticeSpan_realDilatedStandardSimplex_two_div hm i
  apply le_antisymm
  · exact csInf_le (DiscreteMinkowski.bddBelow_minimaSet _ _ _) ⟨hcritical, hrank⟩
  · apply le_csInf
    · exact ⟨2 / m, hcritical, hrank⟩
    · intro r hrset
      by_contra hnot
      have hrlt : r < 2 / (m : ℝ) := lt_of_not_ge hnot
      have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
      have hrsmall : r * (m : ℝ) < 2 := by
        calc
          r * (m : ℝ) < (2 / (m : ℝ)) * m := mul_lt_mul_of_pos_right hrlt hmreal
          _ = 2 := by field_simp
      have hsubset :
          (r • DiscreteMinkowski.halfDifferenceBody
              (realDilatedStandardSimplex n m)) ∩
              (standardIntegerLattice n : Set (Fin n → ℝ)) ⊆ {0} := by
        rintro x ⟨hxbody, hxlattice⟩
        exact latticePoint_eq_zero_of_mem_smul_halfDifference_realDilatedStandardSimplex
          hrset.1 hrsmall hxbody hxlattice
      have hspan : DiscreteMinkowski.scaledLatticeSpan
          (realDilatedStandardSimplex n m) (standardIntegerLattice n) r = ⊥ := by
        rw [DiscreteMinkowski.scaledLatticeSpan]
        apply le_antisymm
        · apply Submodule.span_le.mpr
          intro x hx
          simpa using hsubset hx
        · exact bot_le
      change 0 < r ∧ i.1 + 1 ≤ Module.finrank ℝ
        (DiscreteMinkowski.scaledLatticeSpan (realDilatedStandardSimplex n m)
          (standardIntegerLattice n) r) at hrset
      rw [hspan] at hrset
      simp at hrset

end LatticeVolumeInterpolation
