import CoordinateLattice

/-!
Coordinate-vector mechanisms for the successive-minimum calculation of the axis-parallel box
equality cases in Freyer--Lucas, *Interpolating between volume and lattice point enumerator with
successive minima*.

Catalog items: `integer_box_equality_for_bhw_lattice_conjecture` and
`symmetric_box_equality_case`.

At the scale `1 / m_i`, the `i`-th coordinate basis vector is a lattice point of the dilated box.
Below any scale `r` satisfying `r * m_i < 1`, every lattice point has zero `i`-th coordinate.
These are the upper and lower mechanisms from which the full rank calculation
`λ_i = 1 / m_i` will be assembled.  No ordering of the `m_i`, nor the final rank claim, is hidden
in this file.
-/

open scoped Pointwise

namespace LatticeVolumeInterpolation

variable {n : ℕ}

/-- The `i`-th real coordinate unit vector. -/
def coordinateUnitVector (n : ℕ) (i : Fin n) : Fin n → ℝ :=
  Pi.single i 1

/-- Every real coordinate unit vector belongs to the standard integer lattice. -/
theorem coordinateUnitVector_mem_standardIntegerLattice (n : ℕ) (i : Fin n) :
    coordinateUnitVector n i ∈ standardIntegerLattice n := by
  apply (mem_standardIntegerLattice_iff n _).mpr
  refine ⟨Pi.single i 1, ?_⟩
  intro j
  by_cases h : j = i <;> simp [coordinateUnitVector, h]

/-- Multiplying the `i`-th unit vector by the corresponding half-side length gives a point of the
closed coordinate box. -/
theorem scaled_coordinateUnitVector_mem_realCoordinateBox (m : Fin n → ℕ) (i : Fin n) :
    (m i : ℝ) • coordinateUnitVector n i ∈ realCoordinateBox m := by
  change (fun j => -(m j : ℝ)) ≤ (m i : ℝ) • coordinateUnitVector n i ∧
    (m i : ℝ) • coordinateUnitVector n i ≤ fun j => (m j : ℝ)
  constructor
  · intro j
    by_cases h : j = i
    · subst j
      simp [coordinateUnitVector]
    · simp [coordinateUnitVector, h]
  · intro j
    by_cases h : j = i
    · subst j
      simp [coordinateUnitVector]
    · simp [coordinateUnitVector, h]

/-- If the `i`-th half-side is positive, the `i`-th unit vector lies in the box dilated by its
reciprocal half-side length. -/
theorem coordinateUnitVector_mem_reciprocal_smul_realCoordinateBox (m : Fin n → ℕ) (i : Fin n)
    (hmi : 0 < m i) :
    coordinateUnitVector n i ∈ (m i : ℝ)⁻¹ • realCoordinateBox m := by
  refine ⟨(m i : ℝ) • coordinateUnitVector n i,
    scaled_coordinateUnitVector_mem_realCoordinateBox m i, ?_⟩
  ext j
  simp [coordinateUnitVector, hmi.ne']

/-- If `1 ≤ r m_i`, the `i`-th unit vector is a lattice point of the coordinate box dilated by
the positive scale `r`. -/
theorem coordinateUnitVector_mem_smul_realCoordinateBox_of_one_le {m : Fin n → ℕ} {r : ℝ}
    (hr : 0 < r) (i : Fin n) (hri : 1 ≤ r * m i) :
    coordinateUnitVector n i ∈ r • realCoordinateBox m := by
  have hinv : r⁻¹ ≤ (m i : ℝ) :=
    (inv_le_iff_one_le_mul₀ hr).mpr (by simpa [mul_comm] using hri)
  refine ⟨r⁻¹ • coordinateUnitVector n i, ?_, ?_⟩
  · change (fun j => -(m j : ℝ)) ≤ r⁻¹ • coordinateUnitVector n i ∧
      r⁻¹ • coordinateUnitVector n i ≤ fun j => (m j : ℝ)
    constructor
    · intro j
      by_cases h : j = i
      · subst j
        suffices -(m i : ℝ) ≤ r⁻¹ by simpa [coordinateUnitVector] using this
        exact le_trans (neg_nonpos.mpr (Nat.cast_nonneg _)) (inv_nonneg.mpr hr.le)
      · simp [coordinateUnitVector, h]
    · intro j
      by_cases h : j = i
      · subst j
        simpa [coordinateUnitVector] using hinv
      · simp [coordinateUnitVector, h]
  · ext j
    simp [coordinateUnitVector, hr.ne']

/-- If a family of distinct coordinate unit vectors lies in a set `S`, then the real span of `S`
has dimension at least the number of selected coordinates. -/
theorem finrank_span_ge_of_coordinateUnitVectors {k n : ℕ} (e : Fin k ↪ Fin n)
    (S : Set (Fin n → ℝ))
    (hmem : ∀ j, coordinateUnitVector n (e j) ∈ S) :
    k ≤ Module.finrank ℝ (Submodule.span ℝ S) := by
  let b : Fin k → Fin n → ℝ := fun j => coordinateUnitVector n (e j)
  have hli : LinearIndependent ℝ b := by
    have hbeq : b = (Pi.basisFun ℝ (Fin n)) ∘ e := by
      funext j
      simp [b, Function.comp_apply, Pi.basisFun_apply, coordinateUnitVector]
    rw [hbeq]
    exact (Pi.basisFun ℝ (Fin n)).linearIndependent.comp e e.injective
  calc
    k = Fintype.card (Fin k) := (Fintype.card_fin k).symm
    _ = Module.finrank ℝ (Submodule.span ℝ (Set.range b)) := (finrank_span_eq_card hli).symm
    _ ≤ Module.finrank ℝ (Submodule.span ℝ S) := Submodule.finrank_mono <|
      Submodule.span_mono (by
        rintro _ ⟨j, rfl⟩
        exact hmem j)

/-- The selected coordinate unit vectors give a lower bound on the rank of lattice points in a
dilated coordinate box whenever every selected half-side crosses the unit threshold. -/
theorem finrank_span_smul_realCoordinateBox_ge_of_unit_thresholds {k n : ℕ} (e : Fin k ↪ Fin n)
    (m : Fin n → ℕ) {r : ℝ} (hr : 0 < r)
    (hthreshold : ∀ j, 1 ≤ r * m (e j)) :
    k ≤ Module.finrank ℝ (Submodule.span ℝ
      ((r • realCoordinateBox m) ∩ (standardIntegerLattice n : Set (Fin n → ℝ)))) := by
  apply finrank_span_ge_of_coordinateUnitVectors e
  intro j
  constructor
  · exact coordinateUnitVector_mem_smul_realCoordinateBox_of_one_le hr (e j) (hthreshold j)
  · exact coordinateUnitVector_mem_standardIntegerLattice n (e j)

/-- The same unit-vector threshold gives a rank lower bound for the dependency's
`scaledLatticeSpan`; the coordinate box is its own central symmetral. -/
theorem finrank_scaledLatticeSpan_ge_of_unit_thresholds {k n : ℕ} (e : Fin k ↪ Fin n)
    (m : Fin n → ℕ) {r : ℝ} (hr : 0 < r)
    (hthreshold : ∀ j, 1 ≤ r * m (e j)) :
    k ≤ Module.finrank ℝ (DiscreteMinkowski.scaledLatticeSpan
      (realCoordinateBox m) (standardIntegerLattice n) r) := by
  rw [DiscreteMinkowski.scaledLatticeSpan, halfDifferenceBody_realCoordinateBox]
  exact finrank_span_smul_realCoordinateBox_ge_of_unit_thresholds e m hr hthreshold

/-- For nonincreasing positive half-side lengths, the `(i+1)`-st successive minimum is at most
the reciprocal of the `i`-th half-side.  This is the upper half of the equality calculation
`λ_{i+1} = 1/m_i`; the converse bound is kept separate. -/
theorem successiveMinimum_le_reciprocal_of_antitone {n : ℕ} (m : Fin n → ℕ)
    (hmpos : ∀ j, 0 < m j) (hmono : Antitone m) (i : Fin n) :
    DiscreteMinkowski.successiveMinimum (realCoordinateBox m) (standardIntegerLattice n)
      (i.1 + 1) ≤ (m i : ℝ)⁻¹ := by
  rw [DiscreteMinkowski.successiveMinimum_eq_sInf]
  apply csInf_le (DiscreteMinkowski.bddBelow_minimaSet _ _ _)
  constructor
  · exact inv_pos.mpr (Nat.cast_pos.mpr (hmpos i))
  · let e : Fin (i.1 + 1) ↪ Fin n :=
      ⟨Fin.castLE i.2, Fin.castLE_injective i.2⟩
    have hthreshold : ∀ j, 1 ≤ (m i : ℝ)⁻¹ * m (e j) := by
      intro j
      have hji : e j ≤ i := by
        exact Fin.le_iff_val_le_val.mpr (Nat.le_of_lt_succ j.2)
      have hmi : (m i : ℝ) ≤ m (e j) := by
        exact_mod_cast hmono hji
      calc
        1 = (m i : ℝ)⁻¹ * m i := by
          field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hmpos i))]
        _ ≤ (m i : ℝ)⁻¹ * m (e j) :=
          mul_le_mul_of_nonneg_left hmi (inv_nonneg.mpr (Nat.cast_nonneg _))
    exact finrank_scaledLatticeSpan_ge_of_unit_thresholds e m
      (inv_pos.mpr (Nat.cast_pos.mpr (hmpos i))) hthreshold

/-- If `r * m_i < 1`, every standard-lattice point of `r` times the coordinate box has zero
`i`-th coordinate. -/
theorem lattice_coordinate_eq_zero_of_mem_smul_realCoordinateBox {m : Fin n → ℕ} {r : ℝ}
    (hr : 0 ≤ r) {x : Fin n → ℝ}
    (hxbox : x ∈ r • realCoordinateBox m)
    (hxlattice : x ∈ standardIntegerLattice n)
    {i : Fin n} (hsmall : r * m i < 1) : x i = 0 := by
  obtain ⟨y, hybox, rfl⟩ := hxbox
  obtain ⟨z, hz⟩ := (mem_standardIntegerLattice_iff n (r • y)).mp hxlattice
  have hlow_y : -(m i : ℝ) ≤ y i := hybox.1 i
  have hupp_y : y i ≤ (m i : ℝ) := hybox.2 i
  have hlow : -(1 : ℝ) < (r • y) i := by
    rw [Pi.smul_apply]
    calc
      -(1 : ℝ) < -(r * m i) := by linarith
      _ = r * (-(m i : ℝ)) := by ring
      _ ≤ r * y i := mul_le_mul_of_nonneg_left hlow_y hr
  have hupp : (r • y) i < 1 := by
    rw [Pi.smul_apply]
    calc
      r * y i ≤ r * m i := mul_le_mul_of_nonneg_left hupp_y hr
      _ < 1 := hsmall
  have hz' : z i = 0 := by
    have hlow_z : (-1 : ℤ) < z i := by
      rw [hz i] at hlow
      exact_mod_cast hlow
    have hupp_z : z i < (1 : ℤ) := by
      rw [hz i] at hupp
      exact_mod_cast hupp
    omega
  simpa [hz'] using hz i

/-- Below the reciprocal of the `i`-th half-side, all lattice points of a box with
nonincreasing half-sides are supported on the first `i` coordinates.  Consequently their
real span has dimension at most `i`. -/
theorem finrank_scaledLatticeSpan_le_of_lt_reciprocal {n : ℕ} (m : Fin n → ℕ)
    (hmpos : ∀ j, 0 < m j) (hmono : Antitone m) (i : Fin n) {r : ℝ}
    (hr : 0 < r) (hsmall : r < (m i : ℝ)⁻¹) :
    Module.finrank ℝ (DiscreteMinkowski.scaledLatticeSpan
      (realCoordinateBox m) (standardIntegerLattice n) r) ≤ i.1 := by
  have hmi : 0 < (m i : ℝ) := Nat.cast_pos.mpr (hmpos i)
  have hrmi : r * (m i : ℝ) < 1 := by
    calc
      r * (m i : ℝ) < (m i : ℝ)⁻¹ * (m i : ℝ) :=
        mul_lt_mul_of_pos_right hsmall hmi
      _ = 1 := inv_mul_cancel₀ hmi.ne'
  rw [DiscreteMinkowski.scaledLatticeSpan, halfDifferenceBody_realCoordinateBox]
  have hsubset :
      (r • realCoordinateBox m) ∩ (standardIntegerLattice n : Set (Fin n → ℝ)) ⊆
        Pi.spanSubset ℝ {j : Fin n | j < i} := by
    rintro x ⟨hxbox, hxlattice⟩
    refine Pi.mem_spanSubset_iff.mpr ?_
    intro j hj
    have hij : i ≤ j := le_of_not_gt hj
    have hmji : (m j : ℝ) ≤ m i := by exact_mod_cast hmono hij
    have hrmj : r * (m j : ℝ) < 1 :=
      (mul_le_mul_of_nonneg_left hmji hr.le).trans_lt hrmi
    exact lattice_coordinate_eq_zero_of_mem_smul_realCoordinateBox hr.le hxbox hxlattice hrmj
  calc
    Module.finrank ℝ (Submodule.span ℝ
        ((r • realCoordinateBox m) ∩ (standardIntegerLattice n : Set (Fin n → ℝ))))
        ≤ Module.finrank ℝ (Pi.spanSubset ℝ {j : Fin n | j < i}) :=
      Submodule.finrank_mono (Submodule.span_le.mpr hsubset)
    _ = Set.ncard {j : Fin n | j < i} := Pi.dim_spanSubset
    _ = i.1 := by
      have hset : {j : Fin n | j < i} = (↑(Finset.Iio i) : Set (Fin n)) := by
        ext j
        simp
      rw [hset, Set.ncard_coe_finset, Fin.card_Iio]

/-- For nonincreasing positive integral half-sides, the `(i+1)`-st successive minimum of
the coordinate box is exactly the reciprocal of the `i`-th half-side. -/
theorem successiveMinimum_realCoordinateBox_eq_reciprocal_of_antitone {n : ℕ}
    (m : Fin n → ℕ) (hmpos : ∀ j, 0 < m j) (hmono : Antitone m) (i : Fin n) :
    DiscreteMinkowski.successiveMinimum (realCoordinateBox m) (standardIntegerLattice n)
      (i.1 + 1) = (m i : ℝ)⁻¹ := by
  apply le_antisymm (successiveMinimum_le_reciprocal_of_antitone m hmpos hmono i)
  rw [DiscreteMinkowski.successiveMinimum_eq_sInf]
  apply le_csInf
  · refine ⟨(m i : ℝ)⁻¹, inv_pos.mpr (Nat.cast_pos.mpr (hmpos i)), ?_⟩
    let e : Fin (i.1 + 1) ↪ Fin n :=
      ⟨Fin.castLE i.2, Fin.castLE_injective i.2⟩
    have hthreshold : ∀ j, 1 ≤ (m i : ℝ)⁻¹ * m (e j) := by
      intro j
      have hji : e j ≤ i := Fin.le_iff_val_le_val.mpr (Nat.le_of_lt_succ j.2)
      have hmi : (m i : ℝ) ≤ m (e j) := by exact_mod_cast hmono hji
      calc
        1 = (m i : ℝ)⁻¹ * m i := by
          field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hmpos i))]
        _ ≤ (m i : ℝ)⁻¹ * m (e j) :=
          mul_le_mul_of_nonneg_left hmi (inv_nonneg.mpr (Nat.cast_nonneg _))
    exact finrank_scaledLatticeSpan_ge_of_unit_thresholds e m
      (inv_pos.mpr (Nat.cast_pos.mpr (hmpos i))) hthreshold
  · intro r hrset
    by_contra hnot
    have hlt : r < (m i : ℝ)⁻¹ := lt_of_not_ge hnot
    have hle := finrank_scaledLatticeSpan_le_of_lt_reciprocal m hmpos hmono i hrset.1 hlt
    have hrank := hrset.2
    omega

end LatticeVolumeInterpolation
