import BoxCounts

/-!
The standard coordinate lattice and axis-parallel boxes used in the equality sentences of
Freyer--Lucas, *Interpolating between volume and lattice point enumerator with successive minima*.

Catalog items: `integer_box_equality_for_bhw_lattice_conjecture` and
`symmetric_box_equality_case`.

The paper works with the standard lattice `ℤ^n ⊆ ℝ^n`.  We represent it as the range of the
coordinatewise integer-to-real linear map, rather than treating its points informally.  The final
theorem identifies the resulting finite enumeration with `DiscreteMinkowski.latticePoints` of the
real coordinate box.  It deliberately proves only the counting component of the paper's equality
claims: the successive-minima calculation remains a separate obligation.
-/

open scoped BigOperators Pointwise

namespace LatticeVolumeInterpolation

/-- The coordinatewise inclusion of the integer module into the real coordinate space. -/
noncomputable def intToRealCoordinates (n : ℕ) :
    (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℝ) :=
  LinearMap.piMap fun _ => (Int.castAddHom ℝ).toIntLinearMap

/-- The standard lattice `ℤ^n` inside `ℝ^n`. -/
noncomputable def standardIntegerLattice (n : ℕ) : Submodule ℤ (Fin n → ℝ) :=
  LinearMap.range (intToRealCoordinates n)

/-- A real coordinate vector is in the standard lattice exactly when all of its coordinates are
integer-valued. -/
theorem mem_standardIntegerLattice_iff (n : ℕ) (x : Fin n → ℝ) :
    x ∈ standardIntegerLattice n ↔ ∃ z : Fin n → ℤ, ∀ i, x i = z i := by
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, fun i => rfl⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, funext fun i => by
      simpa [intToRealCoordinates] using (hz i).symm⟩

/-- Coordinatewise integer-to-real inclusion is injective. -/
theorem intToRealCoordinates_injective (n : ℕ) :
    Function.Injective (intToRealCoordinates n) := by
  intro x y hxy
  funext i
  apply (Int.cast_injective : Function.Injective (Int.cast : ℤ → ℝ))
  simpa [intToRealCoordinates] using congrFun hxy i

/-- The embedding underlying the finite enumeration of the standard lattice points. -/
noncomputable def intToRealCoordinatesEmbedding (n : ℕ) :
    (Fin n → ℤ) ↪ (Fin n → ℝ) :=
  ⟨intToRealCoordinates n, intToRealCoordinates_injective n⟩

/-- The real closed coordinate box with integral half-side lengths `m`. -/
noncomputable def realCoordinateBox (m : Fin n → ℕ) : Set (Fin n → ℝ) :=
  Set.Icc (fun i => -(m i : ℝ)) (fun i => m i)

/-- A finite enumeration of the standard-lattice points of `realCoordinateBox m`. -/
noncomputable def coordinateLatticePoints (m : Fin n → ℕ) : Finset (Fin n → ℝ) :=
  (integerBox m).map (intToRealCoordinatesEmbedding n)

/-- The real coordinate box has `∏ i, (2 m_i + 1)` standard-lattice points. -/
theorem card_coordinateLatticePoints (m : Fin n → ℕ) :
    (coordinateLatticePoints m).card = ∏ i, (2 * m i + 1) := by
  rw [coordinateLatticePoints, Finset.card_map, card_integerBox]

/-- The finite coordinate enumeration is exactly the lattice-point set of the real box. -/
theorem coordinateLatticePoints_coe (m : Fin n → ℕ) :
    (coordinateLatticePoints m : Set (Fin n → ℝ)) =
      realCoordinateBox m ∩ standardIntegerLattice n := by
  ext x
  change x ∈ coordinateLatticePoints m ↔
    x ∈ realCoordinateBox m ∧ x ∈ standardIntegerLattice n
  rw [coordinateLatticePoints, Finset.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [integerBox, Finset.mem_Icc] at hz
    constructor
    · change (∀ i, -(m i : ℝ) ≤ (intToRealCoordinatesEmbedding n) z i) ∧
        ∀ i, (intToRealCoordinatesEmbedding n) z i ≤ (m i : ℝ)
      constructor
      · intro i
        have hzi : -(m i : ℤ) ≤ z i := hz.1 i
        have hzi' : -(m i : ℝ) ≤ (z i : ℝ) := by exact_mod_cast hzi
        simpa [intToRealCoordinatesEmbedding, intToRealCoordinates] using hzi'
      · intro i
        have hzi : z i ≤ m i := hz.2 i
        have hzi' : (z i : ℝ) ≤ (m i : ℝ) := by exact_mod_cast hzi
        simpa [intToRealCoordinatesEmbedding, intToRealCoordinates] using hzi'
    · exact (mem_standardIntegerLattice_iff n _).mpr ⟨z, fun i => rfl⟩
  · rintro ⟨hxbox, hxlattice⟩
    obtain ⟨z, hz⟩ := (mem_standardIntegerLattice_iff n x).mp hxlattice
    refine ⟨z, ?_, ?_⟩
    · rw [integerBox, Finset.mem_Icc]
      constructor
      · intro i
        have hxi : -(m i : ℝ) ≤ x i := hxbox.1 i
        rw [hz i] at hxi
        exact_mod_cast hxi
      · intro i
        have hxi : x i ≤ (m i : ℝ) := hxbox.2 i
        rw [hz i] at hxi
        exact_mod_cast hxi
    · funext i
      simpa [intToRealCoordinatesEmbedding, intToRealCoordinates] using (hz i).symm

/-- The preceding finite enumeration is the standard `latticePoints` construction from the
discrete-Minkowski dependency. -/
theorem coordinateLatticePoints_coe_eq_latticePoints (m : Fin n → ℕ) :
    (coordinateLatticePoints m : Set (Fin n → ℝ)) =
      DiscreteMinkowski.latticePoints (realCoordinateBox m) (standardIntegerLattice n) := by
  rw [DiscreteMinkowski.latticePoints_apply]
  exact coordinateLatticePoints_coe m

/-- The closed coordinate box is convex. -/
theorem realCoordinateBox_convex (m : Fin n → ℕ) :
    Convex ℝ (realCoordinateBox m) := by
  exact convex_Icc _ _

/-- The closed coordinate box is origin-symmetric. -/
theorem realCoordinateBox_originSymmetric (m : Fin n → ℕ) :
    DiscreteMinkowski.IsOriginSymmetric (realCoordinateBox m) := by
  change -realCoordinateBox m = realCoordinateBox m
  ext x
  rw [Set.mem_neg]
  change ((fun i => -(m i : ℝ)) ≤ -x ∧ -x ≤ fun i => (m i : ℝ)) ↔
    ((fun i => -(m i : ℝ)) ≤ x ∧ x ≤ fun i => (m i : ℝ))
  constructor
  · intro hx
    constructor
    · intro i
      simpa using neg_le_neg (hx.2 i)
    · intro i
      simpa using neg_le_neg (hx.1 i)
  · intro hx
    constructor
    · intro i
      simpa using neg_le_neg (hx.2 i)
    · intro i
      simpa using neg_le_neg (hx.1 i)

/-- The central symmetral of the closed coordinate box is the box itself. -/
theorem halfDifferenceBody_realCoordinateBox (m : Fin n → ℕ) :
    DiscreteMinkowski.halfDifferenceBody (realCoordinateBox m) = realCoordinateBox m :=
  DiscreteMinkowski.halfDifferenceBody_eq_self (realCoordinateBox_convex m)
    (realCoordinateBox_originSymmetric m)

/-- The paper's successive-minimum formula specialized to the closed coordinate box. -/
theorem paper_successiveMinimum_realCoordinateBox (m : Fin n → ℕ) (i : ℕ) :
    DiscreteMinkowski.successiveMinimum (realCoordinateBox m) (standardIntegerLattice n) i =
      sInf {r : ℝ | 0 < r ∧ i ≤ Module.finrank ℝ
        (Submodule.span ℝ ((r • realCoordinateBox m) ∩
          (standardIntegerLattice n : Set (Fin n → ℝ))))} :=
  paper_successiveMinimum_of_originSymmetric (realCoordinateBox_convex m)
    (realCoordinateBox_originSymmetric m) (standardIntegerLattice n) i

/-- The real open coordinate box with integral half-side lengths `m`. -/
noncomputable def realInteriorCoordinateBox (m : Fin n → ℕ) : Set (Fin n → ℝ) :=
  {x | ∀ i, -(m i : ℝ) < x i ∧ x i < m i}

/-- A finite enumeration of the standard-lattice points in the open real coordinate box. -/
noncomputable def coordinateInteriorLatticePoints (m : Fin n → ℕ) : Finset (Fin n → ℝ) :=
  (integerInteriorBox m).map (intToRealCoordinatesEmbedding n)

/-- If every half-side length is positive, the open real coordinate box has
`∏ i, (2m_i - 1)` standard-lattice points. -/
theorem card_coordinateInteriorLatticePoints (m : Fin n → ℕ) (hm : ∀ i, 0 < m i) :
    (coordinateInteriorLatticePoints m).card = ∏ i, (2 * m i - 1) := by
  rw [coordinateInteriorLatticePoints, Finset.card_map, card_integerInteriorBox m hm]

/-- The finite open-box enumeration is exactly the standard-lattice-point set of the real open
coordinate box. -/
theorem coordinateInteriorLatticePoints_coe (m : Fin n → ℕ) :
    (coordinateInteriorLatticePoints m : Set (Fin n → ℝ)) =
      realInteriorCoordinateBox m ∩ standardIntegerLattice n := by
  ext x
  change x ∈ coordinateInteriorLatticePoints m ↔
    x ∈ realInteriorCoordinateBox m ∧ x ∈ standardIntegerLattice n
  rw [coordinateInteriorLatticePoints, Finset.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [integerInteriorBox, Fintype.mem_piFinset] at hz
    constructor
    · change ∀ i, -(m i : ℝ) < (intToRealCoordinatesEmbedding n) z i ∧
        (intToRealCoordinatesEmbedding n) z i < (m i : ℝ)
      intro i
      constructor
      · have hzi : -(m i : ℤ) < z i := (Finset.mem_Ioo.mp (hz i)).1
        have hzi' : -(m i : ℝ) < (z i : ℝ) := by exact_mod_cast hzi
        simpa [intToRealCoordinatesEmbedding, intToRealCoordinates] using hzi'
      · have hzi : z i < m i := (Finset.mem_Ioo.mp (hz i)).2
        have hzi' : (z i : ℝ) < (m i : ℝ) := by exact_mod_cast hzi
        simpa [intToRealCoordinatesEmbedding, intToRealCoordinates] using hzi'
    · exact (mem_standardIntegerLattice_iff n _).mpr ⟨z, fun i => rfl⟩
  · rintro ⟨hxbox, hxlattice⟩
    obtain ⟨z, hz⟩ := (mem_standardIntegerLattice_iff n x).mp hxlattice
    refine ⟨z, ?_, ?_⟩
    · rw [integerInteriorBox, Fintype.mem_piFinset]
      intro i
      apply Finset.mem_Ioo.mpr
      constructor
      · have hxi : -(m i : ℝ) < x i := (hxbox i).1
        rw [hz i] at hxi
        exact_mod_cast hxi
      · have hxi : x i < (m i : ℝ) := (hxbox i).2
        rw [hz i] at hxi
        exact_mod_cast hxi
    · funext i
      simpa [intToRealCoordinatesEmbedding, intToRealCoordinates] using (hz i).symm

/-- The preceding finite open-box enumeration is the dependency's standard lattice-point set. -/
theorem coordinateInteriorLatticePoints_coe_eq_latticePoints (m : Fin n → ℕ) :
    (coordinateInteriorLatticePoints m : Set (Fin n → ℝ)) =
      DiscreteMinkowski.latticePoints (realInteriorCoordinateBox m) (standardIntegerLattice n) := by
  rw [DiscreteMinkowski.latticePoints_apply]
  exact coordinateInteriorLatticePoints_coe m

end LatticeVolumeInterpolation
