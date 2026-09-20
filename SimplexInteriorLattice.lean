import SimplexInteriorCounts
import SimplexLattice

/-! Real-coordinate and standard-lattice bridge for strict interiors of integral simplices. -/

open scoped BigOperators

namespace LatticeVolumeInterpolation

/-- The strict interior of the integer dilate `m T_n`, in coordinate-inequality form. -/
def realInteriorDilatedStandardSimplex (n m : ℕ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 < x i) ∧ ∑ i, x i < m}

def simplexInteriorNatPointToReal {n m : ℕ} (x : SimplexInteriorNatPoint n m) :
    Fin n → ℝ := fun i => x.1 i

theorem simplexInteriorNatPointToReal_injective {n m : ℕ} :
    Function.Injective
      (simplexInteriorNatPointToReal : SimplexInteriorNatPoint n m → Fin n → ℝ) := by
  intro x y hxy
  apply Subtype.ext
  funext i
  have hi := congrFun hxy i
  change (x.1 i : ℝ) = (y.1 i : ℝ) at hi
  exact_mod_cast hi

noncomputable def simplexInteriorNatPointToRealEmbedding (n m : ℕ) :
    SimplexInteriorNatPoint n m ↪ (Fin n → ℝ) :=
  ⟨simplexInteriorNatPointToReal, simplexInteriorNatPointToReal_injective⟩

noncomputable def simplexInteriorCoordinateLatticePoints (n m : ℕ) :
    Finset (Fin n → ℝ) :=
  Finset.univ.map (simplexInteriorNatPointToRealEmbedding n m)

theorem card_simplexInteriorCoordinateLatticePoints (n m : ℕ) (hn : 0 < n) :
    (simplexInteriorCoordinateLatticePoints n m).card = (m - 1).choose n := by
  rw [simplexInteriorCoordinateLatticePoints, Finset.card_map, Finset.card_univ,
    card_simplexInteriorNatPoint n m hn]

/-- The positive stars-and-bars enumeration is exactly the standard-lattice intersection
with the strict interior of `m T_n`. -/
theorem simplexInteriorCoordinateLatticePoints_coe (n m : ℕ) :
    (simplexInteriorCoordinateLatticePoints n m : Set (Fin n → ℝ)) =
      realInteriorDilatedStandardSimplex n m ∩ standardIntegerLattice n := by
  ext x
  change x ∈ simplexInteriorCoordinateLatticePoints n m ↔
    x ∈ realInteriorDilatedStandardSimplex n m ∩ standardIntegerLattice n
  rw [simplexInteriorCoordinateLatticePoints, Finset.mem_map]
  constructor
  · rintro ⟨q, -, rfl⟩
    constructor
    · constructor
      · intro i
        change (0 : ℝ) < (q.1 i : ℝ)
        exact_mod_cast q.2.1 i
      · change (∑ i, (q.1 i : ℝ)) < (m : ℝ)
        exact_mod_cast q.2.2
    · exact (mem_standardIntegerLattice_iff n _).mpr ⟨fun i => q.1 i, fun i => rfl⟩
  · rintro ⟨hx, hxlattice⟩
    obtain ⟨z, hz⟩ := (mem_standardIntegerLattice_iff n x).mp hxlattice
    have hzpos : ∀ i, 0 < z i := by
      intro i
      have hxi : 0 < x i := hx.1 i
      rw [hz i] at hxi
      exact_mod_cast hxi
    let q : Fin n → ℕ := fun i => (z i).toNat
    have hqcast : ∀ i, (q i : ℝ) = x i := by
      intro i
      rw [hz i]
      have hzi : ((z i).toNat : ℤ) = z i := Int.toNat_of_nonneg (le_of_lt (hzpos i))
      change (((z i).toNat : ℕ) : ℝ) = ((z i : ℤ) : ℝ)
      exact_mod_cast hzi
    have hqpos : ∀ i, 0 < q i := by
      intro i
      change 0 < (z i).toNat
      have hzi : ((z i).toNat : ℤ) = z i := Int.toNat_of_nonneg (le_of_lt (hzpos i))
      have hziPos : (0 : ℤ) < ((z i).toNat : ℤ) := by simpa [hzi] using hzpos i
      exact_mod_cast hziPos
    have hqsum : ∑ i, q i < m := by
      exact_mod_cast (show (∑ i, (q i : ℝ)) < (m : ℝ) by simpa [hqcast] using hx.2)
    refine ⟨⟨q, hqpos, hqsum⟩, Finset.mem_univ _, ?_⟩
    funext i
    exact hqcast i

theorem simplexInteriorCoordinateLatticePoints_coe_eq_latticePoints (n m : ℕ) :
    (simplexInteriorCoordinateLatticePoints n m : Set (Fin n → ℝ)) =
      DiscreteMinkowski.latticePoints (realInteriorDilatedStandardSimplex n m)
        (standardIntegerLattice n) := by
  rw [DiscreteMinkowski.latticePoints_apply]
  exact simplexInteriorCoordinateLatticePoints_coe n m

end LatticeVolumeInterpolation
