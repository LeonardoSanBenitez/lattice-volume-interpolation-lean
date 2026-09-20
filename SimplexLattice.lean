import SimplexCounts
import CoordinateLattice

/-! Real-coordinate and standard-lattice bridge for the simplex stars-and-bars count. -/

open scoped BigOperators

namespace LatticeVolumeInterpolation

/-- The integer dilate `m T_n` in coordinate-inequality form. -/
def realDilatedStandardSimplex (n m : ℕ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ m}

def simplexNatPointToReal {n m : ℕ} (x : SimplexNatPoint n m) : Fin n → ℝ :=
  fun i => x.1 i

theorem simplexNatPointToReal_injective {n m : ℕ} :
    Function.Injective (simplexNatPointToReal : SimplexNatPoint n m → Fin n → ℝ) := by
  intro x y hxy
  apply Subtype.ext
  funext i
  have hi := congrFun hxy i
  change (x.1 i : ℝ) = (y.1 i : ℝ) at hi
  exact_mod_cast hi

noncomputable def simplexNatPointToRealEmbedding (n m : ℕ) :
    SimplexNatPoint n m ↪ (Fin n → ℝ) :=
  ⟨simplexNatPointToReal, simplexNatPointToReal_injective⟩

/-- Finite enumeration of the standard-lattice points of `m T_n`. -/
noncomputable def simplexCoordinateLatticePoints (n m : ℕ) : Finset (Fin n → ℝ) :=
  Finset.univ.map (simplexNatPointToRealEmbedding n m)

theorem card_simplexCoordinateLatticePoints (n m : ℕ) :
    (simplexCoordinateLatticePoints n m).card = (m + n).choose n := by
  rw [simplexCoordinateLatticePoints, Finset.card_map, Finset.card_univ,
    card_simplexNatPoint]

/-- The stars-and-bars enumeration is exactly the standard-lattice intersection with `m T_n`. -/
theorem simplexCoordinateLatticePoints_coe (n m : ℕ) :
    (simplexCoordinateLatticePoints n m : Set (Fin n → ℝ)) =
      realDilatedStandardSimplex n m ∩ standardIntegerLattice n := by
  ext x
  change x ∈ simplexCoordinateLatticePoints n m ↔
    x ∈ realDilatedStandardSimplex n m ∩ standardIntegerLattice n
  rw [simplexCoordinateLatticePoints, Finset.mem_map]
  constructor
  · rintro ⟨q, -, rfl⟩
    constructor
    · constructor
      · intro i
        change (0 : ℝ) ≤ (q.1 i : ℝ)
        positivity
      · change (∑ i, (q.1 i : ℝ)) ≤ (m : ℝ)
        exact_mod_cast q.2
    · exact (mem_standardIntegerLattice_iff n _).mpr ⟨fun i => q.1 i, fun i => rfl⟩
  · rintro ⟨hx, hxlattice⟩
    obtain ⟨z, hz⟩ := (mem_standardIntegerLattice_iff n x).mp hxlattice
    have hznonneg : ∀ i, 0 ≤ z i := by
      intro i
      have hxi : 0 ≤ x i := hx.1 i
      rw [hz i] at hxi
      exact_mod_cast hxi
    let q : Fin n → ℕ := fun i => (z i).toNat
    have hqcast : ∀ i, (q i : ℝ) = x i := by
      intro i
      rw [hz i]
      have hzi : ((z i).toNat : ℤ) = z i := Int.toNat_of_nonneg (hznonneg i)
      change (((z i).toNat : ℕ) : ℝ) = ((z i : ℤ) : ℝ)
      exact_mod_cast hzi
    have hqsum : ∑ i, q i ≤ m := by
      exact_mod_cast (show (∑ i, (q i : ℝ)) ≤ (m : ℝ) by simpa [hqcast] using hx.2)
    refine ⟨⟨q, hqsum⟩, Finset.mem_univ _, ?_⟩
    funext i
    exact hqcast i

theorem simplexCoordinateLatticePoints_coe_eq_latticePoints (n m : ℕ) :
    (simplexCoordinateLatticePoints n m : Set (Fin n → ℝ)) =
      DiscreteMinkowski.latticePoints (realDilatedStandardSimplex n m)
        (standardIntegerLattice n) := by
  rw [DiscreteMinkowski.latticePoints_apply]
  exact simplexCoordinateLatticePoints_coe n m

end LatticeVolumeInterpolation
