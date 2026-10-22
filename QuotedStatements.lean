import PaperConjectures
import ProjectedDeterminantBound

/-!
# Contextual statements quoted in the introduction

The project's catalog excludes proofs of these three contextual results.
Their propositions are recorded here without axioms asserting them. This
distinction does not apply to the separately proved dimensional subcases.
-/

open Set MeasureTheory Module
open scoped BigOperators Pointwise ENNReal

namespace LatticeVolumeInterpolation

noncomputable section

/-- Literal target-paper Eq. (1.2), including its printed lower factor `1`.
This definition does not assert the statement or its sharpness. -/
def BHWTwosidedContextStatement (n : ℕ) : Prop :=
  ∀ K : Set (Fin n → ℝ), IsConvexBody K → DiscreteMinkowski.IsOriginSymmetric K →
    (((DiscreteMinkowski.latticePoints K (standardIntegerLattice n)).ncard : ℝ) ≤
      ∏ i : Fin n, (2 * (i.1 + 1 : ℝ) /
        DiscreteMinkowski.successiveMinimum K (standardIntegerLattice n) (i.1 + 1) + 1)) ∧
    (DiscreteMinkowski.successiveMinimum K (standardIntegerLattice n) n ≤ 2 →
      (n.factorial : ℝ)⁻¹ * ∏ i : Fin n,
        (1 / DiscreteMinkowski.successiveMinimum K (standardIntegerLattice n) (i.1 + 1) - 1) ≤
        ((DiscreteMinkowski.latticePoints K (standardIntegerLattice n)).ncard : ℝ))

/-- The stronger lower factors in the cited Betke--Henk--Wills corollary.
It is separate from the target paper's printed formula. -/
def BHWSourceLowerContextStatement (n : ℕ) : Prop :=
  ∀ K : Set (Fin n → ℝ), IsConvexBody K → DiscreteMinkowski.IsOriginSymmetric K →
    DiscreteMinkowski.successiveMinimum K (standardIntegerLattice n) n ≤ 2 →
      (n.factorial : ℝ)⁻¹ * ∏ i : Fin n,
        (2 / DiscreteMinkowski.successiveMinimum K (standardIntegerLattice n) (i.1 + 1) - 1) ≤
        ((DiscreteMinkowski.latticePoints K (standardIntegerLattice n)).ncard : ℝ)

def malikiosisConstant (n : ℕ) : ℝ := (4 / Real.exp 1) * Real.sqrt 3 ^ (n - 1)

/-- The floor-free Eq. (1.3), recorded as a contextual proposition. -/
def MalikiosisContextStatement (n : ℕ) : Prop :=
  0 < n → ∀ K : Set (Fin n → ℝ), IsConvexBody K →
    ((DiscreteMinkowski.latticePoints K (standardIntegerLattice n)).ncard : ℝ) ≤
      malikiosisConstant n * ∏ i : Fin n,
        (2 / DiscreteMinkowski.successiveMinimum K (standardIntegerLattice n) (i.1 + 1) + 1)

/-- The primary source's stronger integer-part statement, kept distinct. -/
def MalikiosisFloorContextStatement (n : ℕ) : Prop :=
  0 < n → ∀ K : Set (Fin n → ℝ), IsConvexBody K →
    ((DiscreteMinkowski.latticePoints K (standardIntegerLattice n)).ncard : ℝ) ≤
      malikiosisConstant n * ∏ i : Fin n,
        (⌊2 / DiscreteMinkowski.successiveMinimum K (standardIntegerLattice n) (i.1 + 1) + 1⌋₊ : ℝ)

/-- Dropping the integer parts gives the target's contextual statement.
The source theorem is an explicit premise here, rather than an axiom. -/
theorem malikiosis_floor_context_implies_context {n : ℕ}
    (hsource : MalikiosisFloorContextStatement n) : MalikiosisContextStatement n := by
  intro hn K hK
  apply (hsource hn K hK).trans
  apply mul_le_mul_of_nonneg_left
  · apply Finset.prod_le_prod
    · intro i _; positivity
    · intro i _
      have hp := DiscreteMinkowski.successiveMinimum_pos
        (Λ := standardIntegerLattice n) ((isConvexBody_iff K).mp hK).2
        (by omega : 0 < i.1 + 1) (by rw [Module.finrank_fin_fun]; exact i.2)
      exact Nat.floor_le (by positivity)
  · unfold malikiosisConstant
    positivity

def schymuraDirection {n : ℕ} (b : Fin n → (Fin n → ℝ)) (I : Finset (Fin n)) :
    Submodule ℝ (Fin n → ℝ) := Submodule.span ℝ (b '' (I : Set (Fin n)))

/-- The zonotope is measured intrinsically in its own spanned subspace. -/
def schymuraZonotope {n : ℕ} (b : Fin n → (Fin n → ℝ)) (I : Finset (Fin n)) :
    Set ((schymuraDirection b I).map (toEucl n).toLinearMap) :=
  {x | ∃ t : I → ℝ, (∀ i, t i ∈ Icc (0 : ℝ) 1) ∧
    (x : EuclideanSpace ℝ (Fin n)) = ∑ i : I, t i • toEucl n (b i.1)}

/-- Henze's Lemma 1.1, cited as Schymura by Freyer--Lucas. The sum includes
the empty subset, whose term is the full ambient volume. -/
def SchymuraContextStatement (n : ℕ) : Prop :=
  ∀ K : Set (Fin n → ℝ), IsConvexBody K →
    ∀ b : Fin n → (Fin n → ℝ), LinearIndependent ℝ b →
      (∀ i, b i ∈ standardIntegerLattice n) →
      ((DiscreteMinkowski.latticePoints K (standardIntegerLattice n)).ncard : ℝ≥0∞) ≤
        ∑ I : Finset (Fin n),
          volume (projMap (schymuraDirection b I) '' K) * volume (schymuraZonotope b I)

end
end LatticeVolumeInterpolation
