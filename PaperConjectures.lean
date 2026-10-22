import PaperNotation

/-!
# The two open Betke--Henk--Wills conjectures

Catalog items `bhw_lattice_point_conjecture` (Conjecture 1) and
`bhw_ratio_conjecture` (Conjecture 2, Eqs. (1.5)--(1.7)).

These declarations define propositions. They neither prove the conjectures
nor introduce axioms asserting them. Indices `i : Fin n` represent the
paper's indices `i + 1` in `[n]`.
-/

open Set MeasureTheory
open scoped BigOperators

namespace LatticeVolumeInterpolation

noncomputable section

/-- Conjecture 1, in every body of the fixed dimension. -/
def BHWLatticePointConjecture (n : ℕ) : Prop :=
  ∀ K : Set (Fin n → ℝ), IsConvexBody K →
    (DiscreteMinkowski.latticePoints K (standardIntegerLattice n)).ncard ≤
      ∏ i : Fin n,
        ⌊2 / DiscreteMinkowski.successiveMinimum K (standardIntegerLattice n) (i.1 + 1) + 1⌋₊

/-- Conjecture 2, Eq. (1.5). -/
def BHWRatioUpperConjecture (n : ℕ) : Prop :=
  ∀ K : Set (Fin n → ℝ), IsConvexBody K →
    ((DiscreteMinkowski.latticePoints K (standardIntegerLattice n)).ncard : ℝ) ≤
      (volume K).toReal * ∏ i : Fin n,
        (1 + (i.1 + 1 : ℝ) *
          DiscreteMinkowski.successiveMinimum K (standardIntegerLattice n) (i.1 + 1) / 2)

/-- Conjecture 2, Eq. (1.6), including its smallness regime and interior count. -/
def BHWRatioLowerConjecture (n : ℕ) : Prop :=
  ∀ K : Set (Fin n → ℝ), IsConvexBody K →
    DiscreteMinkowski.successiveMinimum K (standardIntegerLattice n) n ≤ 2 / (n : ℝ) →
      (volume K).toReal * ∏ i : Fin n,
        (1 - (i.1 + 1 : ℝ) *
          DiscreteMinkowski.successiveMinimum K (standardIntegerLattice n) (i.1 + 1) / 2) ≤
      ((DiscreteMinkowski.latticePoints (interior K) (standardIntegerLattice n)).ncard : ℝ)

/-- Conjecture 2, Eq. (1.7), including symmetry and its smallness regime. -/
def BHWSymmetricRatioLowerConjecture (n : ℕ) : Prop :=
  ∀ K : Set (Fin n → ℝ), IsConvexBody K → DiscreteMinkowski.IsOriginSymmetric K →
    DiscreteMinkowski.successiveMinimum K (standardIntegerLattice n) n ≤ 2 →
      (volume K).toReal * ∏ i : Fin n,
        (1 - DiscreteMinkowski.successiveMinimum K (standardIntegerLattice n) (i.1 + 1) / 2) ≤
      ((DiscreteMinkowski.latticePoints (interior K) (standardIntegerLattice n)).ncard : ℝ)

/-- All three claims of Conjecture 2; no claim is assumed by this definition. -/
def BHWRatioConjecture (n : ℕ) : Prop :=
  BHWRatioUpperConjecture n ∧ BHWRatioLowerConjecture n ∧ BHWSymmetricRatioLowerConjecture n

end
end LatticeVolumeInterpolation
