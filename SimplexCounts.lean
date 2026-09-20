import LviBasic
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Sym.Card

/-!
Narrow stars-and-bars infrastructure for the standard-simplex equality case in
Freyer--Lucas, *Interpolating between volume and lattice point enumerator with successive
minima*.

Catalog item: `simplex_equality_cases`.

The paper invokes the Ehrhart polynomial of the standard simplex.  We instead identify its
integer points directly with weak compositions: the final coordinate is the unused slack.
-/

open scoped BigOperators

namespace LatticeVolumeInterpolation

/-- Nonnegative integer coordinate vectors whose sum is at most `m`. -/
def SimplexNatPoint (n m : ℕ) := {x : Fin n → ℕ // ∑ i, x i ≤ m}

/-- Adding the slack coordinate turns a bounded weak composition into an exact weak
composition on `n+1` coordinates. -/
noncomputable def simplexNatPointEquivExactSum (n m : ℕ) :
    SimplexNatPoint n m ≃ {p : Fin (n + 1) → ℕ // ∑ i, p i = m} where
  toFun x := ⟨Fin.snoc x.1 (m - ∑ i, x.1 i), by
    rw [Fin.sum_univ_castSucc]
    simp [Nat.add_sub_of_le x.2]⟩
  invFun p := ⟨fun i => p.1 i.castSucc, by
    have hp := p.2
    rw [Fin.sum_univ_castSucc] at hp
    have hle : (∑ i : Fin n, p.1 i.castSucc) ≤ m := Nat.le.intro hp
    exact hle⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    change @Fin.snoc n (fun _ => ℕ) x.1 (m - ∑ j, x.1 j) i.castSucc = x.1 i
    simp
  right_inv p := by
    apply Subtype.ext
    have hp := p.2
    rw [Fin.sum_univ_castSucc] at hp
    have hslack : m - (∑ i : Fin n, p.1 i.castSucc) = p.1 (Fin.last n) := by omega
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa [Fin.snoc_last] using hslack
    · change @Fin.snoc n (fun _ => ℕ) (fun k => p.1 k.castSucc)
        (m - ∑ k : Fin n, p.1 k.castSucc) i.castSucc = p.1 i.castSucc
      simp

/-- The preceding slack-coordinate equivalence followed by Mathlib's stars-and-bars
equivalence with multisets. -/
noncomputable def simplexNatPointEquivSym (n m : ℕ) :
    SimplexNatPoint n m ≃ Sym (Fin (n + 1)) m :=
  (simplexNatPointEquivExactSum n m).trans (Sym.equivNatSumOfFintype (Fin (n + 1)) m).symm

noncomputable instance simplexNatPointFintype (n m : ℕ) : Fintype (SimplexNatPoint n m) :=
  Fintype.ofEquiv (Sym (Fin (n + 1)) m) (simplexNatPointEquivSym n m).symm

/-- Direct stars-and-bars count for the closed integer points of `m T_n`. -/
theorem card_simplexNatPoint (n m : ℕ) :
    Fintype.card (SimplexNatPoint n m) = (m + n).choose n := by
  rw [Fintype.card_congr (simplexNatPointEquivSym n m), Sym.card_sym_eq_choose]
  simpa [Nat.add_comm] using (Nat.choose_symm_add (a := n) (b := m)).symm

end LatticeVolumeInterpolation
