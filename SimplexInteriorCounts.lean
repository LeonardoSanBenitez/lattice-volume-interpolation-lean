import SimplexCounts

/-! Direct stars-and-bars count for strict interior points of an integral standard simplex. -/

open scoped BigOperators

namespace LatticeVolumeInterpolation

/-- Positive integer coordinate vectors whose sum is strictly less than `m`. -/
def SimplexInteriorNatPoint (n m : ℕ) :=
  {x : Fin n → ℕ // (∀ i, 0 < x i) ∧ ∑ i, x i < m}

noncomputable instance simplexInteriorNatPointFintype (n m : ℕ) :
    Fintype (SimplexInteriorNatPoint n m) := by
  letI : Fintype (SimplexNatPoint n m) := simplexNatPointFintype n m
  exact Fintype.ofInjective (β := SimplexNatPoint n m)
    (fun x => (⟨x.1, Nat.le_of_lt x.2.2⟩ : SimplexNatPoint n m))
    (by
      intro x y hxy
      apply Subtype.ext
      exact congrArg (fun z : SimplexNatPoint n m => z.1) hxy)

/-- Subtracting one from every positive coordinate identifies strict interior points with
closed simplex points at the shifted dilation `m - (n+1)`. -/
noncomputable def simplexInteriorNatPointEquiv (n m : ℕ) (h : n + 1 ≤ m) :
    SimplexInteriorNatPoint n m ≃ SimplexNatPoint n (m - (n + 1)) where
  toFun x := ⟨fun i => x.1 i - 1, by
    have hsum : (∑ i, x.1 i) = (∑ i, (x.1 i - 1)) + n := by
      calc
        (∑ i, x.1 i) = ∑ i, ((x.1 i - 1) + 1) := by
          apply Finset.sum_congr rfl
          intro i _hi
          have hi := x.2.1 i
          omega
        _ = (∑ i, (x.1 i - 1)) + n := by simp [Finset.sum_add_distrib]
    simpa only using (show (∑ i, (x.1 i - 1)) ≤ m - (n + 1) by
      apply Nat.le_sub_of_add_le
      have hstep : (∑ i, x.1 i) + 1 ≤ m := x.2.2
      calc
        (∑ i, (x.1 i - 1)) + (n + 1) =
            ((∑ i, (x.1 i - 1)) + n) + 1 := by omega
        _ = (∑ i, x.1 i) + 1 := by rw [← hsum]
        _ ≤ m := hstep)⟩
  invFun y := ⟨fun i => y.1 i + 1, by
    constructor
    · intro i
      exact Nat.zero_lt_succ _
    · have hsum : (∑ i, (y.1 i + 1)) = (∑ i, y.1 i) + n := by
        simp [Finset.sum_add_distrib]
      have hadd : (∑ i, y.1 i) + (n + 1) ≤ m := Nat.add_le_of_le_sub h y.2
      simpa only using (show (∑ i, (y.1 i + 1)) < m by omega)⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    change (x.1 i - 1) + 1 = x.1 i
    have hi := x.2.1 i
    omega
  right_inv y := by
    apply Subtype.ext
    funext i
    change (y.1 i + 1) - 1 = y.1 i
    omega

/-- Strict interior points of `m T_n` are counted by `choose (m-1) n`, including the
small-dilation regime where both sides vanish. -/
theorem card_simplexInteriorNatPoint (n m : ℕ) (hn : 0 < n) :
    Fintype.card (SimplexInteriorNatPoint n m) = (m - 1).choose n := by
  by_cases h : n + 1 ≤ m
  · rw [Fintype.card_congr (simplexInteriorNatPointEquiv n m h), card_simplexNatPoint]
    congr 1
    omega
  · have hempty : IsEmpty (SimplexInteriorNatPoint n m) :=
      ⟨fun x => by
        have hsum : n ≤ ∑ i, x.1 i := by
          calc
            n = ∑ _i : Fin n, 1 := by simp
            _ ≤ ∑ i, x.1 i := Finset.sum_le_sum fun i _ => by
              have hi := x.2.1 i
              omega
        have hnm : n < m := lt_of_le_of_lt hsum x.2.2
        exact h (by omega)⟩
    letI := hempty
    rw [Fintype.card_eq_zero]
    exact (Nat.choose_eq_zero_of_lt (by omega)).symm

end LatticeVolumeInterpolation
