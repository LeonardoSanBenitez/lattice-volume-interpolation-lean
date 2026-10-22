import PlanarRankTwo

/-!
# Counting a pivot body and repaired singleton points

Catalog item `bhw_lattice_conjecture_dimension_three_symmetric`.
After the source's finite-coset repair, the nonpivot lattice points become
a separated finite family of singleton convex sets. The checked row-family
bound then counts them together with the pivot body.
-/

open Set
open scoped BigOperators Pointwise

namespace LatticeVolumeInterpolation

theorem latticePoints_singleton_ncard_of_mem {x : Fin 2 → ℝ}
    (hx : x ∈ standardIntegerLattice 2) :
    (DiscreteMinkowski.latticePoints {x} (standardIntegerLattice 2)).ncard = 1 := by
  simp [DiscreteMinkowski.latticePoints_apply, hx]

/-- The final counting step of the source's rank-two branch, in the pivot
body's original adapted coordinates. No small-period coset premise remains. -/
theorem repaired_pivot_count_le
    {K : Set (Fin 2 → ℝ)} (hc : IsCompact K) (hv : Convex ℝ K) (hne : K.Nonempty)
    {T : Finset (Fin 2 → ℝ)} (hTL : ∀ y ∈ T, y ∈ standardIntegerLattice 2)
    {q r : ℕ} (hr : 0 < r) (hrq : r ≤ q)
    (hfirst : ∀ x ∈ K, ∀ y ∈ K, ∀ z ∈ standardIntegerLattice 2,
      z ≠ 0 → x - y ≠ (q : ℝ) • z)
    (hwithin : ∀ x ∈ K, ∀ y ∈ K, ∀ z ∈ standardIntegerLattice 2,
      z 1 ≠ 0 → x - y ≠ (r : ℝ) • z)
    (havoid : ∀ y ∈ T, ∀ z ∈ standardIntegerLattice 2, y + (r : ℝ) • z ∉ K)
    (hsep : ∀ x ∈ T, ∀ y ∈ T, ∀ z ∈ standardIntegerLattice 2,
      x - y = (r : ℝ) • z → x = y) :
    (DiscreteMinkowski.latticePoints K (standardIntegerLattice 2)).ncard + T.card ≤ q * r := by
  classical
  let F : Option T → Set (Fin 2 → ℝ) := fun i => match i with
    | none => K
    | some t => {t.1}
  have hFc : ∀ i, IsCompact (F i) := by
    intro i
    cases i with
    | none => exact hc
    | some t => exact isCompact_singleton
  have hFv : ∀ i, Convex ℝ (F i) := by
    intro i
    cases i with
    | none => exact hv
    | some t => exact convex_singleton _
  have hFne : ∀ i, (F i).Nonempty := by
    intro i
    cases i with
    | none => exact hne
    | some t => exact ⟨t.1, rfl⟩
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le hr hrq))
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hFfirst : ∀ i, ∀ x ∈ F i, ∀ y ∈ F i, ∀ z ∈ standardIntegerLattice 2,
      z ≠ 0 → x - y ≠ (q : ℝ) • z := by
    intro i
    cases i with
    | none => exact hfirst
    | some t =>
      intro x hx y hy z hz hz0 he
      change x = t.1 at hx
      change y = t.1 at hy
      subst x; subst y
      have hm : (q : ℝ) • z = 0 := by simpa only [sub_self] using he.symm
      exact hz0 ((smul_eq_zero.mp hm).resolve_left hq0)
  have hFwithin : ∀ i, ∀ x ∈ F i, ∀ y ∈ F i, ∀ z ∈ standardIntegerLattice 2,
      z 1 ≠ 0 → x - y ≠ (r : ℝ) • z := by
    intro i
    cases i with
    | none => exact hwithin
    | some t =>
      intro x hx y hy z hz hz1 he
      change x = t.1 at hx
      change y = t.1 at hy
      subst x; subst y
      have hm : (r : ℝ) • z = 0 := by simpa only [sub_self] using he.symm
      have hz0 : z = 0 := (smul_eq_zero.mp hm).resolve_left hr0
      exact hz1 (by simp [hz0])
  have hFcross : ∀ i j, i ≠ j → ∀ x ∈ F i, ∀ y ∈ F j,
      ∀ z ∈ standardIntegerLattice 2, x - y ≠ (r : ℝ) • z := by
    intro i j hij
    cases i with
    | none =>
      cases j with
      | none => exact False.elim (hij rfl)
      | some t =>
        intro x hx y hy z hz he
        change y = t.1 at hy
        subst y
        apply havoid t.1 t.2 z hz
        convert hx using 1
        ext l
        have hl := congrFun he l
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hl
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        linarith
    | some s =>
      cases j with
      | none =>
        intro x hx y hy z hz he
        change x = s.1 at hx
        subst x
        apply havoid s.1 s.2 (-z) ((standardIntegerLattice 2).neg_mem hz)
        convert hy using 1
        ext l
        have hl := congrFun he l
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hl
        simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, mul_neg]
        linarith
      | some t =>
        intro x hx y hy z hz he
        change x = s.1 at hx
        change y = t.1 at hy
        subst x; subst y
        exact hij (congrArg Option.some (Subtype.ext (hsep s.1 s.2 t.1 t.2 z hz he)))
  have hb := planar_family_count_le_of_period_avoidance F hFc hFv hFne hr hrq
    hFfirst hFwithin hFcross
  have hpoint : ∀ t : T,
      (DiscreteMinkowski.latticePoints (F (some t)) (standardIntegerLattice 2)).ncard = 1 :=
    fun t => latticePoints_singleton_ncard_of_mem (hTL t.1 t.2)
  rw [Fintype.sum_option] at hb
  simp_rw [hpoint] at hb
  simpa only [F, Finset.sum_const, Finset.card_univ, Fintype.card_coe, smul_eq_mul, mul_one] using hb

/-- The repaired rank-two branch, preserving the source's non-strict order
of periods. Equal periods use the identity repair rather than an extra premise. -/
theorem planar_family_count_le_of_rank_two_periods
    {ι : Type*} [Fintype ι] (K : ι → Set (Fin 2 → ℝ))
    (hc : ∀ i, IsCompact (K i)) (hv : ∀ i, Convex ℝ (K i))
    (hne : ∀ i, (K i).Nonempty) {q₁ q₂ q₃ : ℕ}
    (hq₃ : 0 < q₃) (hq₃₂ : q₃ ≤ q₂) (hq₂₁ : q₂ ≤ q₁)
    (hfirst : ∀ i, ∀ x ∈ K i, ∀ y ∈ K i, ∀ z ∈ standardIntegerLattice 2,
      z ≠ 0 → x - y ≠ (q₁ : ℝ) • z)
    (hwithin : ∀ i, ∀ x ∈ K i, ∀ y ∈ K i, ∀ z ∈ standardIntegerLattice 2,
      z 1 ≠ 0 → x - y ≠ (q₂ : ℝ) • z)
    (hcross : ∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j,
      ∀ z ∈ standardIntegerLattice 2, x - y ≠ (q₃ : ℝ) • z)
    {i₀ : ι} {v w : Fin 2 → ℝ} (hvD : v ∈ K i₀ - K i₀) (hwD : w ∈ K i₀ - K i₀)
    (hvΛ : v ∈ scaledStandardLattice q₃) (hwΛ : w ∈ scaledStandardLattice q₃)
    (hind : LinearIndependent ℝ ![v, w]) :
    (∑ i, (DiscreteMinkowski.latticePoints (K i) (standardIntegerLattice 2)).ncard) ≤ q₁ * q₂ := by
  classical
  let S := otherBodiesLatticeFinset K hc i₀
  have hSΛ := otherBodiesLatticeFinset_subset_lattice K hc i₀
  have hother := other_body_scaled_period_separated K hv hcross hvD hwD hvΛ hwΛ hind
  have hSsep := otherBodiesLatticeFinset_period_separated K hc i₀ hcross hother
  have hSfree := pivot_disjoint_otherBodies_coset_union K hc i₀ hcross
  have hexT : ∃ T : Finset (Fin 2 → ℝ), T.card = S.card ∧
      (∀ y ∈ T, y ∈ standardIntegerLattice 2) ∧
      (∀ y ∈ T, ∀ z ∈ standardIntegerLattice 2, y + (q₂ : ℝ) • z ∉ K i₀) ∧
      (∀ x ∈ T, ∀ y ∈ T, ∀ z ∈ standardIntegerLattice 2,
        x - y = (q₂ : ℝ) • z → x = y) := by
    rcases lt_or_eq_of_le hq₃₂ with hlt | heq
    · obtain ⟨T, hcard, hTL, hfwd, hrev, havoid, hsep⟩ :=
        exists_finite_coset_translate hq₃ hlt S (hv i₀) (hc i₀).isBounded (hne i₀)
          hSΛ hSfree hSsep
      exact ⟨T, hcard, hTL, havoid, hsep⟩
    · subst q₂
      refine ⟨S, rfl, hSΛ, ?_, hSsep⟩
      intro y hy z hz hx
      exact (Set.disjoint_left.mp hSfree) hx ⟨y, hy, z, hz, rfl⟩
  obtain ⟨T, hcardT, hTL, havoid, hsep⟩ := hexT
  have hb := repaired_pivot_count_le (hc i₀) (hv i₀) (hne i₀) hTL
    (lt_of_lt_of_le hq₃ hq₃₂) hq₂₁ (hfirst i₀) (hwithin i₀) havoid hsep
  have hdis : ∀ i j, i ≠ j → Disjoint (K i) (K j) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    exact hcross i j hij x hxi x hxj 0 (standardIntegerLattice 2).zero_mem (by simp)
  calc
    _ = (DiscreteMinkowski.latticePoints (K i₀) (standardIntegerLattice 2)).ncard + S.card :=
      (otherBodiesLatticeFinset_card K hc i₀ hdis).symm
    _ = (DiscreteMinkowski.latticePoints (K i₀) (standardIntegerLattice 2)).ncard + T.card := by
      rw [hcardT]
    _ ≤ q₁ * q₂ := hb

/-- Malikiosis's planar separated-family theorem (Conjecture 3.2.1 in
dimension two). This is the induction input for the three-dimensional bound. -/
theorem planar_separated_family_count_bound
    {ι : Type*} [Fintype ι] (K : ι → Set (Fin 2 → ℝ))
    (hc : ∀ i, IsCompact (K i)) (hv : ∀ i, Convex ℝ (K i))
    (hne : ∀ i, (K i).Nonempty) {q₁ q₂ q₃ : ℕ}
    (hq₃ : 0 < q₃) (hq₃₂ : q₃ ≤ q₂) (hq₂₁ : q₂ ≤ q₁)
    (hfirst : ∀ i, ∀ x ∈ K i, ∀ y ∈ K i, ∀ z ∈ standardIntegerLattice 2,
      z ≠ 0 → x - y ≠ (q₁ : ℝ) • z)
    (hwithin : ∀ i, ∀ x ∈ K i, ∀ y ∈ K i, ∀ z ∈ standardIntegerLattice 2,
      z 1 ≠ 0 → x - y ≠ (q₂ : ℝ) • z)
    (hcross : ∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j,
      ∀ z ∈ standardIntegerLattice 2, x - y ≠ (q₃ : ℝ) • z) :
    (∑ i, (DiscreteMinkowski.latticePoints (K i) (standardIntegerLattice 2)).ncard) ≤ q₁ * q₂ := by
  classical
  by_cases hno : ∀ v ∈ familyPeriodVectors K q₃, ∀ w ∈ familyPeriodVectors K q₃,
      ¬ LinearIndependent ℝ ![v, w]
  · have hb := planar_family_count_le_of_dependent_periods K hc hv hne hq₃
      (hq₃₂.trans hq₂₁) hfirst hcross hno
    exact hb.trans (Nat.mul_le_mul_left q₁ hq₃₂)
  · push Not at hno
    obtain ⟨v, hvP, w, hwP, hind⟩ := hno
    obtain ⟨i, hvD, zv, hzv, hveq⟩ := hvP
    obtain ⟨j, hwD, zw, hzw, hweq⟩ := hwP
    have hvΛ : v ∈ scaledStandardLattice q₃ := mem_scaledStandardLattice.mpr ⟨zv, hzv, hveq⟩
    have hwΛ : w ∈ scaledStandardLattice q₃ := mem_scaledStandardLattice.mpr ⟨zw, hzw, hweq⟩
    have hij := independent_family_periods_same_index K hv hcross hvD hwD hvΛ hwΛ hind
    subst j
    exact planar_family_count_le_of_rank_two_periods K hc hv hne hq₃ hq₃₂ hq₂₁
      hfirst hwithin hcross hvD hwD hvΛ hwΛ hind

end LatticeVolumeInterpolation
