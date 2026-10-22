import Unimodular
import SeparatedPlanarFamily
import Mathlib.Tactic.LinearCombination

/-!
# Aligning a common planar period line

Catalog item `bhw_lattice_conjecture_dimension_three_symmetric`.
The rank-at-most-one case of Malikiosis's planar family theorem aligns
the common period line with an integer coordinate direction.
-/

open Set Module
open scoped BigOperators Pointwise

namespace LatticeVolumeInterpolation

/-- A nonzero integer vector and its quarter-turn are independent over Z. -/
theorem linearIndependent_integerVector_quarterTurn (p : Fin 2 → ℤ) (hp : p ≠ 0) :
    LinearIndependent ℤ ![p, ![-p 1, p 0]] := by
  have hnorm : p 0 ^ 2 + p 1 ^ 2 ≠ 0 := by
    intro he
    have h0 : p 0 = 0 := by nlinarith [sq_nonneg (p 1)]
    have h1 : p 1 = 0 := by nlinarith [sq_nonneg (p 0)]
    apply hp
    ext i; fin_cases i <;> simp [h0, h1]
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h0 := congrFun hg 0
  have h1 := congrFun hg 1
  simp only [Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at h0 h1
  have hg0 : g 0 * (p 0 ^ 2 + p 1 ^ 2) = 0 := by
    linear_combination p 0 * h0 + p 1 * h1
  have hg1 : g 1 * (p 0 ^ 2 + p 1 ^ 2) = 0 := by
    linear_combination -(p 1) * h0 + p 0 * h1
  have hg0' : g 0 = 0 := (mul_eq_zero.mp hg0).resolve_right hnorm
  have hg1' : g 1 = 0 := (mul_eq_zero.mp hg1).resolve_right hnorm
  fin_cases i
  · exact hg0'
  · exact hg1'

/-- Every nonzero standard-lattice vector can be aligned horizontally by
a real realization of an integer unimodular map. No primitivity is required. -/
theorem exists_unimodular_horizontal_integer_vector
    {v : Fin 2 → ℝ} (hv : v ∈ standardIntegerLattice 2) (hv0 : v ≠ 0) :
    ∃ V : (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ),
      (∀ x, V x ∈ standardIntegerLattice 2 ↔ x ∈ standardIntegerLattice 2) ∧
      (V v) 1 = 0 := by
  obtain ⟨p, hp⟩ := (mem_standardIntegerLattice_iff_castCoords v).mp hv
  have hp0 : p ≠ 0 := by
    intro he
    apply hv0
    rw [hp, he]
    ext i
    simp [castCoords]
  obtain ⟨U, hU⟩ := exists_triangularizing 2 ![p, ![-p 1, p 0]]
    (linearIndependent_integerVector_quarterTurn p hp0)
  obtain ⟨V, hV, hVs, _⟩ := realize_unimodular U
  refine ⟨V, mem_lattice_iff_of_realize V hV hVs, ?_⟩
  rw [hp, hV]
  change (U p 1 : ℝ) = 0
  exact_mod_cast hU 0 1 (by decide)

/-- The period vectors appearing in the source's dimension split. -/
def familyPeriodVectors {ι : Type*} (K : ι → Set (Fin 2 → ℝ)) (r : ℕ) : Set (Fin 2 → ℝ) :=
  {v | ∃ i, v ∈ K i - K i ∧ ∃ z ∈ standardIntegerLattice 2, v = (r : ℝ) • z}

theorem familyPeriodVectors_subset_lattice {ι : Type*} {K : ι → Set (Fin 2 → ℝ)} {r : ℕ} :
    familyPeriodVectors K r ⊆ (standardIntegerLattice 2 : Set (Fin 2 → ℝ)) := by
  rintro v ⟨i, hdiff, z, hz, rfl⟩
  obtain ⟨p, hp⟩ := (mem_standardIntegerLattice_iff_castCoords z).mp hz
  apply (mem_standardIntegerLattice_iff_castCoords _).mpr
  refine ⟨(r : ℤ) • p, ?_⟩
  ext j
  simp [hp, castCoords, Pi.smul_apply, smul_eq_mul]

/-- If no independent pair of period vectors exists, one unimodular map
makes every period horizontal. The zero-period case needs no chosen vector. -/
theorem exists_unimodular_horizontal_family_periods
    {ι : Type*} (K : ι → Set (Fin 2 → ℝ)) (r : ℕ)
    (hno : ∀ v ∈ familyPeriodVectors K r, ∀ w ∈ familyPeriodVectors K r,
      ¬ LinearIndependent ℝ ![v, w]) :
    ∃ V : (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ),
      (∀ x, V x ∈ standardIntegerLattice 2 ↔ x ∈ standardIntegerLattice 2) ∧
      ∀ v ∈ familyPeriodVectors K r, (V v) 1 = 0 := by
  classical
  by_cases hex : ∃ v ∈ familyPeriodVectors K r, v ≠ 0
  · obtain ⟨v, hv, hv0⟩ := hex
    obtain ⟨V, hΛ, hVv⟩ := exists_unimodular_horizontal_integer_vector
      (familyPeriodVectors_subset_lattice hv) hv0
    refine ⟨V, hΛ, ?_⟩
    intro w hw
    have hmul : ∃ a : ℝ, a • v = w := by
      by_contra he
      push Not at he
      exact hno w hw v hv (linearIndependent_fin2.mpr ⟨hv0, he⟩)
    obtain ⟨a, rfl⟩ := hmul
    simp [map_smul, Pi.smul_apply, hVv]
  · refine ⟨LinearEquiv.refl ℝ _, fun _ => Iff.rfl, ?_⟩
    intro v hv
    have hv0 : v = 0 := by
      by_contra he
      exact hex ⟨v, hv, he⟩
    simp [hv0]

/-- The source's rank-at-most-one family branch. The common period line
is aligned before applying the residue-slice count; no primitive-vector
or strict-threshold assumption is added. -/
theorem planar_family_count_le_of_dependent_periods
    {ι : Type*} [Fintype ι] (K : ι → Set (Fin 2 → ℝ))
    (hc : ∀ i, IsCompact (K i)) (hv : ∀ i, Convex ℝ (K i))
    (hne : ∀ i, (K i).Nonempty) {q r : ℕ} (hr : 0 < r) (hrq : r ≤ q)
    (hfirst : ∀ i, ∀ x ∈ K i, ∀ y ∈ K i, ∀ z ∈ standardIntegerLattice 2,
      z ≠ 0 → x - y ≠ (q : ℝ) • z)
    (hcross : ∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j,
      ∀ z ∈ standardIntegerLattice 2, x - y ≠ (r : ℝ) • z)
    (hno : ∀ v ∈ familyPeriodVectors K r, ∀ w ∈ familyPeriodVectors K r,
      ¬ LinearIndependent ℝ ![v, w]) :
    (∑ i, (DiscreteMinkowski.latticePoints (K i) (standardIntegerLattice 2)).ncard) ≤ q * r := by
  obtain ⟨V, hΛ, hhorizontal⟩ := exists_unimodular_horizontal_family_periods K r hno
  have hback : ∀ z ∈ standardIntegerLattice 2, V.symm z ∈ standardIntegerLattice 2 := by
    intro z hz
    apply (hΛ (V.symm z)).mp
    simpa using hz
  have hfirstQ : ∀ i, ∀ x ∈ V '' K i, ∀ y ∈ V '' K i,
      ∀ z ∈ standardIntegerLattice 2, z ≠ 0 → x - y ≠ (q : ℝ) • z := by
    rintro i _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ z hz hz0 he
    have hzback0 : V.symm z ≠ 0 := by
      intro hh
      apply hz0
      have := congrArg V hh
      simpa using this
    apply hfirst i x hx y hy (V.symm z) (hback z hz) hzback0
    apply V.injective
    rw [map_sub, map_smul, V.apply_symm_apply]
    exact he
  have hwithinQ : ∀ i, ∀ x ∈ V '' K i, ∀ y ∈ V '' K i,
      ∀ z ∈ standardIntegerLattice 2, z 1 ≠ 0 → x - y ≠ (r : ℝ) • z := by
    rintro i _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ z hz hz1 he
    have heback : x - y = (r : ℝ) • V.symm z := by
      apply V.injective
      rw [map_sub, map_smul, V.apply_symm_apply]
      exact he
    have hperiod : x - y ∈ familyPeriodVectors K r :=
      ⟨i, ⟨x, hx, y, hy, rfl⟩, V.symm z, hback z hz, heback⟩
    have hh := hhorizontal _ hperiod
    rw [map_sub, he] at hh
    simp only [Pi.smul_apply, smul_eq_mul] at hh
    have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
    exact hz1 ((mul_eq_zero.mp hh).resolve_left hr0)
  have hcrossQ : ∀ i j, i ≠ j → ∀ x ∈ V '' K i, ∀ y ∈ V '' K j,
      ∀ z ∈ standardIntegerLattice 2, x - y ≠ (r : ℝ) • z := by
    rintro i j hij _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ z hz he
    apply hcross i j hij x hx y hy (V.symm z) (hback z hz)
    apply V.injective
    rw [map_sub, map_smul, V.apply_symm_apply]
    exact he
  have hb := planar_family_count_le_of_period_avoidance (fun i => V '' K i)
    (fun i => isCompact_image V (hc i))
    (fun i => (hv i).linear_image V.toLinearMap)
    (fun i => (hne i).image V) hr hrq hfirstQ hwithinQ hcrossQ
  simpa only [ncard_latticePoints_image V hΛ] using hb

end LatticeVolumeInterpolation
