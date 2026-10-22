import LatticePeriodLines
import PlanarPeriodAlignment
import LatticeCosetTranslate

/-!
# Rank-two period geometry for the planar family theorem

Catalog item `bhw_lattice_conjecture_dimension_three_symmetric`.
Independent period segments must belong to the same body. Every other body
then has no nonzero scaled-lattice period, by the checked periodic-line
collision theorem. This is the input to the finite-coset repair.
-/

open Set Module
open scoped BigOperators Pointwise

namespace LatticeVolumeInterpolation

/-- The scaled standard lattice as an actual integer submodule. -/
noncomputable def scaledStandardLattice (r : ℕ) : Submodule ℤ (Fin 2 → ℝ) :=
  (standardIntegerLattice 2).map ((r : ℝ) •
    (LinearMap.id : (Fin 2 → ℝ) →ₗ[ℤ] (Fin 2 → ℝ)))

theorem mem_scaledStandardLattice {r : ℕ} {v : Fin 2 → ℝ} :
    v ∈ scaledStandardLattice r ↔ ∃ z ∈ standardIntegerLattice 2, v = (r : ℝ) • z := by
  rw [scaledStandardLattice, Submodule.mem_map]
  simp only [LinearMap.smul_apply, LinearMap.id_apply]
  constructor <;> rintro ⟨z, hz, he⟩ <;> exact ⟨z, hz, he.symm⟩

/-- Source cross separation is disjointness of the scaled-period saturations. -/
theorem latticeSaturations_disjoint_of_cross_periods
    {K H : Set (Fin 2 → ℝ)} {r : ℕ}
    (hcross : ∀ x ∈ K, ∀ y ∈ H, ∀ z ∈ standardIntegerLattice 2,
      x - y ≠ (r : ℝ) • z) :
    Disjoint (latticeSaturation K (scaledStandardLattice r))
      (latticeSaturation H (scaledStandardLattice r)) := by
  apply latticeSaturations_disjoint_iff_difference_avoids.mpr
  intro x hx y hy hmem
  obtain ⟨z, hz, he⟩ := mem_scaledStandardLattice.mp hmem
  exact hcross x hx y hy z hz he

theorem exists_period_segment_of_mem_difference
    {K : Set (Fin 2 → ℝ)} {v : Fin 2 → ℝ} (hv : v ∈ K - K) :
    ∃ a ∈ K, a + v ∈ K := by
  obtain ⟨x, hx, y, hy, he⟩ := hv
  refine ⟨y, hy, ?_⟩
  convert hx using 1
  ext i
  have hi := congrFun he i
  simp only [Pi.sub_apply] at hi
  simp only [Pi.add_apply]
  linarith

/-- Independent period vectors in a separated planar family have the same
body index. This is the source's initial rank-two collision step. -/
theorem independent_family_periods_same_index
    {ι : Type*} (K : ι → Set (Fin 2 → ℝ)) (hv : ∀ i, Convex ℝ (K i)) {r : ℕ}
    (hcross : ∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j,
      ∀ z ∈ standardIntegerLattice 2, x - y ≠ (r : ℝ) • z)
    {i j : ι} {v w : Fin 2 → ℝ} (hvD : v ∈ K i - K i) (hwD : w ∈ K j - K j)
    (hvΛ : v ∈ scaledStandardLattice r) (hwΛ : w ∈ scaledStandardLattice r)
    (hind : LinearIndependent ℝ ![v, w]) : i = j := by
  by_contra hij
  have hdis := latticeSaturations_disjoint_of_cross_periods (hcross i j hij)
  obtain ⟨a, ha, hav⟩ := exists_period_segment_of_mem_difference hvD
  obtain ⟨b, hb, hbw⟩ := exists_period_segment_of_mem_difference hwD
  obtain ⟨p, hpK, hpH⟩ := latticeSaturations_intersect_of_independent_periods
    (show finrank ℝ (Fin 2 → ℝ) = 2 from Module.finrank_fin_fun ℝ)
    (hv i) (hv j) hvΛ hwΛ hind ha hav hb hbw
  exact (Set.disjoint_left.mp hdis) hpK hpH

/-- Other bodies have unique representatives modulo the smaller period.
This is the exact property needed for the union of their lattice points. -/
theorem other_body_scaled_period_separated
    {ι : Type*} (K : ι → Set (Fin 2 → ℝ)) (hv : ∀ i, Convex ℝ (K i)) {r : ℕ}
    (hcross : ∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j,
      ∀ z ∈ standardIntegerLattice 2, x - y ≠ (r : ℝ) • z)
    {i₀ : ι} {v w : Fin 2 → ℝ} (hvD : v ∈ K i₀ - K i₀) (hwD : w ∈ K i₀ - K i₀)
    (hvΛ : v ∈ scaledStandardLattice r) (hwΛ : w ∈ scaledStandardLattice r)
    (hind : LinearIndependent ℝ ![v, w]) :
    ∀ j, j ≠ i₀ → ∀ x ∈ K j, ∀ y ∈ K j, ∀ z ∈ standardIntegerLattice 2,
      x - y = (r : ℝ) • z → x = y := by
  intro j hji x hx y hy z hz he
  by_contra hxy
  have hdis := latticeSaturations_disjoint_of_cross_periods (hcross i₀ j (Ne.symm hji))
  obtain ⟨a, ha, hav⟩ := exists_period_segment_of_mem_difference hvD
  obtain ⟨b, hb, hbw⟩ := exists_period_segment_of_mem_difference hwD
  have hpΛ : x - y ∈ scaledStandardLattice r := mem_scaledStandardLattice.mpr ⟨z, hz, he⟩
  have hno := no_period_of_disjoint_from_two_independent_periods
    (show finrank ℝ (Fin 2 → ℝ) = 2 from Module.finrank_fin_fun ℝ)
    (hv i₀) (hv j) hdis hvΛ hwΛ hind ha hav hb hbw hpΛ (sub_ne_zero.mpr hxy) hy
  apply hno
  convert hx using 1
  ext i
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

/-- The finite lattice intersection of a compact planar set. -/
noncomputable def compactPlanarLatticeFinset {K : Set (Fin 2 → ℝ)} (hc : IsCompact K) :
    Finset (Fin 2 → ℝ) :=
  (DiscreteMinkowski.finite_inter_lattice hc.isBounded (standardIntegerLattice 2)).toFinset

theorem mem_compactPlanarLatticeFinset {K : Set (Fin 2 → ℝ)} (hc : IsCompact K)
    {x : Fin 2 → ℝ} : x ∈ compactPlanarLatticeFinset hc ↔ x ∈ K ∧ x ∈ standardIntegerLattice 2 := by
  simp [compactPlanarLatticeFinset]

theorem compactPlanarLatticeFinset_card {K : Set (Fin 2 → ℝ)} (hc : IsCompact K) :
    (compactPlanarLatticeFinset hc).card =
      (DiscreteMinkowski.latticePoints K (standardIntegerLattice 2)).ncard :=
  (Set.ncard_eq_toFinset_card _ _).symm

/-- The lattice points of every body other than the chosen pivot body. -/
noncomputable def otherBodiesLatticeFinset {ι : Type*} [Fintype ι]
    (K : ι → Set (Fin 2 → ℝ)) (hc : ∀ i, IsCompact (K i)) (i₀ : ι) :
    Finset (Fin 2 → ℝ) := by
  classical
  exact (Finset.univ.erase i₀).biUnion (fun i => compactPlanarLatticeFinset (hc i))

theorem mem_otherBodiesLatticeFinset {ι : Type*} [Fintype ι]
    (K : ι → Set (Fin 2 → ℝ)) (hc : ∀ i, IsCompact (K i)) (i₀ : ι) {x : Fin 2 → ℝ} :
    x ∈ otherBodiesLatticeFinset K hc i₀ ↔
      ∃ i, i ≠ i₀ ∧ x ∈ K i ∧ x ∈ standardIntegerLattice 2 := by
  classical
  simp [otherBodiesLatticeFinset, mem_compactPlanarLatticeFinset]

theorem otherBodiesLatticeFinset_subset_lattice {ι : Type*} [Fintype ι]
    (K : ι → Set (Fin 2 → ℝ)) (hc : ∀ i, IsCompact (K i)) (i₀ : ι) :
    ∀ x ∈ otherBodiesLatticeFinset K hc i₀, x ∈ standardIntegerLattice 2 := by
  intro x hx
  obtain ⟨i, hi, hxK, hxΛ⟩ := (mem_otherBodiesLatticeFinset K hc i₀).mp hx
  exact hxΛ

/-- Cross-separated bodies have no repeated lattice points in their finite union. -/
theorem otherBodiesLatticeFinset_card {ι : Type*} [Fintype ι]
    (K : ι → Set (Fin 2 → ℝ)) (hc : ∀ i, IsCompact (K i)) (i₀ : ι)
    (hdis : ∀ i j, i ≠ j → Disjoint (K i) (K j)) :
    (DiscreteMinkowski.latticePoints (K i₀) (standardIntegerLattice 2)).ncard +
      (otherBodiesLatticeFinset K hc i₀).card =
      ∑ i, (DiscreteMinkowski.latticePoints (K i) (standardIntegerLattice 2)).ncard := by
  classical
  have hp : (Finset.univ.erase i₀ : Set ι).PairwiseDisjoint
      (fun i => compactPlanarLatticeFinset (hc i)) := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro x hxi hxj
    exact (Set.disjoint_left.mp (hdis i j hij))
      ((mem_compactPlanarLatticeFinset (hc i)).mp hxi).1
      ((mem_compactPlanarLatticeFinset (hc j)).mp hxj).1
  rw [otherBodiesLatticeFinset, Finset.card_biUnion hp]
  simp_rw [compactPlanarLatticeFinset_card]
  exact Finset.add_sum_erase Finset.univ
    (fun i => (DiscreteMinkowski.latticePoints (K i) (standardIntegerLattice 2)).ncard)
    (Finset.mem_univ i₀)

/-- The union of all nonpivot lattice points has distinct smaller-period cosets. -/
theorem otherBodiesLatticeFinset_period_separated {ι : Type*} [Fintype ι]
    (K : ι → Set (Fin 2 → ℝ)) (hc : ∀ i, IsCompact (K i)) (i₀ : ι) {r : ℕ}
    (hcross : ∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j,
      ∀ z ∈ standardIntegerLattice 2, x - y ≠ (r : ℝ) • z)
    (hother : ∀ j, j ≠ i₀ → ∀ x ∈ K j, ∀ y ∈ K j,
      ∀ z ∈ standardIntegerLattice 2, x - y = (r : ℝ) • z → x = y) :
    ∀ x ∈ otherBodiesLatticeFinset K hc i₀, ∀ y ∈ otherBodiesLatticeFinset K hc i₀,
      ∀ z ∈ standardIntegerLattice 2, x - y = (r : ℝ) • z → x = y := by
  intro x hx y hy z hz he
  obtain ⟨i, hi, hxK, hxΛ⟩ := (mem_otherBodiesLatticeFinset K hc i₀).mp hx
  obtain ⟨j, hj, hyK, hyΛ⟩ := (mem_otherBodiesLatticeFinset K hc i₀).mp hy
  by_cases hij : i = j
  · subst j
    exact hother i hi x hxK y hyK z hz he
  · exact False.elim (hcross i j hij x hxK y hyK z hz he)

/-- The pivot body avoids the periodic union of the other lattice points. -/
theorem pivot_disjoint_otherBodies_coset_union {ι : Type*} [Fintype ι]
    (K : ι → Set (Fin 2 → ℝ)) (hc : ∀ i, IsCompact (K i)) (i₀ : ι) {r : ℕ}
    (hcross : ∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j,
      ∀ z ∈ standardIntegerLattice 2, x - y ≠ (r : ℝ) • z) :
    Disjoint (K i₀)
      (latticeCosetUnion (otherBodiesLatticeFinset K hc i₀) (standardIntegerLattice 2) r) := by
  apply Set.disjoint_left.mpr
  rintro x hx ⟨y, hy, z, hz, he⟩
  obtain ⟨j, hj, hyK, hyΛ⟩ := (mem_otherBodiesLatticeFinset K hc i₀).mp hy
  apply hcross i₀ j (Ne.symm hj) x hx y hyK z hz
  rw [he]
  abel

end LatticeVolumeInterpolation
