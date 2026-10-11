import AntiBlocking
import StandardLattice

/-!
# Davenport's inequality for anti-blocking bodies

Catalog item `davenport_for_anti_blocking_bodies` (Sec. 4, the display after the proof of
Theorem 1.1). For a compact anti-blocking `K ⊆ ℝ^n`,

  `G(K) ≤ ∑_{I ⊆ [n]} vol_{n-|I|}(K | L_I^⊥)`,

where `G(K)` counts the points of `ℤ^n` in `K` and the term for `I = ∅` is `vol_n(K)`. The paper
prints the resulting sum from `k = 1`; the decomposition it uses runs over all `I`, and the
empty-set term is needed (catalog `known_issues_in_paper`).

The paper's argument: `G(K) = vol((K ∩ ℤ^n) + [-1,0]^n) ≤ vol(K + [-1,0]^n)`, and
`K + [-1,0]^n` is the union over `I` of the prisms
`{x : x | L_I^⊥ ∈ K | L_I^⊥, x_i ∈ [-1, 0] for i ∈ I}`. The proof below follows it, with the
half-open cube `(-1, 0]^n` so that the translates by lattice points are disjoint, and with
`I = {i : x_i < 0}` as the prism that contains a given point `x`. Only the union bound over
the prisms is needed, not their disjointness.

The standard lattice instances used here are supplied by `StandardLattice`.
-/

open MeasureTheory Set Module
open scoped ENNReal Pointwise

namespace LatticeVolumeInterpolation

noncomputable section

variable {n : ℕ}

/-- The half-open unit cube `(-1, 0]^n`. -/
def unitCubeIoc (n : ℕ) : Set (Fin n → ℝ) := Set.pi univ fun _ => Ioc (-1) 0

theorem volume_unitCubeIoc (n : ℕ) : volume (unitCubeIoc n) = 1 := by
  rw [unitCubeIoc, Real.volume_pi_Ioc]
  simp

/-- Differences of points of the cube meet `ℤ^n` only at the origin. -/
theorem unitCubeIoc_sub_avoids (n : ℕ) :
    ∀ z ∈ unitCubeIoc n - unitCubeIoc n, z ∈ (standardIntegerLattice n : Set (Fin n → ℝ)) →
      z = 0 := by
  rintro z ⟨a, ha, b, hb, rfl⟩ hz
  obtain ⟨w, hw⟩ := (mem_standardIntegerLattice_iff n _).1 hz
  funext i
  have hai : -1 < a i ∧ a i ≤ 0 := ha i (mem_univ i)
  have hbi : -1 < b i ∧ b i ≤ 0 := hb i (mem_univ i)
  have hwi := hw i
  simp only [Pi.sub_apply] at hwi
  have hlt : ((w i : ℤ) : ℝ) < 1 := by rw [← hwi]; linarith [hai.1, hbi.2]
  have hgt : (-1 : ℝ) < ((w i : ℤ) : ℝ) := by rw [← hwi]; linarith [hai.2, hbi.1]
  have h0 : w i = 0 := by
    have h1 : w i < 1 := by exact_mod_cast hlt
    have h2 : -1 < w i := by exact_mod_cast hgt
    omega
  simp [Pi.sub_apply, hwi, h0]

/-- The prism over `K ∩ L_I^⊥` with unit thickness in the coordinates of `I`. -/
def coordPrism (I : Finset (Fin n)) (K : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  coordSplit I ⁻¹' ((Set.Icc (fun _ => -1) (fun _ => 0)) ×ˢ sectionOff I K)

theorem volume_coordPrism {K : Set (Fin n → ℝ)} (hKc : IsCompact K) (I : Finset (Fin n)) :
    volume (coordPrism I K) = volume (sectionOff I K) := by
  have hpres : MeasurePreserving (coordSplit I) volume (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    convert volume_preserving_piEquivPiSubtypeProd (fun _ : Fin n => ℝ) (· ∈ I) using 1
    · rfl
    · congr!
  have hsec : MeasurableSet (sectionOff I K) :=
    hKc.isClosed.measurableSet.preimage
      ((coordSplit I).symm.measurable.comp (measurable_const.prodMk measurable_id))
  rw [coordPrism, hpres.measure_preimage (measurableSet_Icc.prod hsec).nullMeasurableSet,
    Measure.prod_prod, Real.volume_Icc_pi]
  simp

/-- A point of a lattice-translated cube lies in the prism indexed by its negative
coordinates. -/
theorem mem_coordPrism_of_mem_vadd_cube {K : Set (Fin n → ℝ)} (hK : IsAntiBlocking K)
    {z : Fin n → ℝ} (hz : z ∈ K) {x : Fin n → ℝ} (hx : x ∈ z +ᵥ unitCubeIoc n) :
    x ∈ coordPrism (Finset.univ.filter fun i => x i < 0) K := by
  classical
  obtain ⟨c, hc, rfl⟩ := hx
  set I := Finset.univ.filter fun i => (z +ᵥ c) i < 0 with hI
  have hci : ∀ i, -1 < c i ∧ c i ≤ 0 := fun i => hc i (mem_univ i)
  have hzi : ∀ i, 0 ≤ z i := hK.1 z hz
  have hiI : ∀ i : {i // i ∈ I}, z i + c i < 0 := by
    intro i
    have h := i.2
    simp only [hI, Finset.mem_filter, Finset.mem_univ, true_and] at h
    simpa [vadd_eq_add] using h
  refine ⟨⟨fun i => ?_, fun i => ?_⟩, ?_⟩
  · change -1 ≤ z i + c i
    linarith [hzi i, (hci i).1]
  · change z i + c i ≤ 0
    exact (hiI i).le
  · change (coordSplit I).symm (0, (coordSplit I (z +ᵥ c)).2) ∈ K
    refine hK.2 z hz _ (fun i => ?_) (fun i => ?_)
    · rw [coordSplit_symm_apply']
      split_ifs with h
      · exact le_rfl
      · have : ¬ (z +ᵥ c) i < 0 := by simpa [hI] using h
        exact le_of_not_gt this
    · rw [coordSplit_symm_apply']
      split_ifs with h
      · exact hzi i
      · simp only [vadd_eq_add, coordSplit, MeasurableEquiv.piEquivPiSubtypeProd,
          Equiv.piEquivPiSubtypeProd]
        change z i + c i ≤ z i
        linarith [(hci i).2]

/-- **Davenport's inequality for anti-blocking bodies**, with the `I = ∅` term. -/
theorem davenport_antiBlocking {K : Set (Fin n → ℝ)} (hKc : IsCompact K)
    (hK : IsAntiBlocking K) :
    ((DiscreteMinkowski.latticePoints K (standardIntegerLattice n)).ncard : ℝ≥0∞) ≤
      ∑ I : Finset (Fin n), volume (projectionOff I K) := by
  classical
  have hfin : (DiscreteMinkowski.latticePoints K (standardIntegerLattice n)).Finite :=
    DiscreteMinkowski.finite_inter_lattice hKc.isBounded _
  set X := hfin.toFinset with hX
  have hXmem : ∀ x ∈ X, x ∈ standardIntegerLattice n := fun x hx =>
    ((hfin.mem_toFinset).1 hx).2
  have hcount : (X.card : ℝ≥0∞) = volume (⋃ x ∈ X, (x +ᵥ unitCubeIoc n)) := by
    rw [DiscreteMinkowski.measure_biUnion_vadd volume
      (MeasurableSet.univ_pi fun _ => measurableSet_Ioc) (unitCubeIoc_sub_avoids n) hXmem,
      volume_unitCubeIoc, mul_one]
  have hsub : (⋃ x ∈ X, (x +ᵥ unitCubeIoc n)) ⊆ ⋃ I : Finset (Fin n), coordPrism I K := by
    intro y hy
    simp only [mem_iUnion] at hy
    obtain ⟨z, hzX, hy⟩ := hy
    have hzK : z ∈ K := ((hfin.mem_toFinset).1 hzX).1
    exact mem_iUnion.2 ⟨_, mem_coordPrism_of_mem_vadd_cube hK hzK hy⟩
  rw [← Set.ncard_coe_finset X, hX, Finite.coe_toFinset] at hcount
  rw [hcount]
  calc volume (⋃ x ∈ X, (x +ᵥ unitCubeIoc n))
      ≤ volume (⋃ I : Finset (Fin n), coordPrism I K) := measure_mono hsub
    _ ≤ ∑ I : Finset (Fin n), volume (coordPrism I K) := measure_iUnion_fintype_le _ _
    _ = ∑ I : Finset (Fin n), volume (projectionOff I K) := by
        refine Finset.sum_congr rfl fun I _ => ?_
        rw [volume_coordPrism hKc, projectionOff_eq_sectionOff hK]

end

end LatticeVolumeInterpolation
