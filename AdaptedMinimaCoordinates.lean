import TheoremThreeOne
import MinimaDifferenceAvoidance

/-!
# Coordinates adapted to every successive-minimum flag

Catalog item `bhw_lattice_conjecture_dimension_three_symmetric`.
This is the source's adapted lattice basis, expressed as an integer
unimodular coordinate change. The original greedy flag is retained,
so repeated minima introduce no strict-minimum premise.
-/

open Set Module
open scoped BigOperators Pointwise

namespace LatticeVolumeInterpolation

/-- One integer coordinate change makes every preceding minimum flag
vanish in all later coordinates. -/
theorem exists_unimodular_minima_flag_coordinates
    {n : ℕ} {K : Set (Fin n → ℝ)} (hK : DiscreteMinkowski.IsPaperConvexBody K) :
    ∃ V : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ),
      (∀ x, V x ∈ standardIntegerLattice n ↔ x ∈ standardIntegerLattice n) ∧
      ∀ k z, z ∈ DiscreteMinkowski.flagSpan K (standardIntegerLattice n) k →
        ∀ l : Fin n, k ≤ l.1 → (V z) l = 0 := by
  classical
  have hdim : finrank ℝ (Fin n → ℝ) = n := Module.finrank_fin_fun ℝ
  let v : Fin n → (Fin n → ℝ) := fun k =>
    DiscreteMinkowski.flagVector K (standardIntegerLattice n) k.1
  have hvΛ : ∀ k, v k ∈ standardIntegerLattice n := fun k =>
    DiscreteMinkowski.flagVector_mem k.1
      (DiscreteMinkowski.greedyChoice_flagSpan hK (by rw [hdim]; exact k.2))
  have hvind : LinearIndependent ℝ v := linearIndependent_flagVector hK
  choose p hp using fun k => (mem_standardIntegerLattice_iff_castCoords (v k)).mp (hvΛ k)
  have hpind : LinearIndependent ℤ p := by
    rw [Fintype.linearIndependent_iff] at hvind ⊢
    intro g hg k
    have hreal : ∑ j, (g j : ℝ) • v j = 0 := by
      funext l
      have := congrFun hg l
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
      simp only [hp, castCoords]
      exact_mod_cast this
    exact_mod_cast hvind _ hreal k
  obtain ⟨U, hU⟩ := exists_triangularizing n p hpind
  obtain ⟨V, hV, hVs, _⟩ := realize_unimodular U
  refine ⟨V, mem_lattice_iff_of_realize V hV hVs, ?_⟩
  have htri : ∀ i l : Fin n, i < l → (V (v i)) l = 0 := by
    intro i l hil
    rw [hp i, hV]
    change (U (p i) l : ℝ) = 0
    exact_mod_cast hU i l hil
  intro k z hz l hkl
  let f : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
    (LinearMap.proj l).comp V.toLinearMap
  have hgen : ∀ m, m < k →
      DiscreteMinkowski.flagVector K (standardIntegerLattice n) m ∈ LinearMap.ker f := by
    intro m hm
    have hmn : m < n := lt_trans (lt_of_lt_of_le hm hkl) l.isLt
    change (V (DiscreteMinkowski.flagVector K (standardIntegerLattice n) m)) l = 0
    exact htri ⟨m, hmn⟩ l (show m < l.1 from lt_of_lt_of_le hm hkl)
  have hflag := DiscreteMinkowski.flagSpan_le_span
    (K := K) (Λ := standardIntegerLattice n) (S := (LinearMap.ker f : Set (Fin n → ℝ))) k hgen
  have hspan : Submodule.span ℝ (LinearMap.ker f : Set (Fin n → ℝ)) ≤ LinearMap.ker f :=
    Submodule.span_le.mpr (fun _ h => h)
  change z ∈ LinearMap.ker f
  exact hspan (hflag hz)

/-- The source's difference avoidance in an adapted integer frame. A
nonzero later coordinate excludes membership in the preceding minimum flag. -/
theorem exists_unimodular_minima_difference_coordinates
    {n : ℕ} {K : Set (Fin n → ℝ)} (hK : DiscreteMinkowski.IsPaperConvexBody K) :
    ∃ V : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ),
      (∀ x, V x ∈ standardIntegerLattice n ↔ x ∈ standardIntegerLattice n) ∧
      ∀ k, k < n → ∀ q : ℝ, 0 < q →
        2 / q < DiscreteMinkowski.successiveMinimum K (standardIntegerLattice n) (k + 1) →
        ∀ x ∈ V '' K, ∀ y ∈ V '' K, ∀ z ∈ standardIntegerLattice n,
          ∀ l : Fin n, k ≤ l.1 → z l ≠ 0 → x - y ≠ q • z := by
  obtain ⟨V, hΛ, hflag⟩ := exists_unimodular_minima_flag_coordinates hK
  refine ⟨V, hΛ, ?_⟩
  intro k hk q hq hcritical
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ z hz l hkl hzl he
  have hzback : V.symm z ∈ standardIntegerLattice n := by
    apply (hΛ (V.symm z)).mp
    simpa using hz
  have hzflag : V.symm z ∉ DiscreteMinkowski.flagSpan K (standardIntegerLattice n) k := by
    intro hmem
    have hh := hflag k (V.symm z) hmem l hkl
    exact hzl (by simpa using hh)
  apply difference_ne_smul_outside_minima_flag hK
    (by simpa only [Module.finrank_fin_fun] using hk) hq hcritical hzback hzflag hx hy
  apply V.injective
  rw [map_sub, map_smul, V.apply_symm_apply]
  exact he

end LatticeVolumeInterpolation
