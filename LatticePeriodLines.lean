import LviBasic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Periodic lines and planar collisions

Catalog item `bhw_lattice_conjecture_dimension_three_symmetric`.
This implements the independent-period collision step in Malikiosis's
planar-family proof: periodic translates of a segment contain a whole line,
and two nonparallel lines in the plane intersect.
-/

open Set Module
open scoped Pointwise BigOperators

namespace LatticeVolumeInterpolation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The union of all lattice translates of a set; signs do not matter
because a lattice is an additive group. -/
def latticeSaturation (K : Set E) (Λ : Submodule ℤ E) : Set E :=
  {x | ∃ z ∈ Λ, x + z ∈ K}

theorem mem_latticeSaturation_of_mem {K : Set E} {Λ : Submodule ℤ E}
    {x : E} (hx : x ∈ K) : x ∈ latticeSaturation K Λ :=
  ⟨0, Λ.zero_mem, by simpa using hx⟩

theorem add_mem_latticeSaturation_iff {K : Set E} {Λ : Submodule ℤ E}
    {x z : E} (hz : z ∈ Λ) :
    x + z ∈ latticeSaturation K Λ ↔ x ∈ latticeSaturation K Λ := by
  constructor
  · rintro ⟨w, hw, h⟩
    exact ⟨z + w, Λ.add_mem hz hw, by simpa only [add_assoc] using h⟩
  · rintro ⟨w, hw, h⟩
    refine ⟨w - z, Λ.sub_mem hw hz, ?_⟩
    convert h using 1 <;> abel

/-- A period segment and its integer translates cover the entire real line. -/
theorem line_mem_latticeSaturation_of_period
    {K : Set E} (hK : Convex ℝ K) {Λ : Submodule ℤ E}
    {a v : E} (ha : a ∈ K) (hav : a + v ∈ K) (hv : v ∈ Λ) (s : ℝ) :
    a + s • v ∈ latticeSaturation K Λ := by
  let f : ℝ := s - ⌊s⌋
  have hf0 : 0 ≤ f := Int.fract_nonneg s
  have hf1 : f ≤ 1 := (Int.fract_lt_one s).le
  have hc := hK ha hav (sub_nonneg.mpr hf1) hf0 (by ring : (1 - f) + f = 1)
  have he : (1 - f) • a + f • (a + v) = a + f • v := by
    rw [smul_add, ← add_assoc, ← add_smul]
    simp
  rw [he] at hc
  refine ⟨(-⌊s⌋) • v, Λ.smul_mem _ hv, ?_⟩
  have hshift : ((-⌊s⌋) : ℤ) • v = (-(⌊s⌋ : ℝ)) • v := by
    rw [← Int.cast_smul_eq_zsmul ℝ]
    simp only [Int.cast_neg]
  rw [hshift, add_assoc, ← add_smul]
  simpa only [f, sub_eq_add_neg] using hc

/-- The two independent period lines meet. The basis is a real basis,
not an assumption that the two periods form a full integral lattice basis. -/
theorem latticeSaturations_intersect_of_basis_periods
    {K H : Set E} (hK : Convex ℝ K) (hH : Convex ℝ H)
    (b : Basis (Fin 2) ℝ E) {Λ : Submodule ℤ E}
    (hb₀ : b 0 ∈ Λ) (hb₁ : b 1 ∈ Λ) {a c : E}
    (ha : a ∈ K) (ha₀ : a + b 0 ∈ K)
    (hc : c ∈ H) (hc₁ : c + b 1 ∈ H) :
    (latticeSaturation K Λ ∩ latticeSaturation H Λ).Nonempty := by
  let d := b.repr (c - a)
  have hd : d 0 • b 0 + d 1 • b 1 = c - a := by
    simpa only [Fin.sum_univ_two, d] using b.sum_repr (c - a)
  have he : a + d 0 • b 0 = c + (-d 1) • b 1 := by
    calc
      _ = a + (d 0 • b 0 + d 1 • b 1) - d 1 • b 1 := by abel
      _ = a + (c - a) - d 1 • b 1 := by rw [hd]
      _ = _ := by rw [neg_smul]; abel
  refine ⟨a + d 0 • b 0, line_mem_latticeSaturation_of_period hK ha ha₀ hb₀ _, ?_⟩
  rw [he]
  exact line_mem_latticeSaturation_of_period hH hc hc₁ hb₁ _

/-- Cross-family separation is exactly disjointness of periodic saturations. -/
theorem latticeSaturations_disjoint_iff_difference_avoids
    {K H : Set E} {Λ : Submodule ℤ E} :
    Disjoint (latticeSaturation K Λ) (latticeSaturation H Λ) ↔
      ∀ x ∈ K, ∀ y ∈ H, x - y ∉ Λ := by
  constructor
  · intro hd x hx y hy hdiff
    have hyK : y ∈ latticeSaturation K Λ :=
      ⟨x - y, hdiff, by convert hx using 1 <;> abel⟩
    exact (Set.disjoint_left.mp hd) hyK (mem_latticeSaturation_of_mem hy)
  · intro hcross
    apply Set.disjoint_left.mpr
    rintro p ⟨u, hu, hpu⟩ ⟨v, hv, hpv⟩
    apply hcross _ hpu _ hpv
    have he : (p + u) - (p + v) = u - v := by abel
    rw [he]
    exact Λ.sub_mem hu hv

/-- The collision step for two independent period vectors in a real plane.
The generated basis is only a real basis; no lattice-index premise occurs. -/
theorem latticeSaturations_intersect_of_independent_periods
    [FiniteDimensional ℝ E] (hdim : finrank ℝ E = 2)
    {K H : Set E} (hK : Convex ℝ K) (hH : Convex ℝ H)
    {Λ : Submodule ℤ E} {v w : E} (hv : v ∈ Λ) (hw : w ∈ Λ)
    (hind : LinearIndependent ℝ ![v, w]) {a c : E}
    (ha : a ∈ K) (hav : a + v ∈ K) (hc : c ∈ H) (hcw : c + w ∈ H) :
    (latticeSaturation K Λ ∩ latticeSaturation H Λ).Nonempty := by
  classical
  let b : Basis (Fin 2) ℝ E := basisOfLinearIndependentOfCardEqFinrank hind
    (by simp only [Fintype.card_fin, hdim])
  have hb : (b : Fin 2 → E) = ![v, w] :=
    coe_basisOfLinearIndependentOfCardEqFinrank _ _
  have hb₀ : b 0 = v := by simpa only [Matrix.cons_val_zero] using congrFun hb 0
  have hb₁ : b 1 = w := by
    simpa only [Matrix.cons_val_one, Matrix.cons_val_zero] using congrFun hb 1
  exact latticeSaturations_intersect_of_basis_periods hK hH b
    (by simpa only [hb₀] using hv) (by simpa only [hb₁] using hw)
    ha (by simpa only [hb₀] using hav) hc (by simpa only [hb₁] using hcw)

end LatticeVolumeInterpolation
