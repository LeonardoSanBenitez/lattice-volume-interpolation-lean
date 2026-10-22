import LviBasic
import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Lattice-empty translates

Catalog item `bhw_lattice_conjecture_dimension_three_symmetric`.
Malikiosis's Lemma 2.3 chooses a lattice point minimizing the number of
lattice points in its convex hull with the lattice-free convex body.
The strict hull reduction below supplies the geometric step of that argument.
-/

open Set
open scoped Pointwise

namespace LatticeVolumeInterpolation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Moving from `v` towards a point of a convex set along a strict
intermediate point prevents the old vertex from lying in the new hull.
This is the strict reduction used in the source's minimum-count argument. -/
theorem not_mem_convexHull_after_strict_step
    {K : Set E} (hK : Convex ℝ K) {v u : E} {t : ℝ} (ht : 1 < t)
    (hx : v + t • u ∈ K) (hv : v ∉ K) :
    v ∉ convexHull ℝ (insert (v + u) K) := by
  intro hmem
  rw [convexHull_insert ⟨_, hx⟩, hK.convexHull_eq, mem_convexJoin] at hmem
  obtain ⟨w, hw, y, hy, a, b, ha, hb, hab, heq⟩ := hmem
  have hw' : w = v + u := mem_singleton_iff.mp hw
  subst w
  have htpos : 0 < t := by linarith
  have hapos : 0 ≤ a / t := div_nonneg ha htpos.le
  have hd : 0 < a / t + b := by
    by_cases ha0 : a = 0
    · subst a
      norm_num at hab ⊢
      linarith
    · have hagt : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      exact add_pos_of_pos_of_nonneg (div_pos hagt htpos) hb
  have hbalance : (a / t) • (v + t • u) + b • y = (a / t + b) • v := by
    have heq' : a • v + a • u + b • y = v := by simpa only [smul_add] using heq
    have hac : (a / t) * t = a := by field_simp
    calc
      _ = (a / t) • v + a • u + b • y := by rw [smul_add, smul_smul, hac]
      _ = (a / t - a) • v + (a • v + a • u + b • y) := by
        simp only [sub_smul]; abel
      _ = (a / t - a) • v + v := by rw [heq']
      _ = _ := by
        calc
          _ = (a / t - a) • v + (1 : ℝ) • v := by rw [one_smul]
          _ = (a / t - a + 1) • v := (add_smul _ _ _).symm
          _ = (a / t + b) • v := by congr 1; linarith
  have hcoeff : (a / t) / (a / t + b) + b / (a / t + b) = 1 := by
    rw [← add_div, div_self hd.ne']
  have hc := hK hx hy (div_nonneg hapos hd.le) (div_nonneg hb hd.le) hcoeff
  apply hv
  convert hc using 1
  symm
  calc
    _ = (a / t + b)⁻¹ • ((a / t) • (v + t • u) + b • y) := by
      simp only [smul_add, smul_smul, div_eq_mul_inv, mul_comm, mul_assoc]
    _ = (a / t + b)⁻¹ • ((a / t + b) • v) := by rw [hbalance]
    _ = v := by rw [smul_smul, inv_mul_cancel₀ hd.ne', one_smul]

/-- A convex hull vertex cannot be recovered after replacing it by a
different point of the hull. This version also covers replacements in `K`. -/
theorem not_mem_convexHull_insert_swap
    {K : Set E} (hK : Convex ℝ K) (hne : K.Nonempty) {v w : E}
    (hv : v ∉ K) (hw : w ∈ convexHull ℝ (insert v K)) (hwv : w ≠ v) :
    v ∉ convexHull ℝ (insert w K) := by
  by_cases hwK : w ∈ K
  · rwa [insert_eq_of_mem hwK, hK.convexHull_eq]
  rw [convexHull_insert hne, hK.convexHull_eq, mem_convexJoin] at hw
  obtain ⟨v', hv', y, hy, a, b, ha, hb, hab, heq⟩ := hw
  have hv'v : v' = v := mem_singleton_iff.mp hv'
  subst v'
  have hb0 : b ≠ 0 := by
    intro hzero
    have ha1 : a = 1 := by linarith
    exact hwv (by simpa [hzero, ha1] using heq.symm)
  have hb1 : b ≠ 1 := by
    intro hone
    have ha0 : a = 0 := by linarith
    have hyw : y = w := by simpa [hone, ha0] using heq
    exact hwK (hyw ▸ hy)
  have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  have hblt : b < 1 := lt_of_le_of_ne (by linarith) hb1
  have ht : 1 < 1 / b := (lt_div_iff₀ hbpos).mpr (by linarith)
  have hscale : b • (y - v) = w - v := by
    calc
      _ = (a • v + b • y) - (a + b) • v := by
        simp only [smul_sub, add_smul]; abel
      _ = _ := by rw [heq, hab, one_smul]
  have htarget : v + (1 / b) • (w - v) = y := by
    rw [one_div, ← hscale, smul_smul, inv_mul_cancel₀ hb0, one_smul]
    abel
  have hx : v + (1 / b) • (w - v) ∈ K := by rwa [htarget]
  have hstep := not_mem_convexHull_after_strict_step hK ht hx hv
  have he : v + (w - v) = w := by abel
  simpa only [he] using hstep

/-- Minimize the finite number of forbidden points in a vertex hull.
The minimizing hull contains just its chosen forbidden vertex. This form
also applies to finite unions of lattice cosets in source Lemma 2.4. -/
theorem exists_vertex_with_singleton_hull_intersection
    {K P : Set E} (hK : Convex ℝ K) (hne : K.Nonempty) (hP : P.Nonempty)
    (hfree : Disjoint K P)
    (hfinite : ∀ v ∈ P, (convexHull ℝ (insert v K) ∩ P).Finite) :
    ∃ v ∈ P, convexHull ℝ (insert v K) ∩ P = {v} := by
  classical
  let f : E → ℕ := fun v => (convexHull ℝ (insert v K) ∩ P).ncard
  have hex : ∃ m : ℕ, ∃ v ∈ P, f v = m := by
    obtain ⟨v, hv⟩ := hP
    exact ⟨f v, v, hv, rfl⟩
  obtain ⟨v, hv, hfv⟩ := Nat.find_spec hex
  have hmin : ∀ w ∈ P, f v ≤ f w := by
    intro w hw
    rw [hfv]
    exact Nat.find_min' hex ⟨w, hw, rfl⟩
  have hvHull : v ∈ convexHull ℝ (insert v K) := subset_convexHull ℝ _ (mem_insert _ _)
  have hvout : v ∉ K := fun h => (Set.disjoint_left.mp hfree) h hv
  have huniq : ∀ w ∈ convexHull ℝ (insert v K) ∩ P, w = v := by
    rintro w ⟨hwHull, hwP⟩
    by_contra hwv
    have hvnot := not_mem_convexHull_insert_swap hK hne hvout hwHull hwv
    have hsub : convexHull ℝ (insert w K) ⊆ convexHull ℝ (insert v K) :=
      convexHull_min (insert_subset_iff.mpr ⟨hwHull,
        (subset_insert v K).trans (subset_convexHull ℝ _)⟩) (convex_convexHull ℝ _)
    have hstrict : convexHull ℝ (insert w K) ∩ P ⊂ convexHull ℝ (insert v K) ∩ P := by
      refine ⟨inter_subset_inter_left P hsub, ?_⟩
      intro hback
      exact hvnot (hback ⟨hvHull, hv⟩).1
    have hlt : f w < f v := Set.ncard_lt_ncard hstrict (hfinite v hv)
    exact (not_lt_of_ge (hmin w hwP)) hlt
  refine ⟨v, hv, Set.Subset.antisymm ?_ ?_⟩
  · intro w hw
    exact mem_singleton_iff.mpr (huniq w hw)
  · rintro _ rfl
    exact ⟨hvHull, hv⟩

/-- Malikiosis Lemma 2.3: a bounded convex lattice-free set misses some
lattice translate of every strictly enlarged lattice. -/
theorem exists_lattice_empty_scaled_translate
    [FiniteDimensional ℝ E] {K : Set E} {Λ : Submodule ℤ E} [DiscreteTopology Λ]
    (hK : Convex ℝ K) (hb : Bornology.IsBounded K)
    (hfree : Disjoint K (Λ : Set E)) {t : ℝ} (ht : 1 < t) :
    ∃ v ∈ Λ, ∀ z ∈ Λ, v + t • z ∉ K := by
  classical
  by_cases hne : K.Nonempty
  · have hfinite : ∀ v ∈ (Λ : Set E),
        (convexHull ℝ (insert v K) ∩ (Λ : Set E)).Finite := by
      intro v _
      exact DiscreteMinkowski.finite_inter_lattice
        (isBounded_convexHull.mpr (hb.insert v)) Λ
    obtain ⟨v, hv, hset⟩ := exists_vertex_with_singleton_hull_intersection
      hK hne ⟨0, Λ.zero_mem⟩ hfree hfinite
    refine ⟨v, hv, ?_⟩
    intro z hz hx
    have htpos : 0 < t := by linarith
    have hrecip : 0 ≤ 1 / t := (div_pos (by norm_num) htpos).le
    have hrecip1 : 1 / t ≤ 1 := (div_le_one htpos).mpr ht.le
    have hvHull : v ∈ convexHull ℝ (insert v K) := subset_convexHull ℝ _ (mem_insert _ _)
    have hxHull : v + t • z ∈ convexHull ℝ (insert v K) :=
      subset_convexHull ℝ _ (mem_insert_of_mem _ hx)
    have hwHull : v + z ∈ convexHull ℝ (insert v K) := by
      have hc := (convex_convexHull ℝ (insert v K)) hvHull hxHull
        (sub_nonneg.mpr hrecip1) hrecip (by ring : (1 - 1 / t) + 1 / t = 1)
      convert hc using 1
      symm
      calc
        _ = ((1 - 1 / t) + 1 / t) • v + ((1 / t) * t) • z := by
          simp only [smul_add, smul_smul, add_smul]; abel
        _ = v + z := by simp [htpos.ne']
    have hw : v + z ∈ convexHull ℝ (insert v K) ∩ (Λ : Set E) :=
      ⟨hwHull, Λ.add_mem hv hz⟩
    rw [hset] at hw
    have hz0 : z = 0 := by
      have he := mem_singleton_iff.mp hw
      simpa using he
    exact (Set.disjoint_left.mp hfree) (by simpa [hz0] using hx) hv
  · refine ⟨0, Λ.zero_mem, ?_⟩
    intro z hz hx
    exact hne ⟨_, hx⟩

end LatticeVolumeInterpolation
