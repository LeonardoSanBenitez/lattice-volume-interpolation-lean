import SpatialSlices

/-!
# Counting three-dimensional residue slices

Catalog item `bhw_lattice_conjecture_dimension_three_symmetric`, the
dimension-three confirmation sentence after Conjecture 1.

The planar separated-family theorem is applied separately to the integer
heights in each residue class modulo the third period.
-/

open Set
open scoped BigOperators Pointwise

namespace LatticeVolumeInterpolation

theorem spatial_lattice_count_le_of_period_avoidance
    {K : Set (Fin 3 → ℝ)} (hc : IsCompact K) (hv : Convex ℝ K) (hne : K.Nonempty)
    {q₁ q₂ q₃ : ℕ} (hq₃ : 0 < q₃) (hq₃₂ : q₃ ≤ q₂) (hq₂₁ : q₂ ≤ q₁)
    (hfirst : ∀ x ∈ K, ∀ y ∈ K, ∀ z ∈ standardIntegerLattice 3,
      z ≠ 0 → x - y ≠ (q₁ : ℝ) • z)
    (hsecond : ∀ x ∈ K, ∀ y ∈ K, ∀ z ∈ standardIntegerLattice 3,
      z 1 ≠ 0 → x - y ≠ (q₂ : ℝ) • z)
    (hthird : ∀ x ∈ K, ∀ y ∈ K, ∀ z ∈ standardIntegerLattice 3,
      z (Fin.last 2) ≠ 0 → x - y ≠ (q₃ : ℝ) • z) :
    (DiscreteMinkowski.latticePoints K (standardIntegerLattice 3)).ncard ≤ q₁ * q₂ * q₃ := by
  classical
  haveI : NeZero q₃ := ⟨by omega⟩
  let J := Finset.Icc ⌈spatialHeightLo K⌉ ⌊spatialHeightHi K⌋
  let g : J → ZMod q₃ := fun t => (t.1 : ZMod q₃)
  let f : J → ℕ := fun t =>
    (DiscreteMinkowski.latticePoints (spatialSlice K t.1) (standardIntegerLattice 2)).ncard
  rw [spatial_lattice_count_eq_slices hc hv hne]
  rw [← Finset.sum_coe_sort J (fun t : ℤ =>
    (DiscreteMinkowski.latticePoints (spatialSlice K t) (standardIntegerLattice 2)).ncard)]
  change (∑ t : J, f t) ≤ _
  rw [← Fintype.sum_fiberwise g f]
  have hfiber : ∀ r : ZMod q₃, (∑ t : {t // g t = r}, f t.1) ≤ q₁ * q₂ := by
    intro r
    let A : {t // g t = r} → Set (Fin 2 → ℝ) := fun t => spatialSlice K t.1.1
    apply planar_separated_family_count_bound A
      (fun t => spatialSlice_compact hc _) (fun t => spatialSlice_convex hv _)
      (fun t => (spatialSlice_nonempty_iff hc hv hne _).mpr
        (by simpa only [J, Finset.mem_Icc, Int.ceil_le, Int.le_floor, Set.mem_Icc] using t.1.2))
      hq₃ hq₃₂ hq₂₁
    · intro t x hx y hy z hz hn he
      have hzlift := snoc_mem_standardIntegerLattice hz 0
      have hzn : (Fin.snoc z (0 : ℝ) : Fin 3 → ℝ) ≠ 0 := by
        intro hh
        apply hn
        ext j
        simpa only [Fin.snoc_castSucc, Pi.zero_apply] using congrFun hh j.castSucc
      apply hfirst _ hx _ hy _ hzlift (by simpa only [Int.cast_zero] using hzn)
      ext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Pi.sub_apply, Pi.smul_apply, Fin.snoc_last, smul_eq_mul]
        ring
      · simpa only [Pi.sub_apply, Pi.smul_apply, Fin.snoc_castSucc] using congrFun he j
    · intro t x hx y hy z hz hn he
      apply hsecond _ hx _ hy _ (snoc_mem_standardIntegerLattice hz 0)
        (by change (Fin.snoc z (0 : ℝ) : Fin 3 → ℝ) (1 : Fin 2).castSucc ≠ 0
            simpa only [Fin.snoc_castSucc] using hn)
      ext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Pi.sub_apply, Pi.smul_apply, Fin.snoc_last, smul_eq_mul]
        ring
      · simpa only [Pi.sub_apply, Pi.smul_apply, Fin.snoc_castSucc] using congrFun he j
    · intro t s hts x hx y hy z hz he
      have hlabel : (t.1.1 : ZMod q₃) = (s.1.1 : ZMod q₃) := t.2.trans s.2.symm
      obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub s.1.1 t.1.1 q₃).mp hlabel.symm
      have hdiff : (t.1.1 : ℝ) - s.1.1 = (q₃ : ℝ) * k := by exact_mod_cast hk
      have hk0 : k ≠ 0 := by
        intro hh
        have htval : t.1.1 = s.1.1 := by simp only [hh, mul_zero] at hk; omega
        exact hts (Subtype.ext (Subtype.ext htval))
      apply hthird _ hx _ hy _ (snoc_mem_standardIntegerLattice hz k)
        (by simpa only [Fin.snoc_last, ne_eq, Int.cast_eq_zero] using hk0)
      ext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [Pi.sub_apply, Pi.smul_apply, Fin.snoc_last, smul_eq_mul] using hdiff
      · simpa only [Pi.sub_apply, Pi.smul_apply, Fin.snoc_castSucc] using congrFun he j
  calc
    _ ≤ ∑ _r : ZMod q₃, q₁ * q₂ := Finset.sum_le_sum (fun r _ => hfiber r)
    _ = q₁ * q₂ * q₃ := by simp [Nat.mul_comm]

end LatticeVolumeInterpolation
