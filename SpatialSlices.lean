import RepairedPlanarFamily

/-!
# Planar slices of a three-dimensional body

The height decomposition used in the dimension-three lattice bound.
Slices may have empty interior; compactness and convexity are sufficient.
-/

open Set
open scoped BigOperators Pointwise

namespace LatticeVolumeInterpolation

noncomputable section

def spatialSlice (K : Set (Fin 3 → ℝ)) (t : ℝ) : Set (Fin 2 → ℝ) :=
  {x | Fin.snoc x t ∈ K}

theorem spatialSlice_compact {K : Set (Fin 3 → ℝ)} (hc : IsCompact K) (t : ℝ) :
    IsCompact (spatialSlice K t) := by
  refine Metric.isCompact_of_isClosed_isBounded
    (show IsClosed (spatialSlice K t) from hc.isClosed.preimage
      (show Continuous (fun x : Fin 2 → ℝ => (Fin.snoc x t : Fin 3 → ℝ)) by fun_prop)) ?_
  have hcont : Continuous (Fin.init : (Fin 3 → ℝ) → (Fin 2 → ℝ)) := by
    fun_prop
  refine (hc.image hcont).isBounded.subset ?_
  intro x hx
  exact ⟨Fin.snoc x t, hx, by simp only [Fin.init_snoc]⟩

theorem spatialSlice_convex {K : Set (Fin 3 → ℝ)} (hv : Convex ℝ K) (t : ℝ) :
    Convex ℝ (spatialSlice K t) := by
  intro x hx y hy a b ha hb hab
  have hh := hv hx hy ha hb hab
  have he : a • Fin.snoc x t + b • Fin.snoc y t = Fin.snoc (a • x + b • y) t := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Pi.add_apply, Pi.smul_apply, Fin.snoc_last, smul_eq_mul]
      rw [← add_mul, hab, one_mul]
    · simp
  change Fin.snoc (a • x + b • y) t ∈ K
  rw [← he]
  exact hh

def spatialHeightLo (K : Set (Fin 3 → ℝ)) : ℝ := sInf ((fun x => x (Fin.last 2)) '' K)
def spatialHeightHi (K : Set (Fin 3 → ℝ)) : ℝ := sSup ((fun x => x (Fin.last 2)) '' K)

theorem spatial_height_image {K : Set (Fin 3 → ℝ)}
    (hc : IsCompact K) (hv : Convex ℝ K) (hne : K.Nonempty) :
    (fun x => x (Fin.last 2)) '' K = Icc (spatialHeightLo K) (spatialHeightHi K) := by
  have hcomp := hc.image (continuous_apply (Fin.last 2))
  have hconv := hv.linear_image (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) (Fin.last 2))
  have hnon := hne.image (fun x => x (Fin.last 2))
  refine Subset.antisymm
    (fun t ht => ⟨csInf_le hcomp.bddBelow ht, le_csSup hcomp.bddAbove ht⟩) ?_
  exact (convex_iff_ordConnected.1 hconv).out (hcomp.sInf_mem hnon) (hcomp.sSup_mem hnon)

theorem spatialSlice_nonempty_iff {K : Set (Fin 3 → ℝ)}
    (hc : IsCompact K) (hv : Convex ℝ K) (hne : K.Nonempty) (t : ℝ) :
    (spatialSlice K t).Nonempty ↔ t ∈ Icc (spatialHeightLo K) (spatialHeightHi K) := by
  rw [← spatial_height_image hc hv hne]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨Fin.snoc x t, hx, by simp only [Fin.snoc_last]⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨Fin.init x, ?_⟩
    change Fin.snoc (Fin.init x) (x (Fin.last 2)) ∈ K
    rw [Fin.snoc_init_self]
    exact hx

theorem snoc_mem_standardIntegerLattice {x : Fin 2 → ℝ}
    (hx : x ∈ standardIntegerLattice 2) (t : ℤ) :
    Fin.snoc x (t : ℝ) ∈ standardIntegerLattice 3 := by
  obtain ⟨p, hp⟩ := (mem_standardIntegerLattice_iff_castCoords x).mp hx
  apply (mem_standardIntegerLattice_iff_castCoords _).mpr
  refine ⟨Fin.snoc p t, ?_⟩
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · change (Fin.snoc x (t : ℝ) : Fin 3 → ℝ) (Fin.last 2) =
      (((Fin.snoc p t : Fin 3 → ℤ) (Fin.last 2)) : ℝ)
    rw [Fin.snoc_last, Fin.snoc_last]
  · simp only [Fin.snoc_castSucc, castCoords]
    exact congrFun hp j

theorem spatial_lattice_count_eq_slices {K : Set (Fin 3 → ℝ)}
    (hc : IsCompact K) (hv : Convex ℝ K) (hne : K.Nonempty) :
    (DiscreteMinkowski.latticePoints K (standardIntegerLattice 3)).ncard =
      ∑ t ∈ Finset.Icc ⌈spatialHeightLo K⌉ ⌊spatialHeightHi K⌋,
        (DiscreteMinkowski.latticePoints (spatialSlice K t) (standardIntegerLattice 2)).ncard := by
  classical
  let J := Finset.Icc ⌈spatialHeightLo K⌉ ⌊spatialHeightHi K⌋
  let N : ℤ → Finset (Fin 2 → ℝ) := fun t => compactPlanarLatticeFinset (spatialSlice_compact hc t)
  let F : (Σ _ : ℤ, Fin 2 → ℝ) → (Fin 3 → ℝ) := fun p => Fin.snoc p.2 (p.1 : ℝ)
  have hinj : Function.Injective F := by
    rintro ⟨t, x⟩ ⟨s, y⟩ he
    have ht : (t : ℝ) = (s : ℝ) := by
      simpa only [F, Fin.snoc_last] using congrFun he (Fin.last 2)
    have hx : x = y := by
      simpa only [F, Fin.init_snoc] using congrArg Fin.init he
    have hts : t = s := by exact_mod_cast ht
    subst s; subst y; rfl
  have hset : DiscreteMinkowski.latticePoints K (standardIntegerLattice 3) =
      ((J.sigma N).image F : Set (Fin 3 → ℝ)) := by
    ext z
    simp only [DiscreteMinkowski.latticePoints_apply, mem_inter_iff, SetLike.mem_coe,
      Finset.coe_image, mem_image, Finset.mem_coe, Finset.mem_sigma]
    constructor
    · rintro ⟨hzK, hzΛ⟩
      obtain ⟨w, hw⟩ := (mem_standardIntegerLattice_iff_castCoords z).mp hzΛ
      have hheight : z (Fin.last 2) ∈ Icc (spatialHeightLo K) (spatialHeightHi K) := by
        rw [← spatial_height_image hc hv hne]
        exact ⟨z, hzK, rfl⟩
      have hzt : z (Fin.last 2) = (w (Fin.last 2) : ℝ) := congrFun hw _
      have htJ : w (Fin.last 2) ∈ J := by
        simpa only [J, Finset.mem_Icc, Int.ceil_le, Int.le_floor, ← hzt, Set.mem_Icc] using hheight
      have hinitΛ : Fin.init z ∈ standardIntegerLattice 2 := by
        apply (mem_standardIntegerLattice_iff_castCoords _).mpr
        refine ⟨Fin.init w, ?_⟩
        ext j
        exact congrFun hw j.castSucc
      have hback : Fin.snoc (Fin.init z) (w (Fin.last 2) : ℝ) = z := by
        rw [← hzt, Fin.snoc_init_self]
      refine ⟨⟨w (Fin.last 2), Fin.init z⟩, ⟨htJ, ?_⟩, hback⟩
      apply (mem_compactPlanarLatticeFinset _).mpr
      exact ⟨by change Fin.snoc (Fin.init z) (w (Fin.last 2) : ℝ) ∈ K; rwa [hback], hinitΛ⟩
    · rintro ⟨⟨t, x⟩, ⟨_, hx⟩, rfl⟩
      have hx' := (mem_compactPlanarLatticeFinset _).mp hx
      exact ⟨hx'.1, snoc_mem_standardIntegerLattice hx'.2 t⟩
  rw [hset, Set.ncard_coe_finset, Finset.card_image_of_injective _ hinj, Finset.card_sigma]
  exact Finset.sum_congr rfl (fun t _ => compactPlanarLatticeFinset_card _)

end
end LatticeVolumeInterpolation
