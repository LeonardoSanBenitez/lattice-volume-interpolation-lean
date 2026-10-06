import ReverseSchymura
import Tiles

/-!
# Theorem 1.3 is tight for boxes

Catalog item `theorem_1_3_tight_for_boxes` (Sec. 4, end of the proof of Theorem 1.3): for
`K = [0, k_1] × ... × [0, k_n]` with `k_i ∈ ℤ_{>0}` and `b_i = e_i`,

  `vol(K) = ∏ k_i = ∑_{I ⊆ [n]} ∏_{i ∉ I} (k_i - 1) = ∑_{I ⊆ [n]} G_{ℤ^n | L_I^⊥}(int K | L_I^⊥)`.

The projection onto `L_I^⊥` forgets the coordinates in `I`; it has kernel `L_I`, so by
`encard_image_inter_eq_classCount` its count is the class count, and it maps `int K` onto the
open box in the remaining coordinates and `ℤ^n` onto their integer points.

(The paper writes the middle sum as `∑_I ∏_{i ∈ I} (k_i - 1)`; it is the same sum over the
complements `[n] \ I`.)
-/

open MeasureTheory Set Module
open scoped ENNReal

namespace LatticeVolumeInterpolation

noncomputable section

variable {n : ℕ}

/-- The box `[0, k_1] × ... × [0, k_n]`. -/
def intBox (k : Fin n → ℕ) : Set (Fin n → ℝ) := Set.pi univ fun i => Icc (0 : ℝ) (k i)

/-- Forgetting the coordinates in `I`. -/
def restrictOff (I : Finset (Fin n)) : (Fin n → ℝ) →ₗ[ℝ] ({i // i ∉ I} → ℝ) where
  toFun x i := x i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The kernel of forgetting the coordinates outside `I` is `L_I = span{e_i : i ∈ I}`. -/
theorem ker_restrictOff (I : Finset (Fin n)) :
    LinearMap.ker (restrictOff I) =
      Submodule.span ℝ ((fun i => (Pi.single i (1 : ℝ) : Fin n → ℝ)) '' ↑I) := by
  classical
  apply le_antisymm
  · intro x hx
    have hx0 : ∀ i, i ∉ I → x i = 0 := fun i hi => congrFun hx ⟨i, hi⟩
    have : x = ∑ i ∈ I, x i • (Pi.single i (1 : ℝ) : Fin n → ℝ) := by
      funext j
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq]
      split_ifs with h
      · rfl
      · exact hx0 j h
    rw [this]
    exact Submodule.sum_mem _ fun i hi =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    show restrictOff I _ = 0
    funext j
    have : (j : Fin n) ≠ i := fun h => j.2 (h ▸ hi)
    simp [restrictOff, Pi.single_eq_of_ne this]

theorem volume_intBox (k : Fin n → ℕ) : volume (intBox k) = ∏ i, (k i : ℝ≥0∞) := by
  rw [intBox, Set.pi_univ_Icc, Real.volume_Icc_pi]
  simp

/-- The projected count of the interior of the box, for `L_I = span{e_i : i ∈ I}`. -/
theorem projCount_interior_intBox (k : Fin n → ℕ) (hk : ∀ i, 1 ≤ k i) (I : Finset (Fin n)) :
    projCount (Submodule.span ℝ ((fun i => (Pi.single i (1 : ℝ) : Fin n → ℝ)) '' ↑I))
      (interior (intBox k)) = ∏ i : {i // i ∉ I}, ((k i - 1 : ℕ) : ℕ∞) := by
  classical
  rw [projCount_eq_classCount, ← ker_restrictOff,
    ← encard_image_inter_eq_classCount (restrictOff I) _ rfl]
  -- the image is the integer points of the open box in the remaining coordinates
  have hint : interior (intBox k) = Set.pi univ fun i => Ioo (0 : ℝ) (k i) := by
    rw [intBox, interior_pi_set Set.finite_univ]; simp
  have himg : restrictOff I '' (interior (intBox k)) ∩
      restrictOff I '' ((standardIntegerLattice n).toAddSubgroup : Set (Fin n → ℝ)) =
      ((Fintype.piFinset fun i : {i // i ∉ I} => Finset.Ioo (0 : ℤ) (k i)).map
        ⟨fun z i => (z i : ℝ), fun z w h => funext fun i => by
          simpa using congrFun h i⟩ : Set ({i // i ∉ I} → ℝ)) := by
    ext y
    simp only [mem_inter_iff, mem_image, hint, mem_pi, mem_univ, true_implies, mem_Ioo,
      Finset.coe_map, Function.Embedding.coeFn_mk, Finset.mem_coe, Fintype.mem_piFinset,
      Finset.mem_Ioo]
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, ⟨w, hw, hwy⟩⟩
      obtain ⟨z, hz⟩ := (mem_standardIntegerLattice_iff n w).1 hw
      refine ⟨fun i => z i, fun i => ?_, ?_⟩
      · have h := hx i
        have hwi : w i = x i := congrFun hwy i
        rw [hz i] at hwi
        constructor
        · have : (0 : ℝ) < z i := by rw [hwi]; exact h.1
          exact_mod_cast this
        · have : (z i : ℝ) < k i := by rw [hwi]; exact h.2
          exact_mod_cast this
      · funext i
        have hwi : w i.1 = x i.1 := congrFun hwy i
        rw [hz i.1] at hwi
        simpa [restrictOff] using hwi
    · rintro ⟨z, hz, rfl⟩
      refine ⟨⟨fun j => if h : j ∈ I then (k j : ℝ) / 2 else (z ⟨j, h⟩ : ℝ), fun j => ?_, ?_⟩,
        ⟨fun j => if h : j ∈ I then 0 else (z ⟨j, h⟩ : ℝ),
          (mem_standardIntegerLattice_iff n _).2
            ⟨fun j => if h : j ∈ I then 0 else z ⟨j, h⟩, fun j => by
              by_cases h : j ∈ I <;> simp [h]⟩, ?_⟩⟩
      · dsimp only
        split_ifs with h
        · have : (1 : ℝ) ≤ k j := by exact_mod_cast hk j
          constructor <;> linarith
        · have h1 := (hz ⟨j, h⟩).1
          have h2 := (hz ⟨j, h⟩).2
          exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
      · funext i; simp [restrictOff, i.2]
      · funext i; simp [restrictOff, i.2]
  rw [himg, Set.encard_coe_eq_coe_finsetCard, Finset.card_map, Fintype.card_piFinset]
  push_cast
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Int.card_Ioo, sub_zero]
  have := hk i
  norm_cast

/-- **Theorem 1.3 is tight for boxes**: for `k_i ≥ 1` and `b_i = e_i`,
`vol(K) = ∑_{I ⊆ [n]} G_{ℤ^n | L_I^⊥}(int K | L_I^⊥)`. -/
theorem theorem_1_3_tight_for_boxes (k : Fin n → ℕ) (hk : ∀ i, 1 ≤ k i) :
    volume (intBox k) = ∑ I : Finset (Fin n),
      ((projCount (Submodule.span ℝ ((fun i => (Pi.single i (1 : ℝ) : Fin n → ℝ)) '' ↑I))
        (interior (intBox k)) : ℕ∞) : ℝ≥0∞) := by
  classical
  simp_rw [projCount_interior_intBox k hk]
  rw [volume_intBox]
  -- `∏ k_i = ∏ (1 + (k_i - 1)) = ∑_I ∏_{i ∉ I} (k_i - 1)`
  have hk' : ∀ i, (k i : ℝ≥0∞) = 1 + ((k i - 1 : ℕ) : ℝ≥0∞) := by
    intro i; have := hk i; norm_cast; omega
  simp_rw [hk']
  rw [Finset.prod_add, Finset.powerset_univ]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [Finset.prod_const_one, one_mul]
  have hcast : ((∏ i : {i // i ∉ I}, ((k i.1 - 1 : ℕ) : ℕ∞) : ℕ∞) : ℝ≥0∞) =
      ∏ i : {i // i ∉ I}, (((k i.1 - 1 : ℕ) : ℕ∞) : ℝ≥0∞) :=
    map_prod ENat.toENNRealRingHom _ _
  rw [hcast, Finset.prod_subtype (Finset.univ \ I) (p := fun i => i ∉ I) (fun i => by simp)]
  all_goals first | infer_instance | simp

end

end LatticeVolumeInterpolation
