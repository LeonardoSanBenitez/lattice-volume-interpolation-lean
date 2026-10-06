import CoveringTile
import BoxCounts

/-!
# Tightness of Proposition 1.6, and lattice tiles

Catalog items `proposition_1_6_tight_for_cubes` and `lattice_tile_sandwich`.

**Cubes** (Sec. 4, end of the proof of Proposition 1.6). For `K = [0, m]^n`, `m ∈ ℤ_{>0}`:
`vol(K) = m^n`, `G(K) = (m+1)^n`, `G(int K) = (m-1)^n` and `μ(K) = 1/m`, so both bounds of
Proposition 1.6 are equalities (`proposition_1_6_tight_for_cubes`).

**Lattice tiles** (Sec. 1, after Proposition 1.6). A convex body `K` with `K + ℤ^n = ℝ^n` and
`int K ∩ (z + int K) = ∅` for `z ∈ ℤ^n \ {0}` has `vol(K) = μ(K) = 1`, and `μ(rK) = μ(K)/r`; so
Proposition 1.6 gives `(r-1)^n ≤ G(int(rK)) ≤ G(rK) ≤ (r+1)^n` for `r ≥ 1`
(`lattice_tile_sandwich`), with equality for `K = [0,1]^n` and integer `r` by the cube case.
Both volume facts come from the translate-count identity of `VanDerCorput.lean`: a covering
body has at least one translate at every point, a tile at most one.
-/

open MeasureTheory Set Module
open scoped ENNReal Pointwise

namespace LatticeVolumeInterpolation

noncomputable section

variable {n : ℕ}

/-- Counting lattice points of a coordinate product of intervals. -/
theorem ncard_latticePoints_pi (I : Fin n → Set ℝ) (A : Fin n → Finset ℤ)
    (hA : ∀ i (k : ℤ), k ∈ A i ↔ (k : ℝ) ∈ I i) :
    (DiscreteMinkowski.latticePoints (Set.pi univ I) (standardIntegerLattice n)).ncard =
      ∏ i, (A i).card := by
  classical
  have hset : DiscreteMinkowski.latticePoints (Set.pi univ I) (standardIntegerLattice n) =
      ((Fintype.piFinset A).map (intToRealCoordinatesEmbedding n) : Set (Fin n → ℝ)) := by
    ext x
    simp only [DiscreteMinkowski.latticePoints_apply, mem_inter_iff, mem_pi, mem_univ,
      true_implies, SetLike.mem_coe, Finset.coe_map, mem_image, Fintype.mem_piFinset]
    constructor
    · rintro ⟨hx, hxΛ⟩
      obtain ⟨z, hz⟩ := (mem_standardIntegerLattice_iff n x).1 hxΛ
      refine ⟨z, fun i => (hA i (z i)).2 (by rw [← hz i]; exact hx i), ?_⟩
      funext i
      simpa [intToRealCoordinatesEmbedding, intToRealCoordinates] using (hz i).symm
    · rintro ⟨z, hz, rfl⟩
      refine ⟨fun i => ?_, (mem_standardIntegerLattice_iff n _).2 ⟨z, fun i => rfl⟩⟩
      simpa [intToRealCoordinatesEmbedding, intToRealCoordinates] using (hA i (z i)).1 (hz i)
  rw [hset, Set.ncard_coe_finset, Finset.card_map, Fintype.card_piFinset]

/-- The cube `[0, m]^n`. -/
def cube (n m : ℕ) : Set (Fin n → ℝ) := Set.pi univ fun _ => Icc (0 : ℝ) m

theorem volume_cube (m : ℕ) : volume (cube n m) = ENNReal.ofReal ((m : ℝ) ^ n) := by
  rw [cube, Set.pi_univ_Icc, Real.volume_Icc_pi]
  simp [Finset.prod_const, ENNReal.ofReal_pow (Nat.cast_nonneg m)]

theorem interior_cube (m : ℕ) : interior (cube n m) = Set.pi univ fun _ => Ioo (0 : ℝ) m := by
  rw [cube, interior_pi_set Set.finite_univ]
  simp

theorem ncard_latticePoints_cube (m : ℕ) :
    (DiscreteMinkowski.latticePoints (cube n m) (standardIntegerLattice n)).ncard =
      (m + 1) ^ n := by
  rw [cube, ncard_latticePoints_pi _ (fun _ => Finset.Icc 0 (m : ℤ))]
  · simp [Int.card_Icc]
  · intro i k
    simp only [Finset.mem_Icc, mem_Icc]
    constructor
    · rintro ⟨h0, hm⟩; exact ⟨by exact_mod_cast h0, by exact_mod_cast hm⟩
    · rintro ⟨h0, hm⟩; exact ⟨by exact_mod_cast h0, by exact_mod_cast hm⟩

theorem ncard_latticePoints_interior_cube {m : ℕ} (hm : 1 ≤ m) :
    (DiscreteMinkowski.latticePoints (interior (cube n m)) (standardIntegerLattice n)).ncard =
      (m - 1) ^ n := by
  rw [interior_cube, ncard_latticePoints_pi _ (fun _ => Finset.Ioo 0 (m : ℤ))]
  · simp only [Int.card_Ioo, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 1
    omega
  · intro i k
    simp only [Finset.mem_Ioo, mem_Ioo]
    constructor
    · rintro ⟨h0, hm⟩; exact ⟨by exact_mod_cast h0, by exact_mod_cast hm⟩
    · rintro ⟨h0, hm⟩; exact ⟨by exact_mod_cast h0, by exact_mod_cast hm⟩

/-- `r [0, m]^n = [0, r m]^n` membership, for `r > 0`. -/
theorem mem_smul_cube_iff {m : ℕ} {r : ℝ} (hr : 0 < r) (y : Fin n → ℝ) :
    y ∈ r • cube n m ↔ ∀ i, 0 ≤ y i ∧ y i ≤ r * m := by
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hr.ne', cube]
  simp only [mem_pi, mem_univ, true_implies, Pi.smul_apply, smul_eq_mul, mem_Icc]
  refine forall_congr' fun i => ?_
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨?_, ?_⟩
    · have := mul_nonneg hr.le h0; rwa [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul] at this
    · have := mul_le_mul_of_nonneg_left h1 hr.le
      rwa [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul] at this
  · rintro ⟨h0, h1⟩
    refine ⟨mul_nonneg (inv_nonneg.2 hr.le) h0, ?_⟩
    rw [inv_mul_le_iff₀ hr]; exact h1

/-- **The covering radius of `[0, m]^n` is `1/m`** (for `n, m ≥ 1`). -/
theorem coveringRadius_cube (hn : 0 < n) {m : ℕ} (hm : 1 ≤ m) :
    coveringRadius (cube n m) = 1 / m := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hmem : 1 / (m : ℝ) ∈ coveringSet (cube n m) := by
    refine ⟨by positivity, fun y => ?_⟩
    refine ⟨fun i => (⌊y i⌋ : ℝ), (mem_standardIntegerLattice_iff n _).2
      ⟨fun i => ⌊y i⌋, fun i => rfl⟩, ?_⟩
    rw [mem_smul_cube_iff (by positivity)]
    intro i
    simp only [Pi.sub_apply, one_div, inv_mul_cancel₀ hmpos.ne']
    exact ⟨by linarith [Int.floor_le (y i)], by linarith [Int.lt_floor_add_one (y i)]⟩
  have hlow : ∀ r ∈ coveringSet (cube n m), 1 / (m : ℝ) ≤ r := by
    rintro r ⟨hr0, hr⟩
    by_contra hlt
    push Not at hlt
    have hrm : r * m < 1 := by rwa [lt_div_iff₀ hmpos] at hlt
    set c := (r * m + 1) / 2
    obtain ⟨z, hz, hyz⟩ := hr (fun _ => c)
    rw [mem_smul_cube_iff hr0] at hyz
    obtain ⟨w, hw⟩ := (mem_standardIntegerLattice_iff n z).1 hz
    have h := hyz ⟨0, hn⟩
    simp only [Pi.sub_apply, hw] at h
    have hc0 : r * m < c := by simp only [c]; linarith
    have hc1 : c < 1 := by simp only [c]; linarith
    rcases lt_trichotomy (w ⟨0, hn⟩) 0 with hneg | hzero | hpos
    · have : (w ⟨0, hn⟩ : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hneg
      have hrm0 : 0 ≤ r * m := by positivity
      linarith [h.2]
    · rw [hzero, Int.cast_zero, sub_zero] at h; linarith [h.2]
    · have : (1 : ℝ) ≤ w ⟨0, hn⟩ := by exact_mod_cast hpos
      linarith [h.1]
  exact le_antisymm (csInf_le ⟨0, fun _ h => h.1.le⟩ hmem)
    (le_csInf ⟨_, hmem⟩ hlow)

/-- **Proposition 1.6 is tight for cubes.** For `K = [0, m]^n`, `m ≥ 1`, both bounds hold with
equality: `G(K) = vol(K)(1 + μ)^n` and `G(int K) = vol(K)(1 - μ)^n`. -/
theorem proposition_1_6_tight_for_cubes (hn : 0 < n) {m : ℕ} (hm : 1 ≤ m) :
    ((DiscreteMinkowski.latticePoints (cube n m) (standardIntegerLattice n)).ncard : ℝ) =
        (volume (cube n m)).toReal * (1 + coveringRadius (cube n m)) ^ n ∧
      ((DiscreteMinkowski.latticePoints (interior (cube n m))
        (standardIntegerLattice n)).ncard : ℝ) =
        (volume (cube n m)).toReal * (1 - coveringRadius (cube n m)) ^ n := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  rw [coveringRadius_cube hn hm, volume_cube, ENNReal.toReal_ofReal (by positivity),
    ncard_latticePoints_cube, ncard_latticePoints_interior_cube hm]
  constructor
  · push_cast
    rw [← mul_pow]
    congr 1
    field_simp
  · rw [Nat.cast_pow, Nat.cast_sub hm, ← mul_pow]
    congr 1
    push_cast
    field_simp

/-- A lattice tile: covering, with interiorly disjoint lattice translates. -/
def IsLatticeTile (K : Set (Fin n → ℝ)) : Prop :=
  (∀ y : Fin n → ℝ, ∃ z ∈ standardIntegerLattice n, y - z ∈ K) ∧
    ∀ z ∈ standardIntegerLattice n, z ≠ 0 → Disjoint (interior K) (z +ᵥ interior K)

/-- A set whose lattice translates cover `ℝ^n` has volume at least `1`. -/
theorem one_le_volume_of_covers {K : Set (Fin n → ℝ)} (hKm : MeasurableSet K)
    (hcov : ∀ y : Fin n → ℝ, ∃ z ∈ standardIntegerLattice n, y - z ∈ K) : 1 ≤ volume K := by
  rw [← lintegral_translateCount hKm, ← volume_unitCubeIco n, ← setLIntegral_one]
  refine lintegral_mono fun x => ?_
  obtain ⟨z, hz, hxz⟩ := hcov x
  have hmem : -z ∈ translateSet K x :=
    ⟨(standardIntegerLattice n).neg_mem hz, by rwa [neg_add_eq_sub]⟩
  have : (1 : ℕ∞) ≤ (translateSet K x).encard := Set.one_le_encard_iff_nonempty.2 ⟨_, hmem⟩
  have h := ENat.toENNReal_le.2 this
  rwa [ENat.toENNReal_one] at h

/-- **A convex lattice tile has volume `1`.** -/
theorem volume_eq_one_of_isLatticeTile {K : Set (Fin n → ℝ)} (hKc : IsCompact K)
    (hKconv : Convex ℝ K) (hK : IsLatticeTile K) : volume K = 1 := by
  refine le_antisymm ?_ (one_le_volume_of_covers hKc.isClosed.measurableSet hK.1)
  rw [← volume_interior_eq hKconv, ← lintegral_translateCount isOpen_interior.measurableSet,
    ← volume_unitCubeIco n, ← setLIntegral_one]
  refine lintegral_mono fun x => ?_
  have hle : (translateSet (interior K) x).encard ≤ 1 := by
    rw [Set.encard_le_one_iff]
    intro z₁ z₂ h₁ h₂
    by_contra hne
    have hd : z₁ - z₂ ∈ standardIntegerLattice n :=
      (standardIntegerLattice n).sub_mem h₁.1 h₂.1
    refine (hK.2 _ hd (sub_ne_zero.2 hne)).le_bot ⟨h₁.2, ?_⟩
    refine ⟨z₂ + x, h₂.2, ?_⟩
    change (z₁ - z₂) + (z₂ + x) = z₁ + x
    abel
  have h := ENat.toENNReal_le.2 hle
  rwa [ENat.toENNReal_one] at h

/-- **A convex lattice tile has covering radius `1`.** -/
theorem coveringRadius_eq_one_of_isLatticeTile (hn : 0 < n) {K : Set (Fin n → ℝ)}
    (hKc : IsCompact K) (hKconv : Convex ℝ K) (hK : IsLatticeTile K) :
    coveringRadius K = 1 := by
  have hdim : finrank ℝ (Fin n → ℝ) = n := Module.finrank_fin_fun ℝ
  have hvol := volume_eq_one_of_isLatticeTile hKc hKconv hK
  have hone : (1 : ℝ) ∈ coveringSet K := ⟨one_pos, fun y => by
    obtain ⟨z, hz, h⟩ := hK.1 y; exact ⟨z, hz, by rwa [one_smul]⟩⟩
  refine le_antisymm (csInf_le ⟨0, fun _ h => h.1.le⟩ hone)
    (le_csInf ⟨1, hone⟩ fun r ⟨hr0, hr⟩ => ?_)
  have h1 := one_le_volume_of_covers ((hKc.smul r).isClosed.measurableSet) hr
  rw [Measure.addHaar_smul_of_nonneg volume hr0.le, hdim, hvol, mul_one] at h1
  have : (1 : ℝ) ≤ r ^ n := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
    rwa [ENNReal.toReal_one, ENNReal.toReal_ofReal (by positivity)] at this
  by_contra hlt
  push Not at hlt
  have := pow_lt_one₀ hr0.le hlt hn.ne'
  linarith

/-- **Scaling the covering radius:** `μ(rK) = μ(K)/r` for `r > 0`. -/
theorem coveringRadius_smul {K : Set (Fin n → ℝ)} {r : ℝ} (hr : 0 < r) :
    coveringRadius (r • K) = coveringRadius K / r := by
  have hset : coveringSet (r • K) = r⁻¹ • coveringSet K := by
    ext s
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hr.ne'), inv_inv, smul_eq_mul]
    simp only [coveringSet, mem_setOf_eq, smul_smul]
    constructor
    · rintro ⟨hs, h⟩; exact ⟨mul_pos hr hs, by simpa [mul_comm] using h⟩
    · rintro ⟨hs, h⟩
      exact ⟨pos_of_mul_pos_right hs hr.le, by simpa [mul_comm] using h⟩
  rw [coveringRadius, hset, Real.sInf_smul_of_nonneg (inv_nonneg.2 hr.le), smul_eq_mul,
    coveringRadius, div_eq_inv_mul]

/-- **The lattice-tile sandwich.** For a convex lattice tile `K` and `r ≥ 1`,
`(r-1)^n ≤ G(int(rK)) ≤ G(rK) ≤ (r+1)^n`. -/
theorem lattice_tile_sandwich (hn : 0 < n) {K : Set (Fin n → ℝ)} (hKc : IsCompact K)
    (hKb : DiscreteMinkowski.IsPaperConvexBody K) (hK : IsLatticeTile K) {r : ℝ} (hr : 1 ≤ r) :
    (r - 1) ^ n ≤
        ((DiscreteMinkowski.latticePoints (interior (r • K)) (standardIntegerLattice n)).ncard : ℝ) ∧
      ((DiscreteMinkowski.latticePoints (interior (r • K)) (standardIntegerLattice n)).ncard : ℝ) ≤
        ((DiscreteMinkowski.latticePoints (r • K) (standardIntegerLattice n)).ncard : ℝ) ∧
      ((DiscreteMinkowski.latticePoints (r • K) (standardIntegerLattice n)).ncard : ℝ) ≤
        (r + 1) ^ n := by
  have hdim : finrank ℝ (Fin n → ℝ) = n := Module.finrank_fin_fun ℝ
  have hr0 : 0 < r := by linarith
  have hrKc : IsCompact (r • K) := hKc.smul r
  have hrKb : DiscreteMinkowski.IsPaperConvexBody (r • K) := by
    refine ⟨hKb.1.smul₀ r, hKb.2.1.smul r, ?_⟩
    obtain ⟨x, hx⟩ := hKb.2.2
    refine ⟨r • x, ?_⟩
    rw [interior_smul₀ hr0.ne']
    exact smul_mem_smul_set hx
  have hvol : (volume (r • K)).toReal = r ^ n := by
    rw [Measure.addHaar_smul_of_nonneg volume hr0.le, hdim,
      volume_eq_one_of_isLatticeTile hKc hKb.2.1 hK, mul_one,
      ENNReal.toReal_ofReal (by positivity)]
  have hμ : coveringRadius (r • K) = 1 / r := by
    rw [coveringRadius_smul hr0, coveringRadius_eq_one_of_isLatticeTile hn hKc hKb.2.1 hK]
  have hμ1 : coveringRadius (r • K) ≤ 1 := by
    rw [hμ, div_le_one hr0]; exact hr
  refine ⟨?_, ?_, ?_⟩
  · have := proposition_1_6_lower hrKc hrKb hμ1
    rw [hvol, hμ, ← mul_pow] at this
    convert this using 2
    field_simp
  · exact_mod_cast Set.ncard_le_ncard (Set.inter_subset_inter_left _ interior_subset)
      (DiscreteMinkowski.finite_inter_lattice hrKc.isBounded _)
  · have := proposition_1_6_upper hrKc hrKb
    rw [hvol, hμ, ← mul_pow] at this
    convert this using 2
    field_simp

end

end LatticeVolumeInterpolation
