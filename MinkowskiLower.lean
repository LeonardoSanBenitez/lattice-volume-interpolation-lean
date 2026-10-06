import ShakingIterate
import JoinVolume
import TheoremThreeOne

/-!
# The lower half of Minkowski's second theorem

Catalog item `minkowski_second_theorem`, Eq. (1.2), lower bound:
`vol(K) ≥ (1/n!) ∏_{i=1}^n 2/λ_i(K)` for `K ∈ K^n`.

The paper (Sec. 1, after Eq. (1.2)): "the lower bound can also be proved by an inclusion
argument, similar to the symmetric case: one considers the convex hull of the `n` segments in
`K` that realize the `λ_i(K)`" (citing Henk, Henze and Hernández Cifre, Remark 1.1). The
segments: `v_i = (λ_i/2)(a_i - b_i)` with `a_i, b_i ∈ K` and `v_i` independent lattice vectors,
so `K` contains `[b_i, a_i]`, of direction `d_i = (2/λ_i) v_i`.

The volume estimate used is `vol(C) ≥ |det(d_1, ..., d_n)| / n!` for a compact convex `C`
containing segments `[b_i, b_i + d_i]` with independent `d_i`. After a linear map sending
`d_i` to `e_i` it reads `vol(C) ≥ 1/n!` for unit segments along the axes
(`volume_ge_of_unit_segments`), proved by induction on `n`: shaking `C` along the last axis
keeps its volume and makes it contain both its projection `D` (at height `0`) and a vertical
unit segment, and the join bound (`join_volume_lower_bound'`) gives `vol(C) ≥ vol(D)/n`.
Then `|det(d_i)| = ∏ (2/λ_i) |det(v_i)| ≥ ∏ (2/λ_i)`, because independent integer vectors have
a non-zero integer determinant.
-/

open MeasureTheory Set Module
open scoped ENNReal Pointwise

namespace LatticeVolumeInterpolation

noncomputable section

/-- The point with last coordinate `t` over `y`. -/
abbrev lastInsert {m : ℕ} (t : ℝ) (y : Fin m → ℝ) : Fin (m + 1) → ℝ :=
  Fin.insertNth (Fin.last m) t y

/-- Forgetting the last coordinate. -/
abbrev lastDrop {m : ℕ} (x : Fin (m + 1) → ℝ) : Fin m → ℝ :=
  fun k => x ((Fin.last m).succAbove k)

theorem lastInsert_lastDrop {m : ℕ} (x : Fin (m + 1) → ℝ) (t : ℝ) :
    lastInsert t (lastDrop x) = Function.update x (Fin.last m) t := by
  funext k
  refine Fin.lastCases ?_ (fun k => ?_) k
  · simp [lastInsert]
  · have hne : k.castSucc ≠ Fin.last m := Fin.castSucc_ne_last k
    simp only [lastInsert, lastDrop, ← Fin.succAbove_last, Fin.insertNth_apply_succAbove]
    rw [Fin.succAbove_last, Function.update_of_ne hne]

/-- **Unit segments along the axes force volume `1/n!`.** -/
theorem volume_ge_of_unit_segments :
    ∀ (m : ℕ) (C : Set (Fin m → ℝ)), IsCompact C → Convex ℝ C → C.Nonempty →
      (∀ i : Fin m, ∃ p, ∀ t ∈ Icc (0 : ℝ) 1, p + t • (Pi.single i (1 : ℝ) : Fin m → ℝ) ∈ C) →
      ENNReal.ofReal (1 / (m.factorial : ℝ)) ≤ volume C
  | 0, C, _, _, hne, _ => by
    have hC : C = univ := by
      obtain ⟨x, hx⟩ := hne
      ext y; simp only [mem_univ, iff_true]; rwa [Subsingleton.elim y x]
    rw [hC, volume_pi, Measure.pi_of_empty]; simp
  | m + 1, C, hCc, hCconv, hne, hseg => by
    set j := Fin.last m
    -- the projection `D` and the induction hypothesis
    set D := lastDrop '' C with hD
    have hdrop : Continuous (lastDrop (m := m)) := by fun_prop
    have hDc : IsCompact D := hCc.image hdrop
    have hDconv : Convex ℝ D := by
      have : lastDrop (m := m) = (LinearMap.funLeft ℝ ℝ (j.succAbove) : _) := rfl
      rw [hD, this]; exact hCconv.linear_image _
    have hDne : D.Nonempty := hne.image _
    have hDseg : ∀ i : Fin m, ∃ p, ∀ t ∈ Icc (0 : ℝ) 1,
        p + t • (Pi.single i (1 : ℝ) : Fin m → ℝ) ∈ D := by
      intro i
      obtain ⟨p, hp⟩ := hseg (j.succAbove i)
      refine ⟨lastDrop p, fun t ht => ⟨_, hp t ht, ?_⟩⟩
      funext k
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      congr 1
      by_cases h : k = i
      · subst h; simp [j, Fin.succAbove_last]
      · rw [Pi.single_eq_of_ne ((Fin.succAbove_right_injective).ne h),
          Pi.single_eq_of_ne h]
    have hIH := volume_ge_of_unit_segments m D hDc hDconv hDne hDseg
    -- the shaken body and its vertical unit segment
    set C' := coordShaking C j
    have hC'c : IsCompact C' := isCompact_coordShaking hCc j
    have hC'conv : Convex ℝ C' := convex_coordShaking hCc hCconv j
    have hvol : volume C' = volume C := volume_coordShaking hCc hCconv j
    obtain ⟨p, hp⟩ := hseg j
    set y₀ := lastDrop p
    have hfib : ∀ t ∈ Icc (0 : ℝ) 1, p j + t ∈ fibre C j p := by
      intro t ht
      have := hp t ht
      simp only [fibre, mem_setOf_eq]
      convert this using 1
      funext k
      by_cases h : k = j
      · subst h; simp [add_comm]
      · simp [Function.update_of_ne h, Pi.single_eq_of_ne h]
    have hlen : 1 ≤ fibreLength C j p := by
      have := sub_le_fibreLength hCc (hfib 0 ⟨le_rfl, zero_le_one⟩) (hfib 1 ⟨zero_le_one, le_rfl⟩)
      linarith
    -- product coordinates: fibre first, base second, base point moved to `0`
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) j
    have hpres : MeasurePreserving e volume (volume.prod volume) :=
      measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => (volume : Measure ℝ)) j
    have hsymm : ∀ (t : ℝ) (y : Fin m → ℝ), e.symm (t, y) = lastInsert t y := fun _ _ => rfl
    set Cp : Set (ℝ × (Fin m → ℝ)) := (fun q => q + ((0 : ℝ), y₀)) ⁻¹' (e.symm ⁻¹' C')
    have hCpm : MeasurableSet Cp :=
      (hC'c.isClosed.measurableSet.preimage e.symm.measurable).preimage (measurable_add_const _)
    have hCpvol : (volume.prod volume) Cp = volume C := by
      rw [measure_preimage_add_right, ← hpres.measure_preimage
        (hC'c.isClosed.measurableSet.preimage e.symm.measurable).nullMeasurableSet]
      have : e ⁻¹' (e.symm ⁻¹' C') = C' := by ext x; simp
      rw [this, hvol]
    have hCpconv : Convex ℝ Cp := by
      intro q hq r hr a b ha hb hab
      simp only [Cp, mem_preimage, hsymm, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
        Prod.smul_snd, Prod.fst_add] at hq hr ⊢
      have h := hC'conv hq hr ha hb hab
      convert h using 1
      funext k
      refine Fin.lastCases ?_ (fun k => ?_) k
      · simp [lastInsert]
      · simp only [lastInsert, ← Fin.succAbove_last, Fin.insertNth_apply_succAbove,
          Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        have : y₀ k = (a + b) * y₀ k := by rw [hab, one_mul]
        linarith
    -- the two pieces of the join
    set B : Set (Fin m → ℝ) := (fun y => y - y₀) '' D
    have hBc : IsCompact B := hDc.image (by fun_prop)
    have hBvol : volume B = volume D := by
      have : (fun y => y - y₀) '' D = (-y₀) +ᵥ D := by
        rw [← Set.image_vadd]; congr 1; funext y; rw [vadd_eq_add, sub_eq_add_neg, add_comm]
      change volume ((fun y => y - y₀) '' D) = volume D
      rw [this, measure_vadd]
    have hAC : ∀ a ∈ Icc (0 : ℝ) 1, (a, (0 : Fin m → ℝ)) ∈ Cp := by
      intro a ha
      simp only [Cp, mem_preimage, Prod.mk_add_mk, add_zero, zero_add, hsymm]
      rw [show lastInsert a y₀ = Function.update p j a from lastInsert_lastDrop p a]
      refine ⟨?_, ?_, ?_⟩
      · rw [fibre_update]; exact ⟨_, hfib 0 ⟨le_rfl, zero_le_one⟩⟩
      · simpa using ha.1
      · rw [fibreLength_update]; simp only [Function.update_self]; linarith [ha.2]
    have hBC : ∀ b ∈ B, ((0 : ℝ), b) ∈ Cp := by
      rintro _ ⟨y, ⟨x, hx, rfl⟩, rfl⟩
      simp only [Cp, mem_preimage, Prod.mk_add_mk, add_zero, sub_add_cancel, hsymm]
      rw [lastInsert_lastDrop]
      exact update_zero_mem_coordShaking hCc j hx
    have hjoin := join_volume_lower_bound' (volume : Measure ℝ) (volume : Measure (Fin m → ℝ))
      (k := 1) (m := m) (by simp) (by simp) hBc hCpconv hCpm hAC hBC
    rw [hCpvol, Real.volume_Icc, sub_zero, ENNReal.ofReal_one, one_mul, hBvol] at hjoin
    calc ENNReal.ofReal (1 / ((m + 1).factorial : ℝ))
        = ENNReal.ofReal (1 / (m.factorial : ℝ)) *
            ENNReal.ofReal (((1 : ℕ).factorial * m.factorial : ℝ) / ((1 + m).factorial : ℝ)) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [Nat.factorial_one, Nat.cast_one, one_mul, add_comm 1 m]
          have : (m.factorial : ℝ) ≠ 0 := by positivity
          field_simp
      _ ≤ volume D * ENNReal.ofReal
            (((1 : ℕ).factorial * m.factorial : ℝ) / ((1 + m).factorial : ℝ)) :=
          mul_le_mul_left hIH _
      _ ≤ volume C := hjoin

end

end LatticeVolumeInterpolation
