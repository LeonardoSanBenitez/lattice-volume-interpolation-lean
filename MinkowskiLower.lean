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

variable {n : ℕ}

/-- Independent integer vectors have determinant at least `1` in absolute value. -/
theorem one_le_abs_det_of_lattice {v : Fin n → (Fin n → ℝ)} (hv : LinearIndependent ℝ v)
    (hvΛ : ∀ i, v i ∈ standardIntegerLattice n) : 1 ≤ |(Matrix.of v).det| := by
  choose z hz using fun i => (mem_standardIntegerLattice_iff n (v i)).1 (hvΛ i)
  have hV : Matrix.of v = (Matrix.of z).map (Int.castRingHom ℝ) := by
    ext i j; simp [hz i j]
  have hunit : IsUnit (Matrix.of v) := Matrix.linearIndependent_rows_iff_isUnit.1 hv
  have hdet0 : (Matrix.of v).det ≠ 0 := (Matrix.isUnit_iff_isUnit_det _).1 hunit |>.ne_zero
  have hdz : (Matrix.of v).det = ((Matrix.of z).det : ℝ) := by
    rw [hV]
    have := (RingHom.map_det (Int.castRingHom ℝ) (Matrix.of z)).symm
    simpa using this
  rw [hdz] at hdet0 ⊢
  have hz0 : (Matrix.of z).det ≠ 0 := fun h => hdet0 (by rw [h, Int.cast_zero])
  rw [← Int.cast_abs]
  exact_mod_cast Int.one_le_abs hz0

/-- **Minkowski's second theorem, lower bound** (Eq. (1.2)):
`vol(K) ≥ (1/n!) ∏_{i=1}^n 2/λ_i(K)`. -/
theorem minkowski_second_theorem_lower {K : Set (Fin n → ℝ)} (hKcpt : IsCompact K)
    (hKb : DiscreteMinkowski.IsPaperConvexBody K) :
    ENNReal.ofReal ((1 / (n.factorial : ℝ)) * ∏ i : Fin n,
        2 / DiscreteMinkowski.successiveMinimum K (standardIntegerLattice n) (i.1 + 1)) ≤
      volume K := by
  classical
  have hdim : finrank ℝ (Fin n → ℝ) = n := Module.finrank_fin_fun ℝ
  have hKne : K.Nonempty := hKb.2.2.mono interior_subset
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using volume_ge_of_unit_segments 0 K hKcpt hKb.2.1 hKne (fun i => i.elim0)
  set lam : Fin n → ℝ := fun i =>
    DiscreteMinkowski.successiveMinimum K (standardIntegerLattice n) (i.1 + 1) with hlam
  have hpos : ∀ i, 0 < lam i := fun i =>
    DiscreteMinkowski.successiveMinimum_pos hKb (by omega) (by rw [hdim]; exact i.2)
  set v : Fin n → (Fin n → ℝ) := fun k =>
    DiscreteMinkowski.flagVector K (standardIntegerLattice n) k.1 with hv
  have hvΛ : ∀ k, v k ∈ standardIntegerLattice n := fun k =>
    DiscreteMinkowski.flagVector_mem k.1
      (DiscreteMinkowski.greedyChoice_flagSpan hKb (by rw [hdim]; exact k.2))
  have hvind : LinearIndependent ℝ v := linearIndependent_flagVector hKb
  -- the segments realizing the minima
  have hDc : IsCompact (DiscreteMinkowski.halfDifferenceBody K) := by
    rw [DiscreteMinkowski.halfDifferenceBody_apply]
    have hsub : K - K = (fun p : (Fin n → ℝ) × (Fin n → ℝ) => p.1 - p.2) '' (K ×ˢ K) := by
      rw [Set.image_prod]; rfl
    rw [hsub]
    exact ((hKcpt.prod hKcpt).image (by fun_prop)).smul _
  have hab : ∀ k, ∃ a ∈ K, ∃ b ∈ K, v k = lam k • ((2 : ℝ)⁻¹ • (a - b)) := by
    intro k
    have hg := gauge_flagVector_le_successiveMinimum (Λ := standardIntegerLattice n) hKb
      (by rw [hdim]; exact k.2)
    have hcl : v k ∈ closure (lam k • DiscreteMinkowski.halfDifferenceBody K) :=
      (DiscreteMinkowski.mem_closure_smul_iff_gauge_le hKb (hpos k) (v k)).2 hg
    rw [(hDc.smul (lam k)).isClosed.closure_eq] at hcl
    obtain ⟨d, hd, hdv⟩ := mem_smul_set.1 hcl
    rw [DiscreteMinkowski.halfDifferenceBody_apply] at hd
    obtain ⟨w, ⟨a, ha, b, hb, rfl⟩, rfl⟩ := mem_smul_set.1 hd
    exact ⟨a, ha, b, hb, hdv.symm⟩
  choose a ha b hb hvab using hab
  set d : Fin n → (Fin n → ℝ) := fun k => a k - b k with hd
  have hdv : ∀ k, d k = (2 / lam k) • v k := by
    intro k
    rw [hvab k, smul_smul, smul_smul, hd]
    have := (hpos k).ne'
    field_simp
    simp
  have hdind : LinearIndependent ℝ d := by
    have := hvind.units_smul (fun k => Units.mk0 (2 / lam k) (div_ne_zero two_ne_zero
      (hpos k).ne'))
    convert this using 1
    funext k; rw [hdv k]; rfl
  -- map the segments to the unit axis segments
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set Bd := basisOfLinearIndependentOfCardEqFinrank hdind (by rw [Fintype.card_fin, hdim])
  have hBd : ∀ k, Bd k = d k := fun k => by simp [Bd]
  set φ := Bd.equivFun
  have hφd : ∀ k, φ (d k) = Pi.single k 1 := by
    intro k; rw [← hBd, Basis.equivFun_apply, Basis.repr_self, Finsupp.single_eq_pi_single]
  set C := φ '' K
  have hC := volume_ge_of_unit_segments n C (hKcpt.image φ.toContinuousLinearEquiv.continuous)
    (hKb.2.1.linear_image φ.toLinearMap) (hKne.image _) (fun i => ⟨φ (b i), fun t ht => ?seg⟩)
  case seg =>
    refine ⟨b i + t • d i, hKb.2.1 (ha i) (hb i) ht.1 (show (0 : ℝ) ≤ 1 - t by
      linarith [ht.2]) (by ring) |> fun h => ?_, ?_⟩
    · convert h using 1; simp only [hd]; module
    · rw [map_add, map_smul, hφd]
  -- volumes
  have hvolC : volume C = ENNReal.ofReal |LinearMap.det (φ : (Fin n → ℝ) →ₗ[ℝ] _)| * volume K :=
    Measure.addHaar_image_linearMap volume _ K
  -- `|det φ| ⋅ |det d| = 1` and `|det d| = ∏ (2/λ) |det v|`
  set Md := Matrix.of d
  have hdetsymm : LinearMap.det (φ.symm : (Fin n → ℝ) →ₗ[ℝ] _) = Md.det := by
    rw [← LinearMap.det_toMatrix' (φ.symm : (Fin n → ℝ) →ₗ[ℝ] _), ← Matrix.det_transpose]
    congr 1
    ext i j
    simp only [Matrix.transpose_apply, LinearMap.toMatrix'_apply, LinearEquiv.coe_coe]
    rw [show (Pi.single i 1 : Fin n → ℝ) = φ (d i) from (hφd i).symm,
      LinearEquiv.symm_apply_apply]
    rfl
  have hprod := LinearEquiv.det_mul_det_symm φ
  rw [hdetsymm] at hprod
  have hMd : Md = Matrix.diagonal (fun k => 2 / lam k) * Matrix.of v := by
    ext i j
    simp [Md, hdv i, Matrix.diagonal_mul]
  have hdetMd : Md.det = (∏ k, 2 / lam k) * (Matrix.of v).det := by
    rw [hMd, Matrix.det_mul, Matrix.det_diagonal]
  have hv1 := one_le_abs_det_of_lattice hvind hvΛ
  have hP : 0 < ∏ k, 2 / lam k := Finset.prod_pos fun k _ => div_pos two_pos (hpos k)
  have habsd : ∏ k, 2 / lam k ≤ |Md.det| := by
    rw [hdetMd, abs_mul, abs_of_pos hP]
    exact le_mul_of_one_le_right hP.le hv1
  have hdetφ : |LinearMap.det (φ : (Fin n → ℝ) →ₗ[ℝ] _)| = |Md.det|⁻¹ := by
    have h := congrArg abs hprod
    rw [abs_mul, abs_one] at h
    exact eq_inv_of_mul_eq_one_left h
  -- combine
  rw [hvolC, hdetφ] at hC
  have hdetpos : 0 < |Md.det| := hP.trans_le habsd
  have hKtop : volume K ≠ ⊤ := hKcpt.measure_lt_top.ne
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKtop) hC
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (by positivity)] at hreal
  rw [← ENNReal.ofReal_toReal hKtop]
  refine ENNReal.ofReal_le_ofReal ?_
  have hK0 : 0 ≤ (volume K).toReal := ENNReal.toReal_nonneg
  calc 1 / (n.factorial : ℝ) * ∏ k, 2 / lam k ≤ 1 / (n.factorial : ℝ) * |Md.det| :=
        mul_le_mul_of_nonneg_left habsd (by positivity)
    _ ≤ |Md.det|⁻¹ * (volume K).toReal * |Md.det| :=
        mul_le_mul_of_nonneg_right hreal hdetpos.le
    _ = (volume K).toReal := by field_simp

end

end LatticeVolumeInterpolation
