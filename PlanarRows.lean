import TheoremOneFour

/-!
# Horizontal rows of a planar convex body

Infrastructure for Proposition 1.5 (Sec. 5): for a compact convex `P ⊆ ℝ^2` with non-empty
interior, the horizontal line at height `t` meets `P` in the interval `[l(t), r(t)]`
(`rowLo`, `rowHi`) for `t ∈ [y_min, y_max]` (`yLo`, `yHi`). The right end `r` is concave and the
left end `l` convex; `vol(P) = ∫ (r - l)` by Fubini; the interior of `P` is
`{y_min < x_2 < y_max, l(x_2) < x_1 < r(x_2)}`; and the lattice points of `P` and of its interior
are counted row by row.
-/

open Set MeasureTheory

namespace LatticeVolumeInterpolation

noncomputable section

/-- The left end `l(t)` of the row of `P` at height `t`. -/
def rowLo (P : Set (Fin 2 → ℝ)) (t : ℝ) : ℝ := sInf (hsec P t)

/-- The right end `r(t)` of the row of `P` at height `t`. -/
def rowHi (P : Set (Fin 2 → ℝ)) (t : ℝ) : ℝ := sSup (hsec P t)

/-- The lowest height `y_min` of `P`. -/
def yLo (P : Set (Fin 2 → ℝ)) : ℝ := sInf ((fun x : Fin 2 → ℝ => x 1) '' P)

/-- The highest height `y_max` of `P`. -/
def yHi (P : Set (Fin 2 → ℝ)) : ℝ := sSup ((fun x : Fin 2 → ℝ => x 1) '' P)

variable {P : Set (Fin 2 → ℝ)}

theorem pt_mem_iff_mem_hsec {s t : ℝ} : pt s t ∈ P ↔ s ∈ hsec P t := Iff.rfl

theorem convex_hsec (hv : Convex ℝ P) (t : ℝ) : Convex ℝ (hsec P t) := by
  intro s₁ h₁ s₂ h₂ a b ha hb hab
  have := hv h₁ h₂ ha hb hab
  rw [pt_comb] at this
  show pt (a • s₁ + b • s₂) t ∈ P
  have ht : a * t + b * t = t := by rw [← add_mul, hab, one_mul]
  rw [ht] at this
  simpa using this

theorem image_snd_eq_Icc (hc : IsCompact P) (hv : Convex ℝ P) (hne : P.Nonempty) :
    (fun x : Fin 2 → ℝ => x 1) '' P = Icc (yLo P) (yHi P) := by
  have hcomp : IsCompact ((fun x : Fin 2 → ℝ => x 1) '' P) := hc.image (continuous_apply 1)
  have hconv : Convex ℝ ((fun x : Fin 2 → ℝ => x 1) '' P) := by
    have := hv.linear_image (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1)
    simpa using this
  have hne' : ((fun x : Fin 2 → ℝ => x 1) '' P).Nonempty := hne.image _
  refine Subset.antisymm
    (fun t ht => ⟨csInf_le hcomp.bddBelow ht, le_csSup hcomp.bddAbove ht⟩) ?_
  exact (convex_iff_ordConnected.1 hconv).out (hcomp.sInf_mem hne') (hcomp.sSup_mem hne')

theorem hsec_nonempty_iff (hc : IsCompact P) (hv : Convex ℝ P) (hne : P.Nonempty) (t : ℝ) :
    (hsec P t).Nonempty ↔ t ∈ Icc (yLo P) (yHi P) := by
  rw [← image_snd_eq_Icc hc hv hne]
  constructor
  · rintro ⟨s, hs⟩; exact ⟨pt s t, hs, by simp⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x 0, show pt (x 0) (x 1) ∈ P by rw [pt_eta]; exact hx⟩

theorem yLo_le_yHi (hc : IsCompact P) (hv : Convex ℝ P) (hne : P.Nonempty) :
    yLo P ≤ yHi P := by
  obtain ⟨x, hx⟩ := hne
  have : x 1 ∈ Icc (yLo P) (yHi P) := by
    rw [← image_snd_eq_Icc hc hv ⟨x, hx⟩]; exact ⟨x, hx, rfl⟩
  exact this.1.trans this.2

theorem mem_Icc_of_mem (hc : IsCompact P) (hv : Convex ℝ P) {x : Fin 2 → ℝ} (hx : x ∈ P) :
    x 1 ∈ Icc (yLo P) (yHi P) := by
  rw [← image_snd_eq_Icc hc hv ⟨x, hx⟩]; exact ⟨x, hx, rfl⟩

theorem hsec_eq_Icc_rows (hc : IsCompact P) (hv : Convex ℝ P) {t : ℝ}
    (ht : (hsec P t).Nonempty) : hsec P t = Icc (rowLo P t) (rowHi P t) := by
  have hcomp := isCompact_hsec hc t
  refine Subset.antisymm
    (fun s hs => ⟨csInf_le hcomp.bddBelow hs, le_csSup hcomp.bddAbove hs⟩) ?_
  exact (convex_iff_ordConnected.1 (convex_hsec hv t)).out (hcomp.sInf_mem ht) (hcomp.sSup_mem ht)

theorem pt_rowHi_mem (hc : IsCompact P) {t : ℝ} (ht : (hsec P t).Nonempty) :
    pt (rowHi P t) t ∈ P := (isCompact_hsec hc t).sSup_mem ht

theorem pt_rowLo_mem (hc : IsCompact P) {t : ℝ} (ht : (hsec P t).Nonempty) :
    pt (rowLo P t) t ∈ P := (isCompact_hsec hc t).sInf_mem ht

theorem le_rowHi (hc : IsCompact P) {s t : ℝ} (h : pt s t ∈ P) : s ≤ rowHi P t :=
  le_csSup (isCompact_hsec hc t).bddAbove h

theorem rowLo_le (hc : IsCompact P) {s t : ℝ} (h : pt s t ∈ P) : rowLo P t ≤ s :=
  csInf_le (isCompact_hsec hc t).bddBelow h

theorem rowLo_le_rowHi (hc : IsCompact P) {t : ℝ} (ht : (hsec P t).Nonempty) :
    rowLo P t ≤ rowHi P t :=
  rowLo_le hc (pt_rowHi_mem hc ht)

/-- **`r` is concave** on `[y_min, y_max]`. -/
theorem concaveOn_rowHi (hc : IsCompact P) (hv : Convex ℝ P) (hne : P.Nonempty) :
    ConcaveOn ℝ (Icc (yLo P) (yHi P)) (rowHi P) := by
  refine ⟨convex_Icc _ _, fun t₁ ht₁ t₂ ht₂ a b ha hb hab => ?_⟩
  have h₁ := pt_rowHi_mem hc ((hsec_nonempty_iff hc hv hne t₁).2 ht₁)
  have h₂ := pt_rowHi_mem hc ((hsec_nonempty_iff hc hv hne t₂).2 ht₂)
  have hcomb := hv h₁ h₂ ha hb hab
  rw [pt_comb] at hcomb
  simp only [smul_eq_mul]
  exact le_rowHi hc hcomb

/-- **`l` is convex** on `[y_min, y_max]`. -/
theorem convexOn_rowLo (hc : IsCompact P) (hv : Convex ℝ P) (hne : P.Nonempty) :
    ConvexOn ℝ (Icc (yLo P) (yHi P)) (rowLo P) := by
  refine ⟨convex_Icc _ _, fun t₁ ht₁ t₂ ht₂ a b ha hb hab => ?_⟩
  have h₁ := pt_rowLo_mem hc ((hsec_nonempty_iff hc hv hne t₁).2 ht₁)
  have h₂ := pt_rowLo_mem hc ((hsec_nonempty_iff hc hv hne t₂).2 ht₂)
  have hcomb := hv h₁ h₂ ha hb hab
  rw [pt_comb] at hcomb
  simp only [smul_eq_mul]
  exact rowLo_le hc hcomb

/-- The row width `r - l` is concave. -/
theorem concaveOn_rowWidth (hc : IsCompact P) (hv : Convex ℝ P) (hne : P.Nonempty) :
    ConcaveOn ℝ (Icc (yLo P) (yHi P)) (fun t => rowHi P t - rowLo P t) :=
  (concaveOn_rowHi hc hv hne).sub (convexOn_rowLo hc hv hne)

/-- **Fubini**: `vol(P) = ∫_{y_min}^{y_max} (r - l)`. -/
theorem volume_eq_integral_rows (hc : IsCompact P) (hv : Convex ℝ P) (hne : P.Nonempty) :
    volume P = ENNReal.ofReal (∫ t in (yLo P)..(yHi P), (rowHi P t - rowLo P t)) := by
  have hT := yLo_le_yHi hc hv hne
  set e := MeasurableEquiv.finTwoArrow (α := ℝ)
  have hpres : MeasurePreserving e volume (volume.prod volume) :=
    volume_preserving_finTwoArrow ℝ
  have hAm : MeasurableSet P := hc.isClosed.measurableSet
  have hpre : e ⁻¹' (e.symm ⁻¹' P) = P := by ext x; simp
  have hmeas : MeasurableSet (e.symm ⁻¹' P) := hAm.preimage e.symm.measurable
  conv_lhs => rw [← hpre]
  rw [hpres.measure_preimage hmeas.nullMeasurableSet, Measure.prod_apply_symm hmeas]
  have hfib : ∀ t : ℝ, volume ((fun s => (s, t)) ⁻¹' (e.symm ⁻¹' P)) =
      (Icc (yLo P) (yHi P)).indicator
        (fun t => ENNReal.ofReal (rowHi P t - rowLo P t)) t := by
    intro t
    have hset : (fun s => (s, t)) ⁻¹' (e.symm ⁻¹' P) = hsec P t := by
      ext s; exact Iff.rfl
    rw [hset]
    by_cases ht : t ∈ Icc (yLo P) (yHi P)
    · rw [indicator_of_mem ht,
        hsec_eq_Icc_rows hc hv ((hsec_nonempty_iff hc hv hne t).2 ht), Real.volume_Icc]
    · rw [indicator_of_notMem ht, not_nonempty_iff_eq_empty.1
        (fun h => ht ((hsec_nonempty_iff hc hv hne t).1 h)), measure_empty]
  simp_rw [hfib]
  have hconc := concaveOn_rowWidth hc hv hne
  have hint := concave_intervalIntegrable hT hconc
  rw [lintegral_indicator measurableSet_Icc, ← ofReal_integral_eq_lintegral_ofReal,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT]
  · exact (intervalIntegrable_iff_integrableOn_Icc_of_le hT).1 hint
  · refine (ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ fun t ht => ?_)
    exact sub_nonneg.2 (rowLo_le_rowHi hc ((hsec_nonempty_iff hc hv hne t).2 ht))

theorem pt_mem_ball {x : Fin 2 → ℝ} {ε : ℝ} (hε : 0 < ε) {a b : ℝ} (ha : |a - x 0| < ε)
    (hb : |b - x 1| < ε) : pt a b ∈ Metric.ball x ε := by
  rw [Metric.mem_ball, dist_pi_lt_iff hε]
  intro i
  fin_cases i
  · simpa [Real.dist_eq] using ha
  · simpa [Real.dist_eq] using hb

/-- **The interior by rows**: `int P = {y_min < x_2 < y_max, l(x_2) < x_1 < r(x_2)}`. -/
theorem mem_interior_iff_rows (hc : IsCompact P) (hv : Convex ℝ P) (hne : P.Nonempty)
    (x : Fin 2 → ℝ) :
    x ∈ interior P ↔
      x 1 ∈ Ioo (yLo P) (yHi P) ∧ rowLo P (x 1) < x 0 ∧ x 0 < rowHi P (x 1) := by
  constructor
  · intro hx
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hx)
    have hδ : 0 < ε / 2 := by positivity
    have hlt : |ε / 2| < ε := by rw [abs_of_pos hδ]; linarith
    have hP : ∀ a b : ℝ, |a| < ε → |b| < ε → pt (x 0 + a) (x 1 + b) ∈ P := fun a b ha hb =>
      hball (pt_mem_ball hε (by simpa using ha) (by simpa using hb))
    have h1 := mem_Icc_of_mem hc hv (hP 0 (ε / 2) (by simpa using hε) hlt)
    have h2 := mem_Icc_of_mem hc hv (hP 0 (-(ε / 2)) (by simpa using hε) (by rwa [abs_neg]))
    have h3 := le_rowHi hc (hP (ε / 2) 0 hlt (by simpa using hε))
    have h4 := rowLo_le hc (hP (-(ε / 2)) 0 (by rwa [abs_neg]) (by simpa using hε))
    simp only [add_zero] at h3 h4
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at h1 h2
    refine ⟨⟨by linarith [h2.1], by linarith [h1.2]⟩, by linarith, by linarith⟩
  · rintro ⟨hy, hl, hr⟩
    have hconcH := (concaveOn_rowHi hc hv hne).continuousOn_interior
    have hconvL := (convexOn_rowLo hc hv hne).continuousOn_interior
    rw [interior_Icc] at hconcH hconvL
    set S1 : Set (Fin 2 → ℝ) := (fun q : Fin 2 → ℝ => q 1) ⁻¹' Ioo (yLo P) (yHi P) with hS1
    have hS1o : IsOpen S1 := isOpen_Ioo.preimage (continuous_apply 1)
    have hmaps : MapsTo (fun q : Fin 2 → ℝ => q 1) S1 (Ioo (yLo P) (yHi P)) := fun q hq => hq
    have hg1 : ContinuousOn (fun q : Fin 2 → ℝ => rowHi P (q 1) - q 0) S1 :=
      (hconcH.comp (continuous_apply 1).continuousOn hmaps).sub
        (continuous_apply 0).continuousOn
    have hg2 : ContinuousOn (fun q : Fin 2 → ℝ => q 0 - rowLo P (q 1)) S1 :=
      (continuous_apply 0).continuousOn.sub
        (hconvL.comp (continuous_apply 1).continuousOn hmaps)
    set U := (S1 ∩ (fun q : Fin 2 → ℝ => rowHi P (q 1) - q 0) ⁻¹' Ioi 0) ∩
      (fun q : Fin 2 → ℝ => q 0 - rowLo P (q 1)) ⁻¹' Ioi 0 with hU
    have hUo : IsOpen U :=
      (hg2.mono inter_subset_left).isOpen_inter_preimage
        (hg1.isOpen_inter_preimage hS1o isOpen_Ioi) isOpen_Ioi
    have hUP : U ⊆ P := by
      rintro q ⟨⟨hq1, hq2⟩, hq3⟩
      simp only [mem_preimage, mem_Ioi, sub_pos] at hq2 hq3
      have hne' := (hsec_nonempty_iff hc hv hne (q 1)).2 (Ioo_subset_Icc_self hq1)
      have : q 0 ∈ hsec P (q 1) := by
        rw [hsec_eq_Icc_rows hc hv hne']; exact ⟨hq3.le, hq2.le⟩
      have := pt_mem_iff_mem_hsec.2 this
      rwa [pt_eta] at this
    exact interior_maximal hUP hUo ⟨⟨hy, by simpa using hr⟩, by simpa using hl⟩

/-- Inside the height range the rows have positive length. -/
theorem rowLo_lt_rowHi (hc : IsCompact P) (hv : Convex ℝ P) (hint : (interior P).Nonempty)
    {t : ℝ} (ht : t ∈ Ioo (yLo P) (yHi P)) : rowLo P t < rowHi P t := by
  have hne : P.Nonempty := hint.mono interior_subset
  obtain ⟨c, hcI⟩ := hint
  obtain ⟨hc1, hcl, hcr⟩ := (mem_interior_iff_rows hc hv hne c).1 hcI
  have hconc := concaveOn_rowWidth hc hv hne
  have hf0 : ∀ s ∈ Icc (yLo P) (yHi P), 0 ≤ rowHi P s - rowLo P s := fun s hs =>
    sub_nonneg.2 (rowLo_le_rowHi hc ((hsec_nonempty_iff hc hv hne s).2 hs))
  have hfc : 0 < rowHi P (c 1) - rowLo P (c 1) := by linarith
  have hmemc : c 1 ∈ Icc (yLo P) (yHi P) := Ioo_subset_Icc_self hc1
  have hle := yLo_le_yHi hc hv hne
  -- `t` lies between `c 1` and an endpoint `e`
  have key : ∀ e ∈ Icc (yLo P) (yHi P), ∀ θ : ℝ, 0 < θ → θ ≤ 1 →
      t = θ * c 1 + (1 - θ) * e → rowLo P t < rowHi P t := by
    intro e he θ hθ0 hθ1 htθ
    have h : θ • (rowHi P (c 1) - rowLo P (c 1)) + (1 - θ) • (rowHi P e - rowLo P e) ≤
        rowHi P (θ • c 1 + (1 - θ) • e) - rowLo P (θ • c 1 + (1 - θ) • e) :=
      hconc.2 hmemc he hθ0.le (by linarith) (by ring)
    simp only [smul_eq_mul] at h
    rw [← htθ] at h
    have h1 := hf0 e he
    have h2 : 0 < θ * (rowHi P (c 1) - rowLo P (c 1)) := mul_pos hθ0 hfc
    have h3 : 0 ≤ (1 - θ) * (rowHi P e - rowLo P e) := mul_nonneg (by linarith) h1
    linarith
  rcases lt_trichotomy t (c 1) with h | h | h
  · have hpos : 0 < c 1 - yLo P := by linarith [ht.1]
    exact key (yLo P) ⟨le_rfl, hle⟩ ((t - yLo P) / (c 1 - yLo P))
      (div_pos (by linarith [ht.1]) hpos) ((div_le_one hpos).2 (by linarith))
      (by field_simp; ring)
  · rw [h]; linarith
  · have hpos : 0 < yHi P - c 1 := by linarith [ht.2]
    exact key (yHi P) ⟨hle, le_rfl⟩ ((yHi P - t) / (yHi P - c 1))
      (div_pos (by linarith [ht.2]) hpos) ((div_le_one hpos).2 (by linarith))
      (by field_simp; ring)

/-! ### Counting lattice points row by row -/

/-- A set described by integer rows: its lattice points are counted row by row. -/
theorem ncard_latticePoints_eq_sum_rows (X : Set (Fin 2 → ℝ)) (J : Finset ℤ) (N : ℤ → Finset ℤ)
    (h : ∀ a b : ℤ, pt (a : ℝ) (b : ℝ) ∈ X ↔ b ∈ J ∧ a ∈ N b) :
    (DiscreteMinkowski.latticePoints X (standardIntegerLattice 2)).ncard =
      ∑ b ∈ J, (N b).card := by
  classical
  set F : (Σ _ : ℤ, ℤ) → (Fin 2 → ℝ) := fun p => pt (p.2 : ℝ) (p.1 : ℝ) with hF
  have hinj : Function.Injective F := by
    rintro ⟨b, a⟩ ⟨b', a'⟩ hab
    have h0 := congrFun hab 0
    have h1 := congrFun hab 1
    simp [hF] at h0 h1
    subst h0; subst h1; rfl
  have hset : DiscreteMinkowski.latticePoints X (standardIntegerLattice 2) =
      ((J.sigma N).image F : Set (Fin 2 → ℝ)) := by
    ext z
    simp only [DiscreteMinkowski.latticePoints_apply, mem_inter_iff, SetLike.mem_coe,
      Finset.coe_image, mem_image, Finset.mem_coe, Finset.mem_sigma]
    constructor
    · rintro ⟨hzX, hzΛ⟩
      obtain ⟨w, hw⟩ := (mem_standardIntegerLattice_iff 2 z).1 hzΛ
      have hz : z = pt (w 0 : ℝ) (w 1 : ℝ) := by
        refine vec2_ext ?_ ?_ <;> simp [hw 0, hw 1]
      rw [hz] at hzX
      exact ⟨⟨w 1, w 0⟩, (h _ _).1 hzX, hz.symm⟩
    · rintro ⟨⟨b, a⟩, hab, rfl⟩
      refine ⟨(h a b).2 hab, (mem_standardIntegerLattice_iff 2 _).2 ⟨![a, b], fun i => ?_⟩⟩
      fin_cases i <;> simp [hF]
  rw [hset, Set.ncard_coe_finset, Finset.card_image_of_injective _ hinj, Finset.card_sigma]

/-- `G(P) = Σ_{y_min ≤ j ≤ y_max} #(ℤ ∩ [l(j), r(j)])`. -/
theorem ncard_latticePoints_eq_rows (hc : IsCompact P) (hv : Convex ℝ P) (hne : P.Nonempty) :
    (DiscreteMinkowski.latticePoints P (standardIntegerLattice 2)).ncard =
      ∑ b ∈ Finset.Icc ⌈yLo P⌉ ⌊yHi P⌋, (Finset.Icc ⌈rowLo P b⌉ ⌊rowHi P b⌋).card := by
  refine ncard_latticePoints_eq_sum_rows P _ _ fun a b => ?_
  simp only [Finset.mem_Icc, Int.ceil_le, Int.le_floor]
  constructor
  · intro h
    have hb := mem_Icc_of_mem hc hv h
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at hb
    exact ⟨hb, rowLo_le hc h, le_rowHi hc h⟩
  · rintro ⟨hb, ha1, ha2⟩
    have hne' := (hsec_nonempty_iff hc hv hne b).2 hb
    show (a : ℝ) ∈ hsec P b
    rw [hsec_eq_Icc_rows hc hv hne']
    exact ⟨ha1, ha2⟩

/-- `G(int P) = Σ_{y_min < j < y_max} #(ℤ ∩ (l(j), r(j)))`. -/
theorem ncard_latticePoints_interior_eq_rows (hc : IsCompact P) (hv : Convex ℝ P)
    (hne : P.Nonempty) :
    (DiscreteMinkowski.latticePoints (interior P) (standardIntegerLattice 2)).ncard =
      ∑ b ∈ Finset.Ioo ⌊yLo P⌋ ⌈yHi P⌉, (Finset.Ioo ⌊rowLo P b⌋ ⌈rowHi P b⌉).card := by
  refine ncard_latticePoints_eq_sum_rows _ _ _ fun a b => ?_
  rw [mem_interior_iff_rows hc hv hne]
  simp only [Finset.mem_Ioo, Int.floor_lt, Int.lt_ceil, mem_Ioo, Matrix.cons_val_one,
    Matrix.cons_val_zero]

end

end LatticeVolumeInterpolation
