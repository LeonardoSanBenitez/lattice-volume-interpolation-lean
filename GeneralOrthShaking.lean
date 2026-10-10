import GeneralShaking
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Algebra.Order.Field.Pointwise

/-!
# Blaschke shaking in an arbitrary direction and dimension

Catalog item `lemma_3_2_shaking_properties` (Lemma 3.2(i)--(iv)). The earlier
`GeneralShaking` proves all four parts in the plane. Here the orthogonal projection
and each fibre are expressed in the paper's direction `u` in `ℝⁿ`; the scalar fibre
parameter multiplies `u` itself, so its interval length is Euclidean chord length
divided by the Euclidean length of `u` (not the supremum norm on the function space).
-/

open Set Module MeasureTheory
open scoped Pointwise

namespace LatticeVolumeInterpolation

noncomputable section

variable {n : ℕ}

/-- Standard coordinate dot product in `ℝⁿ`. -/
def dotN (u x : Fin n → ℝ) : ℝ := u ⬝ᵥ x

/-- Projection to the hyperplane perpendicular to `u`. -/
def orthProjN (u x : Fin n → ℝ) : Fin n → ℝ :=
  x - (dotN u x / dotN u u) • u

def orthProjNLinear (u : Fin n → ℝ) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun := orthProjN u
  map_add' x y := by
    funext i
    simp [orthProjN, dotN, dotProduct_add, add_div, add_mul, Pi.add_apply,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  map_smul' r x := by
    funext i
    simp [orthProjN, dotN, dotProduct_smul, mul_div_assoc, Pi.smul_apply,
      Pi.sub_apply, smul_eq_mul]
    ring

/-- The scalar parameters of the chord above a projected point. -/
def rawFibre (K : Set (Fin n → ℝ)) (u p : Fin n → ℝ) : Set ℝ :=
  {t | p + t • u ∈ K}

def rawLength (K : Set (Fin n → ℝ)) (u p : Fin n → ℝ) : ℝ :=
  sSup (rawFibre K u p) - sInf (rawFibre K u p)

/-- Orthogonal Blaschke shaking, with each chord moved to start in `u⊥`. -/
def orthShakingN (K : Set (Fin n → ℝ)) (u : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {y | ∃ p ∈ orthProjN u '' K, ∃ t ∈ Icc 0 (rawLength K u p), y = p + t • u}

theorem dotN_self_pos {u : Fin n → ℝ} (hu : u ≠ 0) : 0 < dotN u u := by
  have hn : 0 ≤ u ⬝ᵥ u := by
    change 0 ≤ ∑ i, u i * u i
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg (u i)
  have hne : u ⬝ᵥ u ≠ 0 := fun h => hu (dotProduct_self_eq_zero.mp h)
  unfold dotN
  rcases lt_or_eq_of_le hn with h | h
  · exact h
  · exact False.elim (hne h.symm)

theorem orthProjN_mem_hyperplane {u : Fin n → ℝ} (hu : u ≠ 0) (x : Fin n → ℝ) :
    dotN u (orthProjN u x) = 0 := by
  have hd := (dotN_self_pos hu).ne'
  have hd' : u ⬝ᵥ u ≠ 0 := hd
  simp only [orthProjN, dotN, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  field_simp [hd']
  ring

/-- An orthogonal chart sends any nonzero `u` to a positive coordinate vector.
The reflection is across the hyperplane perpendicular to `u/‖u‖ - e_j`. -/
theorem exists_direction_chart (j : Fin n) {u : Fin n → ℝ} (hu : u ≠ 0) :
    ∃ (V : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) (c : ℝ),
      0 < c ∧ V u = c • Pi.single j (1 : ℝ) ∧
      |LinearMap.det (V : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))| = 1 ∧
      (∀ x y, dotN (V x) (V y) = dotN x y) := by
  let F := EuclideanSpace.equiv (Fin n) ℝ
  let z : EuclideanSpace ℝ (Fin n) := F.symm u
  have hz : z ≠ 0 := by
    intro h
    apply hu
    have : u = F z := by simp [z]
    rw [this, h]
    simp
  let w : EuclideanSpace ℝ (Fin n) := ‖z‖⁻¹ • z
  let e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single j 1
  have hw : ‖w‖ = 1 := norm_smul_inv_norm hz
  have he : ‖e‖ = 1 := by simp [e]
  let R := (ℝ ∙ (w - e))ᗮ.reflection
  have hRw : R w = e := Submodule.reflection_sub (hw.trans he.symm)
  let V : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) :=
    F.symm.toLinearEquiv.trans (R.toLinearEquiv.trans F.toLinearEquiv)
  have hzw : z = ‖z‖ • w := by
    simp [w, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz)]
  refine ⟨V, ‖z‖, norm_pos_iff.mpr hz, ?_, ?_, ?_⟩
  · calc
      V u = F (R z) := rfl
      _ = F (R (‖z‖ • w)) := by rw [← hzw]
      _ = ‖z‖ • F e := by rw [map_smul, hRw, map_smul]
      _ = ‖z‖ • Pi.single j (1 : ℝ) := by congr 1
  · have hdet_eq : LinearMap.det (V : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) =
        LinearMap.det (R.toLinearEquiv :
          (EuclideanSpace ℝ (Fin n)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin n))) := by
      change LinearMap.det (F.toLinearEquiv.toLinearMap ∘ₗ
        R.toLinearEquiv.toLinearMap ∘ₗ F.symm.toLinearEquiv.toLinearMap) = _
      exact LinearMap.det_conj R.toLinearEquiv.toLinearMap F.toLinearEquiv
    rw [hdet_eq, Submodule.det_reflection]
    simp
  · intro x y
    have hinner := R.inner_map_map (F.symm x) (F.symm y)
    change (F (R (F.symm y))) ⬝ᵥ (F (R (F.symm x))) = y ⬝ᵥ x at hinner
    simpa [dotN, dotProduct_comm, V, F] using hinner

theorem chart_proj_zero (j : Fin n) {u : Fin n → ℝ} (hu : u ≠ 0)
    (V : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) (c : ℝ) (hc : 0 < c)
    (hVu : V u = c • Pi.single j (1 : ℝ))
    (hdot : ∀ x y, dotN (V x) (V y) = dotN x y)
    (x : Fin n → ℝ) : (V (orthProjN u x)) j = 0 := by
  have h0 := orthProjN_mem_hyperplane hu x
  have h := hdot u (orthProjN u x)
  rw [hVu] at h
  change (c • Pi.single j (1 : ℝ)) ⬝ᵥ V (orthProjN u x) = dotN u (orthProjN u x) at h
  rw [smul_dotProduct, single_dotProduct, one_mul] at h
  exact (mul_eq_zero.mp (h.trans h0)).resolve_left hc.ne'

theorem chart_orthProj (j : Fin n) {u : Fin n → ℝ} (hu : u ≠ 0)
    (V : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) (c : ℝ) (hc : 0 < c)
    (hVu : V u = c • Pi.single j (1 : ℝ))
    (hdot : ∀ x y, dotN (V x) (V y) = dotN x y)
    (x : Fin n → ℝ) :
    V (orthProjN u x) = Function.update (V x) j 0 := by
  have h0 := chart_proj_zero j hu V c hc hVu hdot x
  have hlin : V (orthProjN u x) =
      V x - (dotN u x / dotN u u) • (c • Pi.single j (1 : ℝ)) := by
    simp [orthProjN, map_sub, map_smul, hVu]
  funext i
  by_cases hi : i = j
  · subst i
    simpa using h0
  · have hcoord := congrFun hlin i
    simpa [Function.update_of_ne hi, Pi.single_eq_of_ne hi] using hcoord

theorem orthProjN_add_smul (u x : Fin n → ℝ) :
    orthProjN u x + (dotN u x / dotN u u) • u = x := by
  unfold orthProjN
  abel

theorem orthProjN_u_eq_zero {u : Fin n → ℝ} (hu : u ≠ 0) : orthProjN u u = 0 := by
  have hd := (dotN_self_pos hu).ne'
  simp [orthProjN, div_self hd]

theorem orthProjN_add_smul_u {u : Fin n → ℝ} (hu : u ≠ 0)
    (x : Fin n → ℝ) (t : ℝ) :
    orthProjN u (x + t • u) = orthProjN u x := by
  change orthProjNLinear u (x + t • u) = orthProjNLinear u x
  rw [map_add, map_smul]
  change orthProjN u x + t • orthProjN u u = orthProjN u x
  simp [orthProjN_u_eq_zero hu]

theorem orthProjN_idem {u : Fin n → ℝ} (hu : u ≠ 0) (x : Fin n → ℝ) :
    orthProjN u (orthProjN u x) = orthProjN u x := by
  have h := orthProjN_add_smul_u hu (orthProjN u x) (dotN u x / dotN u u)
  rw [orthProjN_add_smul u x] at h
  exact h.symm

theorem orthProjN_eq_of_sub_smul {u : Fin n → ℝ} (hu : u ≠ 0)
    {a b : Fin n → ℝ} {t : ℝ} (hab : a - b = t • u) :
    orthProjN u a = orthProjN u b := by
  have h : a = b + t • u := by rw [← hab]; abel
  rw [h, orthProjN_add_smul_u hu]

theorem rawFibre_bdd {K : Set (Fin n → ℝ)} (hK : Bornology.IsBounded K)
    {u : Fin n → ℝ} (hu : u ≠ 0) (p : Fin n → ℝ) :
    BddAbove (rawFibre K u p) ∧ BddBelow (rawFibre K u p) := by
  obtain ⟨R, hR⟩ := hK.exists_norm_le
  have hupos : 0 < ‖u‖ := norm_pos_iff.2 hu
  have key : ∀ t ∈ rawFibre K u p, |t| ≤ (R + ‖p‖) / ‖u‖ := by
    intro t ht
    rw [le_div_iff₀ hupos]
    have h1 := hR _ ht
    have h2 : ‖t • u‖ ≤ ‖p + t • u‖ + ‖p‖ := by
      have := norm_sub_le (p + t • u) p
      simpa using this
    rw [norm_smul, Real.norm_eq_abs] at h2
    linarith
  refine ⟨⟨(R + ‖p‖) / ‖u‖, fun t ht => (le_abs_self t).trans (key t ht)⟩,
    ⟨-((R + ‖p‖) / ‖u‖), fun t ht => ?_⟩⟩
  have h := key t ht
  rw [abs_le] at h
  exact h.1

theorem isCompact_rawFibre {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    {u : Fin n → ℝ} (hu : u ≠ 0) (p : Fin n → ℝ) :
    IsCompact (rawFibre K u p) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · exact hK.isClosed.preimage (continuous_const.add (continuous_id.smul continuous_const))
  · have hb := rawFibre_bdd hK.isBounded hu p
    exact isBounded_iff_bddBelow_bddAbove.2 ⟨hb.2, hb.1⟩

theorem convex_rawFibre {K : Set (Fin n → ℝ)} (hK : Convex ℝ K)
    (u p : Fin n → ℝ) : Convex ℝ (rawFibre K u p) := by
  intro s hs t ht a b ha hb hab
  change p + (a * s + b * t) • u ∈ K
  convert hK hs ht ha hb hab using 1
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination -(p i) * hab

theorem rawFibre_eq_Icc {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (hKc : Convex ℝ K) {u : Fin n → ℝ} (hu : u ≠ 0)
    (p : Fin n → ℝ) (hne : (rawFibre K u p).Nonempty) :
    rawFibre K u p = Icc (sInf (rawFibre K u p)) (sSup (rawFibre K u p)) := by
  have hc := isCompact_rawFibre hK hu p
  refine Subset.antisymm (fun t ht => ⟨csInf_le hc.bddBelow ht, le_csSup hc.bddAbove ht⟩) ?_
  have hord := (convex_iff_ordConnected.1 (convex_rawFibre hKc u p))
  exact hord.out (hc.sInf_mem hne) (hc.sSup_mem hne)

theorem rawLength_nonneg {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    {u : Fin n → ℝ} (hu : u ≠ 0) {p : Fin n → ℝ}
    (hne : (rawFibre K u p).Nonempty) : 0 ≤ rawLength K u p := by
  obtain ⟨t, ht⟩ := hne
  obtain ⟨habove, hbelow⟩ := rawFibre_bdd hK.isBounded hu p
  unfold rawLength
  have hlo := csInf_le hbelow ht
  have hhi := le_csSup habove ht
  linarith

/-- A shaken point projects back to its own fibre anchor. -/
theorem orthProjN_shaken_point {K : Set (Fin n → ℝ)}
    {u : Fin n → ℝ} (hu : u ≠ 0) {p : Fin n → ℝ}
    (hp : p ∈ orthProjN u '' K) (t : ℝ) :
    orthProjN u (p + t • u) = p := by
  obtain ⟨x, _, rfl⟩ := hp
  rw [orthProjN_add_smul_u hu, orthProjN_idem hu]

/-- Each shaken fibre is the interval starting at its orthogonal projection. -/
theorem rawFibre_orthShakingN {K : Set (Fin n → ℝ)}
    {u : Fin n → ℝ} (hu : u ≠ 0) {p : Fin n → ℝ}
    (hp : p ∈ orthProjN u '' K) :
    rawFibre (orthShakingN K u) u p = Icc 0 (rawLength K u p) := by
  ext t
  constructor
  · rintro ⟨q, hq, s, hs, heq⟩
    have hproj := congrArg (orthProjN u) heq
    rw [orthProjN_shaken_point hu hp t, orthProjN_shaken_point hu hq s] at hproj
    subst q
    have hsmul : t • u = s • u := add_left_cancel heq
    have hts : t = s := smul_left_injective ℝ hu hsmul
    exact hts ▸ hs
  · intro ht
    exact ⟨p, hp, t, ht, rfl⟩

theorem rawFibre_nonempty_of_proj {K : Set (Fin n → ℝ)}
    {u : Fin n → ℝ} {p : Fin n → ℝ}
    (hp : p ∈ orthProjN u '' K) : (rawFibre K u p).Nonempty := by
  obtain ⟨x, hx, rfl⟩ := hp
  exact ⟨dotN u x / dotN u u, by
    change orthProjN u x + (dotN u x / dotN u u) • u ∈ K
    rw [orthProjN_add_smul]
    exact hx⟩

/-- Shaking preserves the scalar length of every nonempty directional fibre. -/
theorem rawLength_orthShakingN {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    {u : Fin n → ℝ} (hu : u ≠ 0) {p : Fin n → ℝ}
    (hp : p ∈ orthProjN u '' K) :
    rawLength (orthShakingN K u) u p = rawLength K u p := by
  have hlen := rawLength_nonneg hK hu (rawFibre_nonempty_of_proj hp)
  change sSup (rawFibre (orthShakingN K u) u p) -
    sInf (rawFibre (orthShakingN K u) u p) = rawLength K u p
  rw [rawFibre_orthShakingN hu hp, csSup_Icc hlen, csInf_Icc hlen]
  simp

/-- Any directional difference realized in `K` is realized after shaking. -/
theorem smul_mem_sub_orthShakingN_of_mem_sub {K : Set (Fin n → ℝ)}
    (hK : IsCompact K) {u : Fin n → ℝ} (hu : u ≠ 0)
    {δ : ℝ} (hδ : 0 ≤ δ) (hmem : δ • u ∈ K - K) :
    δ • u ∈ orthShakingN K u - orthShakingN K u := by
  obtain ⟨a, ha, b, hb, hab⟩ := mem_sub.mp hmem
  have hba : a = b + δ • u := by rw [← hab]; abel
  let p := orthProjN u b
  let t := dotN u b / dotN u u
  have hp : p ∈ orthProjN u '' K := ⟨b, hb, rfl⟩
  have hbt : t ∈ rawFibre K u p := by
    change p + t • u ∈ K
    exact (orthProjN_add_smul u b).symm ▸ hb
  have hat : t + δ ∈ rawFibre K u p := by
    change p + (t + δ) • u ∈ K
    rw [add_smul, ← add_assoc, orthProjN_add_smul u b]
    exact hba ▸ ha
  have hlen : δ ≤ rawLength K u p := by
    obtain ⟨habove, hbelow⟩ := rawFibre_bdd hK.isBounded hu p
    have hlo := csInf_le hbelow hbt
    have hhi := le_csSup habove hat
    unfold rawLength
    linarith
  have hzero : p ∈ orthShakingN K u :=
    ⟨p, hp, 0, ⟨le_rfl, (rawLength_nonneg hK hu ⟨t, hbt⟩)⟩, by simp⟩
  have htop : p + δ • u ∈ orthShakingN K u :=
    ⟨p, hp, δ, ⟨hδ, hlen⟩, rfl⟩
  exact mem_sub.mpr ⟨p + δ • u, htop, p, hzero, by abel⟩

/-- For convex `K`, a directional difference after shaking already occurred in `K`. -/
theorem smul_mem_sub_of_mem_sub_orthShakingN {K : Set (Fin n → ℝ)}
    (hK : IsCompact K) (hKc : Convex ℝ K)
    {u : Fin n → ℝ} (hu : u ≠ 0)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hmem : δ • u ∈ orthShakingN K u - orthShakingN K u) :
    δ • u ∈ K - K := by
  obtain ⟨a, ha, b, hb, hab⟩ := mem_sub.mp hmem
  obtain ⟨p, hp, s, hs, rfl⟩ := ha
  obtain ⟨q, hq, t, ht, rfl⟩ := hb
  have hproj := orthProjN_eq_of_sub_smul hu hab
  rw [orthProjN_shaken_point hu hp s, orthProjN_shaken_point hu hq t] at hproj
  subst q
  have hst : s - t = δ := by
    have hsmul : (s - t) • u = δ • u := by
      rw [← hab]
      module
    exact smul_left_injective ℝ hu hsmul
  have hlen : δ ≤ rawLength K u p := by linarith [hs.2, ht.1]
  have hne := rawFibre_nonempty_of_proj hp
  have hcompact := isCompact_rawFibre hK hu p
  have hlo : sInf (rawFibre K u p) ∈ rawFibre K u p := hcompact.sInf_mem hne
  have hhi : sInf (rawFibre K u p) + δ ∈ rawFibre K u p := by
    have hmemIcc : sInf (rawFibre K u p) + δ ∈
        Icc (sInf (rawFibre K u p)) (sSup (rawFibre K u p)) := by
      refine ⟨by linarith, ?_⟩
      unfold rawLength at hlen
      linarith
    exact (congrArg (fun S : Set ℝ => sInf (rawFibre K u p) + δ ∈ S)
      (rawFibre_eq_Icc hK hKc hu p hne).symm).mp hmemIcc
  have hlow : p + sInf (rawFibre K u p) • u ∈ K := hlo
  have hhigh : p + (sInf (rawFibre K u p) + δ) • u ∈ K := hhi
  exact mem_sub.mpr ⟨p + (sInf (rawFibre K u p) + δ) • u, hhigh,
    p + sInf (rawFibre K u p) • u, hlow, by module⟩

theorem mem_smul_halfDifferenceBody_iff (S : Set (Fin n → ℝ))
    (u : Fin n → ℝ) {r : ℝ} (hr : 0 < r) :
    u ∈ r • DiscreteMinkowski.halfDifferenceBody S ↔
      (2 / r) • u ∈ S - S := by
  rw [DiscreteMinkowski.halfDifferenceBody_apply,
    Set.mem_smul_set_iff_inv_smul_mem₀ hr.ne',
    Set.mem_smul_set_iff_inv_smul_mem₀ (by norm_num : (2⁻¹ : ℝ) ≠ 0)]
  simp only [inv_inv, smul_smul]
  field_simp

/-- **Lemma 3.2(iii), all dimensions:** shaking leaves the gauge of its direction unchanged. -/
theorem gauge_orthShakingN_direction_eq {K : Set (Fin n → ℝ)}
    (hK : IsCompact K) (hKb : DiscreteMinkowski.IsPaperConvexBody K)
    {u : Fin n → ℝ} (hu : u ≠ 0) :
    gauge (DiscreteMinkowski.halfDifferenceBody (orthShakingN K u)) u =
      gauge (DiscreteMinkowski.halfDifferenceBody K) u := by
  unfold gauge
  congr 1
  ext r
  refine and_congr_right fun hr => ?_
  rw [mem_smul_halfDifferenceBody_iff _ u hr,
    mem_smul_halfDifferenceBody_iff _ u hr]
  have hδ : 0 ≤ 2 / r := by positivity
  exact ⟨smul_mem_sub_of_mem_sub_orthShakingN hK hKb.2.1 hu hδ,
    smul_mem_sub_orthShakingN_of_mem_sub hK hu hδ⟩

/-- **Lemma 3.2(i), all dimensions:** the orthogonal projection lies in the shaking. -/
theorem orthProjN_image_subset_orthShakingN {K : Set (Fin n → ℝ)}
    (hK : IsCompact K) {u : Fin n → ℝ} (hu : u ≠ 0) :
    orthProjN u '' K ⊆ orthShakingN K u := by
  rintro p ⟨x, hx, rfl⟩
  have hne : (rawFibre K u (orthProjN u x)).Nonempty := by
    refine ⟨dotN u x / dotN u u, ?_⟩
    change orthProjN u x + (dotN u x / dotN u u) • u ∈ K
    rw [orthProjN_add_smul u x]
    exact hx
  obtain ⟨habove, hbelow⟩ := rawFibre_bdd hK.isBounded hu (orthProjN u x)
  obtain ⟨t, ht⟩ := hne
  have hlen : 0 ≤ rawLength K u (orthProjN u x) := by
    unfold rawLength
    have hlo := csInf_le hbelow ht
    have hhi := le_csSup habove ht
    linarith
  exact ⟨_, ⟨x, hx, rfl⟩, 0, ⟨le_rfl, hlen⟩, by simp⟩

/-- **Lemma 3.2(iv), all dimensions:** projection cannot increase the shaken gauge. -/
theorem gauge_orthShakingN_proj_le {K : Set (Fin n → ℝ)}
    (hK : IsCompact K) (hKb : DiscreteMinkowski.IsPaperConvexBody K)
    {u : Fin n → ℝ} (hu : u ≠ 0) (x : Fin n → ℝ) :
    gauge (DiscreteMinkowski.halfDifferenceBody (orthShakingN K u)) (orthProjN u x) ≤
      gauge (DiscreteMinkowski.halfDifferenceBody K) x := by
  refine le_of_forall_gt_imp_ge_of_dense fun r hr => ?_
  have hr0 : 0 < r := lt_of_le_of_lt (gauge_nonneg _) hr
  have hx : x ∈ r • DiscreteMinkowski.halfDifferenceBody K :=
    DiscreteMinkowski.mem_smul_of_gauge_lt hKb hr
  obtain ⟨d, hd, hdx⟩ := mem_smul_set.1 hx
  rw [DiscreteMinkowski.halfDifferenceBody_apply] at hd
  obtain ⟨w, ⟨a, ha, b, hb, rfl⟩, rfl⟩ := mem_smul_set.1 hd
  have hpa : orthProjN u a ∈ orthShakingN K u :=
    orthProjN_image_subset_orthShakingN hK hu ⟨a, ha, rfl⟩
  have hpb : orthProjN u b ∈ orthShakingN K u :=
    orthProjN_image_subset_orthShakingN hK hu ⟨b, hb, rfl⟩
  have hrep : orthProjN u x =
      r • ((2 : ℝ)⁻¹ • (orthProjN u a - orthProjN u b)) := by
    rw [← hdx]
    exact (orthProjNLinear u).map_smul r ((2 : ℝ)⁻¹ • (a - b)) |>.trans (by
      rw [map_smul, map_sub]; rfl)
  have hmem : orthProjN u x ∈
      r • DiscreteMinkowski.halfDifferenceBody (orthShakingN K u) := by
    rw [hrep, DiscreteMinkowski.halfDifferenceBody_apply]
    exact smul_mem_smul_set (smul_mem_smul_set (sub_mem_sub hpa hpb))
  exact DiscreteMinkowski.gauge_le_of_mem_smul hr0.le hmem

/-! ### Transport of the fibres and their volumes -/

theorem chart_fibre_point (j : Fin n) {u p : Fin n → ℝ}
    (V : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) (c : ℝ)
    (hVu : V u = c • Pi.single j (1 : ℝ)) (hp : (V p) j = 0) (t : ℝ) :
    V (p + t • u) = Function.update (V p) j (c * t) := by
  rw [map_add, map_smul, hVu]
  funext i
  by_cases hi : i = j
  · subst i; simp [hp, mul_comm]
  · simp [Function.update_of_ne hi, Pi.single_eq_of_ne hi]

theorem fibre_chart (K : Set (Fin n → ℝ)) (j : Fin n) {u p : Fin n → ℝ}
    (V : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) (c : ℝ) (hc : 0 < c)
    (hVu : V u = c • Pi.single j (1 : ℝ)) (hp : (V p) j = 0) :
    fibre (V '' K) j (V p) = c • rawFibre K u p := by
  ext s
  constructor
  · intro hs
    refine ⟨s / c, ?_, by simpa only [smul_eq_mul] using mul_div_cancel₀ s hc.ne'⟩
    change p + (s / c) • u ∈ K
    have hpoint := chart_fibre_point j V c hVu hp (s / c)
    rw [mul_div_cancel₀ _ hc.ne'] at hpoint
    have himage : V (p + (s / c) • u) ∈ V '' K := hpoint.symm ▸ hs
    exact V.injective.mem_set_image.mp himage
  · rintro ⟨t, ht, rfl⟩
    change Function.update (V p) j (c * t) ∈ V '' K
    rw [← chart_fibre_point j V c hVu hp t]
    exact ⟨p + t • u, ht, rfl⟩

theorem fibreLength_chart {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (hKc : Convex ℝ K) (j : Fin n) {u p : Fin n → ℝ} (hu : u ≠ 0)
    (V : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) (c : ℝ) (hc : 0 < c)
    (hVu : V u = c • Pi.single j (1 : ℝ)) (hp : (V p) j = 0)
    (hne : (rawFibre K u p).Nonempty) :
    fibreLength (V '' K) j (V p) = c * rawLength K u p := by
  have hf := fibre_chart K j V c hc hVu hp
  rw [rawFibre_eq_Icc hK hKc hu p hne, LinearOrderedField.smul_Icc hc] at hf
  have hord : sInf (rawFibre K u p) ≤ sSup (rawFibre K u p) := by
    have := rawLength_nonneg hK hu hne
    unfold rawLength at this
    linarith
  unfold fibreLength
  rw [hf, csSup_Icc (mul_le_mul_of_nonneg_left hord hc.le),
    csInf_Icc (mul_le_mul_of_nonneg_left hord hc.le)]
  exact (mul_sub c _ _).symm

/-- The direction chart identifies the exact shaking sets, including their boundary fibres. -/
theorem image_orthShakingN_eq_coordShaking {K : Set (Fin n → ℝ)}
    (hK : IsCompact K) (hKc : Convex ℝ K) (j : Fin n) {u : Fin n → ℝ} (hu : u ≠ 0)
    (V : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) (c : ℝ) (hc : 0 < c)
    (hVu : V u = c • Pi.single j (1 : ℝ))
    (hdot : ∀ x y, dotN (V x) (V y) = dotN x y) :
    V '' orthShakingN K u = coordShaking (V '' K) j := by
  ext y
  constructor
  · rintro ⟨z, ⟨p, hp, t, ht, rfl⟩, rfl⟩
    have hp0 : (V p) j = 0 := by
      obtain ⟨x, hx, rfl⟩ := hp
      exact chart_proj_zero j hu V c hc hVu hdot x
    have hne := rawFibre_nonempty_of_proj hp
    rw [chart_fibre_point j V c hVu hp0]
    refine ⟨?_, by simpa using mul_nonneg hc.le ht.1, ?_⟩
    · rw [fibre_update, fibre_chart K j V c hc hVu hp0]
      obtain ⟨t, ht⟩ := hne
      exact ⟨c * t, ⟨t, ht, rfl⟩⟩
    · rw [fibreLength_update, fibreLength_chart hK hKc j hu V c hc hVu hp0 hne]
      simpa using mul_le_mul_of_nonneg_left ht.2 hc.le
  · rintro ⟨hne, hy0, hyl⟩
    obtain ⟨s, x, hx, hxchart⟩ := hne
    let p := orthProjN u x
    have hp : p ∈ orthProjN u '' K := ⟨x, hx, rfl⟩
    have hVp : V p = Function.update y j 0 := by
      rw [chart_orthProj j hu V c hc hVu hdot x, hxchart]
      simp
    have hp0 : (V p) j = 0 := by rw [hVp]; simp
    have hraw := rawFibre_nonempty_of_proj hp
    have hlen : fibreLength (V '' K) j y = c * rawLength K u p := by
      rw [← fibreLength_update (V '' K) j y 0, ← hVp]
      exact fibreLength_chart hK hKc j hu V c hc hVu hp0 hraw
    refine ⟨p + (y j / c) • u, ⟨p, hp, y j / c, ⟨div_nonneg hy0 hc.le, ?_⟩, rfl⟩, ?_⟩
    · apply (div_le_iff₀ hc).2
      rw [hlen] at hyl
      simpa [mul_comm] using hyl
    · rw [chart_fibre_point j V c hVu hp0, hVp, mul_div_cancel₀ _ hc.ne']
      simp

/-- The Euclidean length of the actual chord is its scalar length times the
Euclidean length of the direction; the ambient function-space norm is not used. -/
theorem euclidean_chord_length {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    {u p : Fin n → ℝ} (hu : u ≠ 0) (hne : (rawFibre K u p).Nonempty) :
    dist ((EuclideanSpace.equiv (Fin n) ℝ).symm
      (p + sSup (rawFibre K u p) • u))
      ((EuclideanSpace.equiv (Fin n) ℝ).symm
      (p + sInf (rawFibre K u p) • u)) =
    rawLength K u p * ‖(EuclideanSpace.equiv (Fin n) ℝ).symm u‖ := by
  rw [dist_eq_norm, ← map_sub]
  have hsub : (p + sSup (rawFibre K u p) • u) -
      (p + sInf (rawFibre K u p) • u) = rawLength K u p • u := by
    unfold rawLength
    module
  rw [hsub, map_smul, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (rawLength_nonneg hK hu hne)]

/-- **Lemma 3.2(ii), all dimensions:** orthogonal shaking preserves volume.
The chart transports the unchanged chord lengths to the coordinate Fubini identity. -/
theorem volume_orthShakingN {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (hKc : Convex ℝ K) {u : Fin n → ℝ} (hu : u ≠ 0) :
    volume (orthShakingN K u) = volume K := by
  have hn : 0 < n := by
    by_contra h
    have hn0 : n = 0 := by omega
    subst n
    exact hu (Subsingleton.elim _ _)
  let j : Fin n := ⟨0, hn⟩
  obtain ⟨V, c, hc, hVu, hdet, hdot⟩ := exists_direction_chart j hu
  have hcont : Continuous V := V.toContinuousLinearEquiv.continuous
  calc
    volume (orthShakingN K u) = volume (V '' orthShakingN K u) :=
      (volume_image_of_det V hdet _).symm
    _ = volume (coordShaking (V '' K) j) := by
      rw [image_orthShakingN_eq_coordShaking hK hKc j hu V c hc hVu hdot]
    _ = volume (V '' K) := volume_coordShaking (hK.image hcont) (hKc.linear_image V.toLinearMap) j
    _ = volume K := volume_image_of_det V hdet K

end

end LatticeVolumeInterpolation
