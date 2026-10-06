import Davenport
import WeightedSimplex

/-!
# The upper bound of Theorem 1.1 for anti-blocking bodies

Catalog item `theorem_1_1_upper_bound`, the part of its proof after the reductions. Let
`K ⊆ ℝ^n` be compact, convex and anti-blocking, and suppose `s_i e_i ∈ K` with `s_i > 0` for
every `i`. Then

  `G(K) ≤ vol(K) ∏_{i=1}^n (1 + n / s_i)`.

With `s_i = 2/λ_i`, which Lemma 3.3 supplies, this is Eq. (1.8). The proof is the paper's:

1. Eq. (4.1) for anti-blocking bodies (`rogers_shephard_antiBlocking`) gives
   `vol_k(K ∩ L_I) vol_{n-k}(K | L_I^⊥) ≤ binom(n, k) vol(K)` for `|I| = k`;
2. `K ∩ L_I` contains `conv{0, s_i e_i : i ∈ I}`, of volume `(∏_{i ∈ I} s_i) / k!`
   (`volume_weightedSimplex`), so
   `vol_{n-k}(K | L_I^⊥) ≤ k! binom(n, k) vol(K) ∏_{i ∈ I} (1/s_i) ≤ vol(K) ∏_{i ∈ I} (n/s_i)`,
   using `k! binom(n, k) ≤ n^k`, which the paper uses without stating it;
3. Davenport's inequality for anti-blocking bodies (`davenport_antiBlocking`) and the expansion
   `∑_{I ⊆ [n]} ∏_{i ∈ I} a_i = ∏_i (1 + a_i)` finish the proof.
-/

open MeasureTheory Set Module
open scoped ENNReal

namespace LatticeVolumeInterpolation

noncomputable section

variable {n : ℕ}

/-- `conv{0, s_i e_i : i ∈ I}`, in the coordinates of `L_I`, lies in `K ∩ L_I`. -/
theorem weightedSimplex_subset_sectionOn {K : Set (Fin n → ℝ)} (hKconv : Convex ℝ K)
    (h0 : (0 : Fin n → ℝ) ∈ K) {s : Fin n → ℝ} (hs : ∀ i, 0 < s i)
    (hmem : ∀ i, Pi.single i (s i) ∈ K) (I : Finset (Fin n)) :
    weightedSimplex (fun i : {i // i ∈ I} => s i) ⊆ sectionOn I K := by
  classical
  intro u hu
  obtain ⟨hu0, hu1⟩ := hu
  set w : {i // i ∈ I} → ℝ := fun i => u i / s i with hw
  have hw0 : ∀ i, 0 ≤ w i := fun i => div_nonneg (hu0 i) (hs i).le
  set τ := ∑ i, w i with hτ
  have hτ0 : 0 ≤ τ := Finset.sum_nonneg fun i _ => hw0 i
  -- the point `(u, 0)` as a combination of the vertices `s_i e_i`
  have hpt : (coordSplit I).symm (u, 0) = ∑ i, w i • Pi.single (i : Fin n) (s i) := by
    funext j
    rw [coordSplit_symm_apply', Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    split_ifs with hj
    · rw [Finset.sum_eq_single ⟨j, hj⟩]
      · simp [hw, (hs j).ne']
      · rintro b - hb
        have : (j : Fin n) ≠ b := fun h => hb (Subtype.ext h.symm)
        simp [this]
      · simp
    · refine (Finset.sum_eq_zero fun b _ => ?_).symm
      have : j ≠ (b : Fin n) := fun h => hj (h ▸ b.2)
      simp [this]
  change (coordSplit I).symm (u, 0) ∈ K
  rw [hpt]
  rcases hτ0.eq_or_lt with hτz | hτpos
  · have hwz : ∀ i, w i = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hw0 i).1 hτz.symm i (Finset.mem_univ i)
    simpa [hwz] using h0
  · have hq : ∑ i, (w i / τ) • Pi.single (i : Fin n) (s i) ∈ K := by
      refine hKconv.sum_mem (fun i _ => div_nonneg (hw0 i) hτ0) ?_ (fun i _ => hmem i)
      rw [← Finset.sum_div, div_self hτpos.ne']
    have hsc := (hKconv.starConvex h0).smul_mem hq hτ0 hu1
    have : τ • ∑ i, (w i / τ) • Pi.single (i : Fin n) (s i) =
        ∑ i, w i • Pi.single (i : Fin n) (s i) := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, mul_div_cancel₀ _ hτpos.ne']
    rwa [this] at hsc

/-- `k! binom(n, k) ≤ n^k`, in the form used below. -/
theorem choose_mul_factorial_le_pow {n k : ℕ} :
    (n.choose k * k.factorial : ℝ) ≤ (n : ℝ) ^ k := by
  have h : n.choose k * k.factorial ≤ n ^ k := by
    rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.descFactorial_le_pow n k
  exact_mod_cast h

/-- The bound on one projection: `vol_{n-k}(K | L_I^⊥) ≤ vol(K) ∏_{i ∈ I} (n / s_i)`. -/
theorem volume_projectionOff_le {K : Set (Fin n → ℝ)} (hKc : IsCompact K)
    (hKconv : Convex ℝ K) (hK : IsAntiBlocking K) (h0 : (0 : Fin n → ℝ) ∈ K)
    {s : Fin n → ℝ} (hs : ∀ i, 0 < s i) (hmem : ∀ i, Pi.single i (s i) ∈ K)
    (I : Finset (Fin n)) :
    volume (projectionOff I K) ≤ ENNReal.ofReal (∏ i ∈ I, ((n : ℝ) / s i)) * volume K := by
  classical
  set P : ℝ := ∏ i : {i // i ∈ I}, s i with hP
  have hPpos : 0 < P := Finset.prod_pos fun i _ => hs i
  set a : ℝ≥0∞ := ENNReal.ofReal (P / (I.card.factorial : ℝ)) with ha
  have hcard : Fintype.card {i // i ∈ I} = I.card := Fintype.card_coe I
  have hsimp : a ≤ volume (sectionOn I K) := by
    have h := volume_weightedSimplex (ι := {i // i ∈ I}) (s := fun i => s i) (fun i => hs i)
    rw [hcard] at h
    rw [ha, hP, ← h]
    exact measure_mono (weightedSimplex_subset_sectionOn hKconv h0 hs hmem I)
  have hrs := rogers_shephard_antiBlocking hKc hKconv hK I
  have ha0 : a ≠ 0 := by
    rw [ha]; exact (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hatop : a ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmain : a * volume (projectionOff I K) ≤ (n.choose I.card : ℝ≥0∞) * volume K :=
    le_trans (mul_le_mul_left hsimp _) hrs
  have hdiv : volume (projectionOff I K) ≤ a⁻¹ * ((n.choose I.card : ℝ≥0∞) * volume K) := by
    calc volume (projectionOff I K) = a⁻¹ * (a * volume (projectionOff I K)) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel ha0 hatop, one_mul]
      _ ≤ a⁻¹ * ((n.choose I.card : ℝ≥0∞) * volume K) := mul_le_mul_right hmain _
  -- `a⁻¹ binom(n, k) = k! binom(n, k) / P ≤ n^k / P = ∏_{i ∈ I} n / s_i`
  have hconst : a⁻¹ * (n.choose I.card : ℝ≥0∞) ≤ ENNReal.ofReal (∏ i ∈ I, ((n : ℝ) / s i)) := by
    have hprod : ∏ i ∈ I, ((n : ℝ) / s i) = (n : ℝ) ^ I.card / P := by
      rw [Finset.prod_div_distrib, Finset.prod_const, hP, Finset.prod_coe_sort]
    rw [hprod, ha, ← ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [inv_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hPpos]
    have := choose_mul_factorial_le_pow (n := n) (k := I.card)
    linarith
  calc volume (projectionOff I K) ≤ a⁻¹ * ((n.choose I.card : ℝ≥0∞) * volume K) := hdiv
    _ = a⁻¹ * (n.choose I.card : ℝ≥0∞) * volume K := (mul_assoc _ _ _).symm
    _ ≤ ENNReal.ofReal (∏ i ∈ I, ((n : ℝ) / s i)) * volume K := mul_le_mul_left hconst _

/-- **The upper bound of Theorem 1.1 for anti-blocking bodies.** -/
theorem upper_bound_antiBlocking {K : Set (Fin n → ℝ)} (hKc : IsCompact K)
    (hKconv : Convex ℝ K) (hK : IsAntiBlocking K) {s : Fin n → ℝ} (hs : ∀ i, 0 < s i)
    (hmem : ∀ i, Pi.single i (s i) ∈ K) :
    ((DiscreteMinkowski.latticePoints K (standardIntegerLattice n)).ncard : ℝ≥0∞) ≤
      volume K * ENNReal.ofReal (∏ i, (1 + (n : ℝ) / s i)) := by
  classical
  rcases K.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · simp [DiscreteMinkowski.latticePoints]
  have h0 : (0 : Fin n → ℝ) ∈ K :=
    hK.2 x hx 0 (fun _ => le_rfl) (fun i => hK.1 x hx i)
  calc ((DiscreteMinkowski.latticePoints K (standardIntegerLattice n)).ncard : ℝ≥0∞)
      ≤ ∑ I : Finset (Fin n), volume (projectionOff I K) := davenport_antiBlocking hKc hK
    _ ≤ ∑ I : Finset (Fin n), ENNReal.ofReal (∏ i ∈ I, ((n : ℝ) / s i)) * volume K :=
        Finset.sum_le_sum fun I _ =>
          volume_projectionOff_le hKc hKconv hK h0 hs hmem I
    _ = volume K * ENNReal.ofReal (∏ i, (1 + (n : ℝ) / s i)) := by
        rw [← Finset.sum_mul, mul_comm, ← ENNReal.ofReal_sum_of_nonneg
          (fun I _ => Finset.prod_nonneg fun i _ => div_nonneg (Nat.cast_nonneg n) (hs i).le),
          Finset.prod_one_add, Finset.powerset_univ]

end

end LatticeVolumeInterpolation
