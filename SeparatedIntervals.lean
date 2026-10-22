import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

/-!
# Separated interval families

Catalog item `bhw_lattice_conjecture_dimension_three_symmetric`.
The one-dimensional case of Malikiosis's Conjecture 3.2.1, used in the
established symmetric dimension-three floor-product bound quoted by
Freyer--Lucas. Each closed interval has length less than `q₁`, and distinct
intervals have no points differing by a multiple of `q₂ ≤ q₁`.

The source distinguishes a long interval, whose periodic translates cover
the line, from short intervals, whose integer points inject into residues.
-/

open Set
open scoped BigOperators

namespace LatticeVolumeInterpolation

/-- The integer points in the closed real interval `[a,b]`. -/
noncomputable def intervalIntegerPoints (a b : ℝ) : Finset ℤ :=
  Finset.Icc ⌈a⌉ ⌊b⌋

theorem mem_intervalIntegerPoints {a b : ℝ} {z : ℤ} :
    z ∈ intervalIntegerPoints a b ↔ a ≤ (z : ℝ) ∧ (z : ℝ) ≤ b := by
  simp only [intervalIntegerPoints, Finset.mem_Icc, Int.ceil_le, Int.le_floor]

/-- An interval of length less than a positive integer contains at most that
many integers; reduction modulo that integer is injective on its points. -/
theorem intervalIntegerPoints_card_le {a b : ℝ} {q : ℕ}
    (_hq : 0 < q) (hlen : b - a < q) :
    (intervalIntegerPoints a b).card ≤ q := by
  rw [intervalIntegerPoints, Int.card_Icc]
  have ha := Int.le_ceil a
  have hb := Int.floor_le b
  have h : ⌊b⌋ + 1 - ⌈a⌉ ≤ (q : ℤ) := by
    have hr : (⌊b⌋ : ℝ) - (⌈a⌉ : ℝ) < q := by linarith
    have hz : ⌊b⌋ - ⌈a⌉ < (q : ℤ) := by exact_mod_cast hr
    omega
  exact Int.toNat_le.mpr (by exact_mod_cast h)

/-- The periodic translates of a closed interval of length at least `q`
cover the real line. The source uses this to eliminate all other intervals. -/
theorem exists_periodic_translate_mem_interval {a b x : ℝ} {q : ℕ}
    (hq : 0 < q) (hlen : (q : ℝ) ≤ b - a) :
    ∃ k : ℤ, a ≤ x + (q : ℝ) * k ∧ x + (q : ℝ) * k ≤ b := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  refine ⟨⌈(a - x) / q⌉, ?_, ?_⟩
  · have h := Int.le_ceil ((a - x) / q)
    have hm := mul_le_mul_of_nonneg_left h hqr.le
    have he : (q : ℝ) * ((a - x) / q) = a - x := by field_simp
    rw [he] at hm
    linarith
  · have h := Int.ceil_lt_add_one ((a - x) / q)
    have hm := mul_lt_mul_of_pos_left h hqr
    have he : (q : ℝ) * (((a - x) / q) + 1) = a - x + q := by field_simp
    rw [he] at hm
    linarith

/-- Short intervals separated modulo `q` have jointly injective residue maps. -/
theorem interval_residue_injective {ι : Type*} {a b : ι → ℝ} {q : ℕ}
    (hq : 0 < q) (hlen : ∀ i, b i - a i < q)
    (hsep : ∀ i j, i ≠ j → ∀ x ∈ Icc (a i) (b i),
      ∀ y ∈ Icc (a j) (b j), ∀ k : ℤ, x - y ≠ (q : ℝ) * k) :
    Function.Injective (fun p : Σ i, {z // z ∈ intervalIntegerPoints (a i) (b i)} =>
      (p.2.1 : ZMod q)) := by
  rintro ⟨i, x, hx⟩ ⟨j, y, hy⟩ heq
  have hx' := mem_intervalIntegerPoints.mp hx
  have hy' := mem_intervalIntegerPoints.mp hy
  have hdvd := (ZMod.intCast_eq_intCast_iff_dvd_sub x y q).mp heq
  obtain ⟨k, hk⟩ := hdvd
  have hdiff : (y : ℝ) - x = (q : ℝ) * k := by exact_mod_cast hk
  have hij : i = j := by
    by_contra hne
    exact hsep j i (Ne.symm hne) y hy' x hx' k hdiff
  subst j
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hl : -(q : ℝ) < (y : ℝ) - x := by linarith [hlen i]
  have hu : (y : ℝ) - x < q := by linarith [hlen i]
  have hk0 : k = 0 := by
    have hkl : (-1 : ℝ) < k := by nlinarith
    have hku : (k : ℝ) < 1 := by nlinarith
    have hkl' : (-1 : ℤ) < k := by exact_mod_cast hkl
    have hku' : k < (1 : ℤ) := by exact_mod_cast hku
    omega
  have hxy : x = y := by
    have : y - x = 0 := by simpa [hk0] using hk
    omega
  subst y
  rfl

/-- Malikiosis's one-dimensional separated-family inequality, including
empty intervals and singleton intervals. These endpoints are needed for
the slices and isolated integer points in the planar induction. -/
theorem separated_intervals_card_sum_le {ι : Type*} [Fintype ι]
    {a b : ι → ℝ} {q₁ q₂ : ℕ} (hq₂ : 0 < q₂) (horder : q₂ ≤ q₁)
    (hlen : ∀ i, b i - a i < q₁)
    (hsep : ∀ i j, i ≠ j → ∀ x ∈ Icc (a i) (b i),
      ∀ y ∈ Icc (a j) (b j), ∀ k : ℤ, x - y ≠ (q₂ : ℝ) * k) :
    ∑ i, (intervalIntegerPoints (a i) (b i)).card ≤ q₁ := by
  classical
  by_cases hshort : ∀ i, b i - a i < q₂
  · haveI : NeZero q₂ := ⟨by omega⟩
    have hinj := interval_residue_injective hq₂ hshort hsep
    have hc := Fintype.card_le_of_injective _ hinj
    have hbound : ∑ i, (intervalIntegerPoints (a i) (b i)).card ≤ q₂ := by
      simpa only [Fintype.card_sigma, Fintype.card_coe, ZMod.card] using hc
    exact hbound.trans horder
  · push Not at hshort
    obtain ⟨i, hi⟩ := hshort
    have hzero : ∀ j, j ≠ i → (intervalIntegerPoints (a j) (b j)).card = 0 := by
      intro j hji
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_of_forall_notMem
      intro y hy
      have hy' := mem_intervalIntegerPoints.mp hy
      obtain ⟨k, hklo, hkhi⟩ := exists_periodic_translate_mem_interval hq₂ hi (x := (y : ℝ))
      exact hsep i j (Ne.symm hji) ((y : ℝ) + (q₂ : ℝ) * k) ⟨hklo, hkhi⟩
        y hy' k (by ring)
    rw [Finset.sum_eq_single i (fun j _ hji => hzero j hji) (by simp)]
    exact intervalIntegerPoints_card_le (by omega) (hlen i)

/-- Grouping intervals by a finite label set applies the separated-family
bound independently in every group. Malikiosis labels rows by their height
residue; no separation is required between different groups. -/
theorem grouped_separated_intervals_card_sum_le
    {ι ρ : Type*} [Fintype ι] [Fintype ρ] (g : ι → ρ)
    {a b : ι → ℝ} {q₁ q₂ : ℕ} (hq₂ : 0 < q₂) (horder : q₂ ≤ q₁)
    (hlen : ∀ i, b i - a i < q₁)
    (hsep : ∀ i j, g i = g j → i ≠ j → ∀ x ∈ Icc (a i) (b i),
      ∀ y ∈ Icc (a j) (b j), ∀ k : ℤ, x - y ≠ (q₂ : ℝ) * k) :
    ∑ i, (intervalIntegerPoints (a i) (b i)).card ≤ Fintype.card ρ * q₁ := by
  classical
  rw [← Fintype.sum_fiberwise g (fun i => (intervalIntegerPoints (a i) (b i)).card)]
  calc
    _ ≤ ∑ _r : ρ, q₁ := by
      apply Finset.sum_le_sum
      intro r _
      apply separated_intervals_card_sum_le
        (a := fun i : {i // g i = r} => a i.1)
        (b := fun i : {i // g i = r} => b i.1) hq₂ horder (fun i => hlen i.1)
      intro i j hne x hx y hy k
      exact hsep i.1 j.1 (i.2.trans j.2.symm)
        (fun he => hne (Subtype.ext he)) x hx y hy k
    _ = _ := by simp

end LatticeVolumeInterpolation
