import RealRectangles
import RatioConjectureLimit

/-!
# The elongated-box comparison

Catalog item `covering_radius_bound_not_comparable`, the unnumbered
comparison of Eqs. (1.15) and (1.8) after Proposition 1.6.

In dimension `n+1`, the first `n` half-sides equal `r` and the final
half-side is one half. The covering constant stays `2^(n+1)` while the
minimum-based constant tends to `n+2`.
-/

open Set Filter Topology
open scoped BigOperators

namespace LatticeVolumeInterpolation

noncomputable section

def thinBoxWidths (n : ℕ) (r : ℝ) : Fin (n + 1) → ℝ :=
  fun i => if i.1 < n then r else 1 / 2

def thinBox (n : ℕ) (r : ℝ) : Set (Fin (n + 1) → ℝ) := rectangularBox (thinBoxWidths n r)

theorem thinBoxWidths_antitone (n : ℕ) {r : ℝ} (hr : 1 / 2 ≤ r) :
    Antitone (thinBoxWidths n r) := by
  intro i j hij
  have hv : i.1 ≤ j.1 := hij
  simp only [thinBoxWidths]
  split_ifs <;> first | exact le_rfl | exact hr | omega

theorem successiveMinimum_thinBox (n : ℕ) {r : ℝ} (hr : 1 / 2 ≤ r) (i : Fin (n + 1)) :
    DiscreteMinkowski.successiveMinimum (thinBox n r) (standardIntegerLattice (n + 1))
      (i.1 + 1) = if i.1 < n then r⁻¹ else 2 := by
  rw [thinBox, successiveMinimum_rectangularBox _
    (fun j => by simp only [thinBoxWidths]; split_ifs <;> linarith)
    (thinBoxWidths_antitone n hr)]
  simp only [thinBoxWidths]
  split_ifs <;> norm_num

theorem coveringRadius_thinBox (n : ℕ) {r : ℝ} (hr : 1 / 2 ≤ r) :
    coveringRadius (thinBox n r) = 1 := by
  apply coveringRadius_rectangularBox_eq_one (thinBoxWidths n r)
    (fun i => by simp only [thinBoxWidths]; split_ifs <;> first | exact hr | rfl) (Fin.last n)
  simp [thinBoxWidths]

theorem thinBox_covering_constant (n : ℕ) {r : ℝ} (hr : 1 / 2 ≤ r) :
    (1 + coveringRadius (thinBox n r)) ^ (n + 1) = (2 : ℝ) ^ (n + 1) := by
  rw [coveringRadius_thinBox n hr]
  norm_num

theorem thinBox_minima_constant (n : ℕ) {r : ℝ} (hr : 1 / 2 ≤ r) :
    (∏ i : Fin (n + 1), (1 + (n + 1 : ℝ) *
      DiscreteMinkowski.successiveMinimum (thinBox n r)
        (standardIntegerLattice (n + 1)) (i.1 + 1) / 2)) =
      (1 + (n + 1 : ℝ) * r⁻¹ / 2) ^ n * (n + 2 : ℝ) := by
  simp_rw [successiveMinimum_thinBox n hr]
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.isLt, ↓reduceIte, Fin.val_last, lt_self_iff_false]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  ring

theorem thinBox_minima_constant_limit (n : ℕ) :
    Tendsto (fun r : ℝ => ∏ i : Fin (n + 1), (1 + (n + 1 : ℝ) *
      DiscreteMinkowski.successiveMinimum (thinBox n r)
        (standardIntegerLattice (n + 1)) (i.1 + 1) / 2)) atTop (𝓝 (n + 2 : ℝ)) := by
  have hbase : Tendsto (fun r : ℝ => 1 + (n + 1 : ℝ) * r⁻¹ / 2) atTop (𝓝 1) := by
    have hh : Tendsto (fun r : ℝ => 1 + (n + 1 : ℝ) * r⁻¹ / 2)
        atTop (𝓝 (1 + (n + 1 : ℝ) * 0 / 2)) :=
      tendsto_const_nhds.add ((tendsto_const_nhds.mul tendsto_inv_atTop_zero).div_const 2)
    simpa using hh
  have hh := (hbase.pow n).mul_const (n + 2 : ℝ)
  have he : (fun r : ℝ => (1 + (n + 1 : ℝ) * r⁻¹ / 2) ^ n * (n + 2 : ℝ)) =ᶠ[atTop]
      (fun r : ℝ => ∏ i : Fin (n + 1), (1 + (n + 1 : ℝ) *
        DiscreteMinkowski.successiveMinimum (thinBox n r)
          (standardIntegerLattice (n + 1)) (i.1 + 1) / 2)) := by
    filter_upwards [eventually_ge_atTop (1 / 2 : ℝ)] with r hr
    exact (thinBox_minima_constant n hr).symm
  simpa using hh.congr' he

theorem thinBox_isConvexBody (n : ℕ) {r : ℝ} (hr : 1 / 2 ≤ r) :
    IsConvexBody (thinBox n r) := by
  refine ⟨isCompact_Icc, convex_Icc _ _, ⟨0, ?_⟩⟩
  apply mem_interior_iff_mem_nhds.mpr
  apply Metric.mem_nhds_iff.mpr
  refine ⟨1 / 2, by norm_num, ?_⟩
  intro x hx
  have hcoord := (dist_pi_lt_iff (by norm_num : (0 : ℝ) < 1 / 2)).mp (Metric.mem_ball.mp hx)
  have hw : ∀ i, (1 / 2 : ℝ) ≤ thinBoxWidths n r i := by
    intro i; simp only [thinBoxWidths]; split_ifs <;> first | exact hr | rfl
  change -thinBoxWidths n r ≤ x ∧ x ≤ thinBoxWidths n r
  constructor <;> intro i
  · have hh := abs_lt.mp (show |x i| < 1 / 2 by simpa [Real.dist_eq] using hcoord i)
    change -(thinBoxWidths n r i) ≤ x i
    linarith [hw i]
  · have hh := abs_lt.mp (show |x i| < 1 / 2 by simpa [Real.dist_eq] using hcoord i)
    linarith [hw i]

theorem thinBox_cube_covering_constant_lt_minima (n : ℕ) (hn : 0 < n) :
    (1 + coveringRadius (thinBox n (1 / 2))) ^ (n + 1) <
      ∏ i : Fin (n + 1), (1 + (n + 1 : ℝ) *
        DiscreteMinkowski.successiveMinimum (thinBox n (1 / 2))
          (standardIntegerLattice (n + 1)) (i.1 + 1) / 2) := by
  rw [thinBox_covering_constant n le_rfl, thinBox_minima_constant n le_rfl]
  have he : (1 + (n + 1 : ℝ) * (1 / 2 : ℝ)⁻¹ / 2) = (n + 2 : ℝ) := by ring
  rw [he, ← pow_succ]
  exact pow_lt_pow_left₀ (by exact_mod_cast (show 2 < n + 2 by omega))
    (by norm_num) (by omega)

private theorem dimension_plus_one_lt_power (n : ℕ) (hn : 0 < n) : n + 2 < 2 ^ (n + 1) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hz : n = 0
    · subst n; norm_num
    · have hh := ih (by omega)
      rw [pow_succ]
      omega

theorem eventually_thinBox_minima_constant_lt_covering (n : ℕ) (hn : 0 < n) :
    ∀ᶠ r : ℝ in atTop,
      (∏ i : Fin (n + 1), (1 + (n + 1 : ℝ) *
        DiscreteMinkowski.successiveMinimum (thinBox n r)
          (standardIntegerLattice (n + 1)) (i.1 + 1) / 2)) <
        (1 + coveringRadius (thinBox n r)) ^ (n + 1) := by
  have hgap : (n + 2 : ℝ) < (2 : ℝ) ^ (n + 1) := by
    exact_mod_cast dimension_plus_one_lt_power n hn
  have he := (thinBox_minima_constant_limit n).eventually (gt_mem_nhds hgap)
  filter_upwards [he, eventually_ge_atTop (1 / 2 : ℝ)] with r hr hhalf
  rwa [thinBox_covering_constant n hhalf]

end
end LatticeVolumeInterpolation
