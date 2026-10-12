module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Tactic

/-!
# Infinite power integrals in observability

Computations for paper `e1a0fd5`, `equations.tex` lines 1742–1752,
1796–1803.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory Filter
open scoped Topology

/-- Exact integral used in the weighted Volterra norm; paper `e1a0fd5`,
`eq:observability-power-operator-bound`, lines 1742–1747. -/
theorem observability_power_integral {r q : ℝ} (hr : 0 < r) (hq : q < 1) :
    (∫ ξ in Ioi (0 : ℝ), (r + ξ / 2) ^ (q - 2)) =
      2 * r ^ (q - 1) / (1 - q) := by
  let G : ℝ → ℝ := fun ξ ↦ 2 * (r + ξ / 2) ^ (q - 1) / (q - 1)
  have hder (ξ : ℝ) (hξ : ξ ∈ Ici 0) : HasDerivAt G ((r + ξ / 2) ^ (q - 2)) ξ := by
    have hb : r + ξ / 2 ≠ 0 := by linarith [show 0 ≤ ξ from hξ]
    have hq0 : q - 1 ≠ 0 := by linarith
    convert ((((hasDerivAt_id ξ).div_const 2).const_add r).rpow_const
      (p := q - 1) (Or.inl hb)).const_mul 2 |>.div_const (q - 1) using 1
    · rfl
    · norm_num only [sub_sub, id_eq]
      field_simp
  have ht : Tendsto G atTop (𝓝 0) := by
    have hbase : Tendsto (fun ξ : ℝ ↦ r + ξ / 2) atTop atTop :=
      tendsto_atTop_add_const_left _ r
        (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2))
    have hpow : Tendsto (fun ξ : ℝ ↦ (r + ξ / 2) ^ (q - 1)) atTop (𝓝 0) := by
      simpa only [neg_sub, Function.comp_def] using
        (tendsto_rpow_neg_atTop (by linarith : 0 < 1 - q)).comp hbase
    simpa [G] using (hpow.const_mul 2).div_const (q - 1)
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hder
    (by intro ξ hξ; exact Real.rpow_nonneg (by linarith [show 0 < ξ from hξ]) _) ht]
  dsimp [G]
  simp only [zero_div, add_zero, zero_sub]
  have hq0 : q - 1 ≠ 0 := by linarith
  have hq1 : 1 - q ≠ 0 := by linarith
  field_simp
  ring

/-- The full coefficient of the power estimate; paper `e1a0fd5`,
`eq:observability-power-operator-bound`, lines 1742–1747. -/
theorem observability_power_integral_scaled {r q p : ℝ} (hr : 0 < r) (hq : q < 1) :
    4 * p / (2 - q) * (∫ ξ in Ioi (0 : ℝ), (r + ξ / 2) ^ (q - 2)) =
      8 * p / ((2 - q) * (1 - q)) * r ^ (q - 1) := by
  rw [observability_power_integral hr hq]
  field_simp
  ring

/-- The `x^(-5/2)` tail has coefficient `2/3`; paper `e1a0fd5`,
`equations.tex` lines 1796–1803. -/
theorem observability_tail_five_halves {r : ℝ} (hr : 0 < r) :
    (∫ x in Ioi r, x ^ (-5 / 2 : ℝ)) = (2 / 3) * r ^ (-3 / 2 : ℝ) := by
  rw [integral_Ioi_rpow_of_lt (by norm_num : (-5 / 2 : ℝ) < -1) hr]
  norm_num
  ring

/-- The `x^(-7/2)` tail has coefficient `2/5`; paper `e1a0fd5`,
`equations.tex` lines 1796–1803. -/
theorem observability_tail_seven_halves {r : ℝ} (hr : 0 < r) :
    (∫ x in Ioi r, x ^ (-7 / 2 : ℝ)) = (2 / 5) * r ^ (-5 / 2 : ℝ) := by
  rw [integral_Ioi_rpow_of_lt (by norm_num : (-7 / 2 : ℝ) < -1) hr]
  norm_num
  ring

/-- An explicit sufficient bound for the square-root tail; paper `e1a0fd5`,
`equations.tex` lines 1796–1803. -/
theorem observability_sqrt_tail_le {r : ℝ} (hr : 0 < r) :
    (∫ x in Ioi r, Real.sqrt (x - r) / x ^ 3) ≤ (2 / 3) * r ^ (-3 / 2 : ℝ) := by
  have hpoint (x : ℝ) (hx : x ∈ Ioi r) :
      Real.sqrt (x - r) / x ^ 3 ≤ x ^ (-5 / 2 : ℝ) := by
    have hx0 : 0 < x := hr.trans hx
    calc
      _ ≤ Real.sqrt x / x ^ 3 := div_le_div_of_nonneg_right
        (Real.sqrt_le_sqrt (by linarith)) (by positivity)
      _ = x ^ (-5 / 2 : ℝ) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast x 3,
          ← Real.rpow_sub hx0]
        norm_num
  have hi := integrableOn_Ioi_rpow_of_lt (by norm_num : (-5 / 2 : ℝ) < -1) hr
  have hn : ∀ᵐ x ∂volume.restrict (Ioi r), 0 ≤ Real.sqrt (x - r) / x ^ 3 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact div_nonneg (Real.sqrt_nonneg _) (pow_nonneg (hr.trans hx).le _)
  have hb : ∀ᵐ x ∂volume.restrict (Ioi r), Real.sqrt (x - r) / x ^ 3 ≤
      x ^ (-5 / 2 : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact hpoint x hx
  exact (integral_mono_of_nonneg hn hi hb).trans_eq (observability_tail_five_halves hr)

end AcExtensionPrinciple

end
