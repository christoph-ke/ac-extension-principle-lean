module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Tactic

/-!
# Exact time-oscillation integral

Computation for paper `e1a0fd5`,
`eq:observability-time-oscillation-kernel`, `equations.tex` lines 1749–1752.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory Filter
open scoped Topology

/-- The rational moment behind the square-root kernel; paper `e1a0fd5`,
`eq:observability-time-oscillation-kernel`, lines 1749–1752. -/
theorem oscillation_rational_moment :
    (∫ x in Ioi (0 : ℝ), x ^ 2 / (1 + x ^ 2) ^ 2) = Real.pi / 4 := by
  let G : ℝ → ℝ := fun x ↦ (Real.arctan x - x / (1 + x ^ 2)) / 2
  have hd (x : ℝ) (_hx : x ∈ Ici 0) :
      HasDerivAt G (x ^ 2 / (1 + x ^ 2) ^ 2) x := by
    have hn : 1 + x ^ 2 ≠ 0 := by positivity
    convert ((Real.hasDerivAt_arctan x).sub
      ((hasDerivAt_id x).div (((hasDerivAt_id x).pow 2).const_add 1) hn)).div_const 2
      using 1
    · rfl
    · simp only [Pi.pow_apply, id_eq]
      field_simp
      ring
  have hr : Tendsto (fun x : ℝ ↦ x / (1 + x ^ 2)) atTop (𝓝 0) := by
    apply squeeze_zero' (g := fun x : ℝ ↦ x⁻¹)
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      positivity
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      apply (div_le_iff₀ (by positivity : 0 < 1 + x ^ 2)).mpr
      rw [← one_div]
      rw [div_mul_eq_mul_div, one_mul]
      apply (le_div_iff₀ hx).mpr
      nlinarith
    · exact tendsto_inv_atTop_zero
  have ht : Tendsto G atTop (𝓝 (Real.pi / 4)) := by
    have ha := Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds
    convert (ha.sub hr).div_const 2 using 1
    congr 1
    ring
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hd
    (by intro x _; positivity) ht]
  simp [G]

/-- Exact time-oscillation constant `π√2`; paper `e1a0fd5`,
`eq:observability-time-oscillation-kernel`, lines 1749–1752. -/
theorem observability_time_oscillation_integral {r : ℝ} (hr : 0 < r) :
    (∫ ξ in Ioi (0 : ℝ), Real.sqrt ξ / (r + ξ / 2) ^ 2) =
      Real.pi * Real.sqrt 2 / Real.sqrt r := by
  let f : ℝ → ℝ := fun ξ ↦ Real.sqrt ξ / (r + ξ / 2) ^ 2
  have hsub := integral_comp_rpow_Ioi_of_pos (g := f) (by norm_num : (0 : ℝ) < 2)
  have hsub' : (∫ x in Ioi (0 : ℝ), 2 * x ^ 2 / (r + x ^ 2 / 2) ^ 2) =
      ∫ ξ in Ioi (0 : ℝ), f ξ := by
    rw [← hsub]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp [f]
    norm_num only [Real.rpow_two, Real.rpow_one, smul_eq_mul]
    rw [Real.sqrt_sq (le_of_lt hx)]
    ring
  let a : ℝ := Real.sqrt (2 * r)
  have ha : 0 < a := Real.sqrt_pos.mpr (by positivity)
  have ha2 : a ^ 2 = 2 * r := Real.sq_sqrt (by positivity)
  let g : ℝ → ℝ := fun x ↦ 2 * x ^ 2 / (r + x ^ 2 / 2) ^ 2
  have hg (x : ℝ) : g (a * x) = (4 / r) * (x ^ 2 / (1 + x ^ 2) ^ 2) := by
    dsimp [g]
    rw [mul_pow, ha2]
    have hn : 1 + x ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  have hscale := integral_comp_mul_left_Ioi g 0 ha
  simp only [mul_zero, smul_eq_mul] at hscale
  have hscale' : (∫ x in Ioi (0 : ℝ), g x) =
      a * ((4 / r) * (Real.pi / 4)) := by
    rw [show (fun x ↦ g (a * x)) = (fun x ↦ (4 / r) * (x ^ 2 / (1 + x ^ 2) ^ 2))
      from funext hg, integral_const_mul, oscillation_rational_moment] at hscale
    have hh := congrArg (fun z : ℝ ↦ a * z) hscale
    simpa only [← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul] using hh.symm
  rw [← hsub']
  change (∫ x in Ioi (0 : ℝ), g x) = _
  rw [hscale']
  dsimp [a]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hs : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr.le
  have hs0 : Real.sqrt r ≠ 0 := (Real.sqrt_pos.mpr hr).ne'
  field_simp
  nlinarith

end AcExtensionPrinciple

end
