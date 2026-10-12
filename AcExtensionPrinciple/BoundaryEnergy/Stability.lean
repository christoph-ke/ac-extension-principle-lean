module

public import AcExtensionPrinciple.BoundaryEnergy.Integral
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Boundary energy stability

Source: paper commit `e1a0fd5`, `equations.tex` lines 700–706,
729 (`eq:boundary-energy-stability`). Includes the variation bound for the integral
of the absolute derivative, proved using Mathlib's Jordan decomposition.
-/

public section

namespace AcExtensionPrinciple

open MeasureTheory Set Filter
open scoped Topology

/-- The integral of the absolute derivative is at most total variation (even for BV functions);
paper `e1a0fd5`, calculus input to `eq:boundary-energy-stability`, lines 700–706, 729. -/
theorem integral_abs_deriv_le_variation {P : ℝ → ℝ} {a0 a1 : ℝ}
    (ha : a0 ≤ a1) (hP : BoundedVariationOn P (Icc a0 a1)) :
    (∫ x in a0..a1, |deriv P x|) ≤ (eVariationOn P (Icc a0 a1)).toReal := by
  obtain ⟨p, q, hp, hq, hPQ, hv⟩ :=
    hP.locallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn'
  have hpU : MonotoneOn p (uIcc a0 a1) := by rwa [uIcc_of_le ha]
  have hqU : MonotoneOn q (uIcc a0 a1) := by rwa [uIcc_of_le ha]
  have hiP : IntervalIntegrable (deriv P) volume a0 a1 :=
    (show BoundedVariationOn P (uIcc a0 a1) by rwa [uIcc_of_le ha]).intervalIntegrable_deriv
  have hieq : (∫ x in a0..a1, |deriv P x|) ≤
      ∫ x in a0..a1, deriv p x + deriv q x := by
    apply intervalIntegral.integral_mono_ae_restrict ha hiP.abs
      (hpU.intervalIntegrable_deriv.add hqU.intervalIntegrable_deriv)
    rw [Filter.EventuallyLE, ← restrict_Ioo_eq_restrict_Icc, ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hp.ae_differentiableWithinAt_of_mem,
      hq.ae_differentiableWithinAt_of_mem] with x hpx hqx hx
    have hxC : x ∈ Icc a0 a1 := Ioo_subset_Icc_self hx
    have hnhds : Icc a0 a1 ∈ 𝓝 x := Icc_mem_nhds hx.1 hx.2
    have hpD := (hpx hxC).differentiableAt hnhds
    have hqD := (hqx hxC).differentiableAt hnhds
    have hp0 : 0 ≤ deriv p x := by
      rw [← derivWithin_of_mem_nhds hnhds]
      exact hp.derivWithin_nonneg
    have hq0 : 0 ≤ deriv q x := by
      rw [← derivWithin_of_mem_nhds hnhds]
      exact hq.derivWithin_nonneg
    rw [hPQ, (hpD.hasDerivAt.sub hqD.hasDerivAt).deriv]
    simpa [abs_of_nonneg hp0, abs_of_nonneg hq0] using (abs_sub (deriv p x) (deriv q x))
  have hpi := hpU.intervalIntegral_deriv_mem_uIcc
  have hqi := hqU.intervalIntegral_deriv_mem_uIcc
  have hpm : p a0 ≤ p a1 := hp (by simp [ha]) (by simp [ha]) ha
  have hqm : q a0 ≤ q a1 := hq (by simp [ha]) (by simp [ha]) ha
  rw [uIcc_of_le (sub_nonneg.mpr hpm)] at hpi
  rw [uIcc_of_le (sub_nonneg.mpr hqm)] at hqi
  have hvar := hv a0 (by simp [ha]) a1 (by simp [ha])
  rw [variationOnFromTo.eq_of_le _ _ ha, inter_self] at hvar
  rw [intervalIntegral.integral_add hpU.intervalIntegrable_deriv hqU.intervalIntegrable_deriv]
    at hieq
  linarith [hpi.2, hqi.2]

/-- Regularized square root preserves AC on a nonnegative energy trace;
paper `e1a0fd5`, the `√(E+η)` step at `equations.tex` line 729. -/
theorem absolutelyContinuousOnInterval_sqrt_add {E : ℝ → ℝ} {a0 a1 eta : ℝ}
    (hE : AbsolutelyContinuousOnInterval E a0 a1)
    (hE0 : ∀ x ∈ uIcc a0 a1, 0 ≤ E x) (heta : 0 < eta) :
    AbsolutelyContinuousOnInterval (fun x ↦ Real.sqrt (E x + eta)) a0 a1 := by
  let K : NNReal := ⟨1 / (2 * Real.sqrt eta), by positivity⟩
  have hL : LipschitzOnWith K Real.sqrt (Ici eta) := by
    apply (convex_Ici eta).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (f' := fun x ↦ 1 / (2 * Real.sqrt x))
    · intro x hx
      exact (Real.hasDerivAt_sqrt (ne_of_gt (lt_of_lt_of_le heta hx))).hasDerivWithinAt
    · intro x hx
      change |1 / (2 * Real.sqrt x)| ≤ 1 / (2 * Real.sqrt eta)
      rw [abs_of_nonneg (by positivity)]
      exact one_div_le_one_div_of_le (by positivity)
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hx) (by norm_num))
  exact hL.comp_absolutelyContinuousOnInterval
    (fun x hx ↦ by simp only [mem_Ici]; linarith [hE0 x hx])
    (hE.add ((LipschitzWith.const eta).lipschitzOnWith.absolutelyContinuousOnInterval))

/-- Algebraic bound for the regularized energy derivative; paper `e1a0fd5`,
`eq:boundary-energy-stability`, lines 700–706 and 729. -/
theorem sqrt_energy_derivative_bound {b E A E' P' eta : ℝ}
    (hb : 0 < b) (hE0 : 0 ≤ E) (heta : 0 < eta)
    (hA : (b / 2) * A ^ 2 ≤ E) (hder : E' ≤ b * A * P') :
    E' / (2 * Real.sqrt (E + eta)) ≤ Real.sqrt (b / 2) * |P'| := by
  have hbhalf : 0 ≤ b / 2 := by positivity
  have hEs : 0 < E + eta := by linarith
  have hAs : Real.sqrt (b / 2) * |A| ≤ Real.sqrt (E + eta) := by
    have hs := Real.sqrt_le_sqrt (hA.trans (by linarith : E ≤ E + eta))
    rwa [Real.sqrt_mul hbhalf, Real.sqrt_sq_eq_abs] at hs
  have hscale : (b / 2) * |A| ≤ Real.sqrt (b / 2) * Real.sqrt (E + eta) := by
    calc
      _ = Real.sqrt (b / 2) * (Real.sqrt (b / 2) * |A|) := by
        rw [← mul_assoc, ← sq, Real.sq_sqrt hbhalf]
      _ ≤ _ := mul_le_mul_of_nonneg_left hAs (Real.sqrt_nonneg _)
  have hBA : b * |A| ≤ 2 * Real.sqrt (b / 2) * Real.sqrt (E + eta) := by
    linarith
  apply (div_le_iff₀ (by positivity : 0 < 2 * Real.sqrt (E + eta))).mpr
  calc
    E' ≤ b * A * P' := hder
    _ = b * (A * P') := by ring
    _ ≤ b * |A * P'| := mul_le_mul_of_nonneg_left (le_abs_self _) hb.le
    _ = (b * |A|) * |P'| := by rw [abs_mul]; ring
    _ ≤ (2 * Real.sqrt (b / 2) * Real.sqrt (E + eta)) * |P'| :=
      mul_le_mul_of_nonneg_right hBA (abs_nonneg _)
    _ = _ := by ring

/-- Stability before taking `η ↓ 0`; paper `e1a0fd5`,
`eq:boundary-energy-stability`, lines 700–706 and 729. Derivative inequalities
are stated a.e. on the open interval, in the ordinary Lebesgue measure. -/
theorem boundary_energy_stability_regularized {a0 a1 b eta : ℝ} {E P A : ℝ → ℝ}
    (ha : a0 ≤ a1) (hb : 0 < b) (heta : 0 < eta)
    (hE : AbsolutelyContinuousOnInterval E a0 a1)
    (hP : AbsolutelyContinuousOnInterval P a0 a1)
    (hE0 : ∀ x ∈ Icc a0 a1, 0 ≤ E x)
    (hA : ∀ x ∈ Icc a0 a1, (b / 2) * (A x) ^ 2 ≤ E x)
    (hder : ∀ᵐ x ∂volume, x ∈ Ioo a0 a1 → deriv E x ≤ b * A x * deriv P x) :
    Real.sqrt (E a1 + eta) ≤ Real.sqrt (E a0 + eta) +
      Real.sqrt (b / 2) * (eVariationOn P (Icc a0 a1)).toReal := by
  have hE0U : ∀ x ∈ uIcc a0 a1, 0 ≤ E x := by rwa [uIcc_of_le ha]
  have hs := absolutelyContinuousOnInterval_sqrt_add hE hE0U heta
  have hbound : (∫ x in a0..a1, deriv (fun s ↦ Real.sqrt (E s + eta)) x) ≤
      ∫ x in a0..a1, Real.sqrt (b / 2) * |deriv P x| := by
    apply intervalIntegral.integral_mono_ae_restrict ha hs.intervalIntegrable_deriv
      (hP.intervalIntegrable_deriv.abs.const_mul _)
    rw [Filter.EventuallyLE, ← restrict_Ioo_eq_restrict_Icc,
      ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hder, hE.ae_differentiableAt] with x hxder hxD hx
    have hxC : x ∈ Icc a0 a1 := Ioo_subset_Icc_self hx
    have hxU : x ∈ uIcc a0 a1 := by rwa [uIcc_of_le ha]
    have hdx := ((hxD hxU).hasDerivAt.add_const eta).sqrt
      (by linarith [hE0 x hxC] : E x + eta ≠ 0)
    rw [hdx.deriv]
    exact sqrt_energy_derivative_bound hb (hE0 x hxC) heta (hA x hxC) (hxder hx)
  rw [hs.integral_deriv_eq_sub, intervalIntegral.integral_const_mul] at hbound
  have hv := integral_abs_deriv_le_variation ha
    (show BoundedVariationOn P (Icc a0 a1) by
      simpa only [uIcc_of_le ha] using hP.boundedVariationOn)
  have hmul := mul_le_mul_of_nonneg_left hv (Real.sqrt_nonneg (b / 2))
  linarith

/-- Boundary energy stability C; paper `e1a0fd5`, `eq:boundary-energy-stability`,
lines 700–706 and 729. No separate BV assumption is needed, since `P` is AC.
The a.e. derivative inequality is imposed only on the open interval. -/
theorem boundary_energy_stability {a0 a1 b : ℝ} {E P A : ℝ → ℝ}
    (ha : a0 ≤ a1) (hb : 0 < b)
    (hE : AbsolutelyContinuousOnInterval E a0 a1)
    (hP : AbsolutelyContinuousOnInterval P a0 a1)
    (hE0 : ∀ x ∈ Icc a0 a1, 0 ≤ E x)
    (hA : ∀ x ∈ Icc a0 a1, (b / 2) * (A x) ^ 2 ≤ E x)
    (hder : ∀ᵐ x ∂volume, x ∈ Ioo a0 a1 → deriv E x ≤ b * A x * deriv P x) :
    Real.sqrt (E a1) ≤ Real.sqrt (E a0) +
      Real.sqrt (b / 2) * (eVariationOn P (Icc a0 a1)).toReal := by
  have hlim (x : ℝ) : Tendsto (fun eta : ℝ ↦ Real.sqrt (E x + eta))
      (𝓝[>] 0) (𝓝 (Real.sqrt (E x))) := by
    have hid : Tendsto (fun eta : ℝ ↦ eta) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id'.mpr nhdsWithin_le_nhds
    simpa only [Function.comp_def, add_zero] using
      (Real.continuous_sqrt.tendsto (E x + 0)).comp (hid.const_add (E x))
  apply le_of_tendsto_of_tendsto (hlim a1) ((hlim a0).add_const _)
  filter_upwards [self_mem_nhdsWithin] with eta heta
  exact boundary_energy_stability_regularized ha hb heta hE hP hE0 hA hder

end AcExtensionPrinciple

end
