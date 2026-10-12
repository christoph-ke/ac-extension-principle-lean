module

public import AcExtensionPrinciple.Observability.LemmaA3Weight
public import AcExtensionPrinciple.Observability.LemmaA3Calculus

/-!
# Lemma A.3: AC Gronwall with the sharp annular factor

Paper `e1a0fd5`, `eq:observability-annular-differential`,
`eq:observability-annular-gronwall`, lines 1593–1621.
Internal premises are radius and mass primitives, lapse/scalar estimates,
and the boundary flux integrals, all discharged from normalized chart data.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory

/-- The annular AC integrating-factor estimate. Paper `e1a0fd5`,
`eq:observability-annular-gronwall` and `eq:observability-annular-exponent`,
lines 1607–1621. `A` bounds the coefficient of outgoing boundary flux. -/
theorem lemmaA3_weighted_gronwall {z D v F : ℝ → ℝ} {p b τ : ℝ}
    (hτ : 0 ≤ τ) (hp : 0 ≤ p)
    (hz : AbsolutelyContinuousOnInterval z 0 τ)
    (hD : AbsolutelyContinuousOnInterval D 0 τ)
    (hpos : ∀ s ∈ Icc 0 τ, 2 * p < z s)
    (hupper : ∀ s ∈ Icc 0 τ, z s ≤ b)
    (hDpos : ∀ s ∈ Icc 0 τ, 0 ≤ D s) (hD0 : D 0 = 0)
    (hF : IntervalIntegrable F volume 0 τ) (hFpos : ∀ s ∈ Icc 0 τ, 0 ≤ F s)
    (hder : ∀ᵐ s, s ∈ Ioo 0 τ → HasDerivAt z (v s) s ∧
      v s ≤ -(1 - 2 * p / z s) ∧
      deriv D s ≤ F s + 2 * ((z s)⁻¹ - b⁻¹) / (1 - 2 * p / z s) * D s) :
    D τ * lemmaA3Weight p (z τ) ≤ b ^ 2 * (∫ s in 0..τ, F s) := by
  have hw := lemmaA3Weight_ac hz (by
    intro s hs
    rw [uIcc_of_le hτ] at hs
    exact hpos s hs)
  have hprod : AbsolutelyContinuousOnInterval (fun s => D s * lemmaA3Weight p (z s)) 0 τ := by
    convert hD.mul hw using 1
  have hi : (∫ s in 0..τ, deriv (fun s => D s * lemmaA3Weight p (z s)) s) ≤
      ∫ s in 0..τ, b ^ 2 * F s := by
    apply intervalIntegral.integral_mono_ae_restrict hτ hprod.intervalIntegrable_deriv
      (hF.const_mul _)
    rw [Filter.EventuallyLE, ← restrict_Ioo_eq_restrict_Icc, ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hder, hD.ae_differentiableAt] with s hs hd hsI
    have hscc : s ∈ Icc 0 τ := ⟨hsI.1.le, hsI.2.le⟩
    have hDz := (hd (by simpa [uIcc_of_le hτ] using hscc)).hasDerivAt
    have hzs := (hs hsI).1
    have hwt : HasDerivAt (fun s => lemmaA3Weight p (z s))
        (lemmaA3Weight p (z s) * (2 / (z s - 2 * p) + 4 * p / (z s - 2 * p) ^ 2) * v s) s := by
      convert (lemmaA3Weight_hasDerivAt (hpos s hscc)).comp s hzs using 1
      funext x
      rfl
    have hfun : (fun s => D s * lemmaA3Weight p (z s)) = (D * fun s => lemmaA3Weight p (z s)) := by
      funext x
      rfl
    rw [hfun, (hDz.mul hwt).deriv]
    have hwb := lemmaA3Weight_bounds hp (hpos s hscc) (hupper s hscc)
    have hDrift := lemmaA3Weight_drift hp (hpos s hscc) (hupper s hscc) (hs hsI).2.1
    have hmul := mul_le_mul_of_nonneg_right (hs hsI).2.2 hwb.1.le
    have hcancel := mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (hDpos s hscc) hwb.1.le) hDrift
    have hbound := mul_le_mul_of_nonneg_right hwb.2 (hFpos s hscc)
    nlinarith
  rw [hprod.integral_deriv_eq_sub, intervalIntegral.integral_const_mul, hD0, zero_mul, sub_zero] at hi
  exact hi

end AcExtensionPrinciple

end
