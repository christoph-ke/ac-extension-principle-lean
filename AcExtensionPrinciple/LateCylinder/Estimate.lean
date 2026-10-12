module

public import AcExtensionPrinciple.LateCylinder.Trace
public import AcExtensionPrinciple.LateCylinder.Geometry

/-!
# Integrated variation estimate on a cylinder

Paper `e1a0fd5`, `eq:cylinder-datum-derivative` and
`eq:late-cylinder-variation`, equations.tex lines 819–833.
The two smooth terms are integrated in boundary time; the transported
initial term is controlled by its monotone variation tail.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory

/-- The fixed-radius source coefficient is small when μ ≤ ε.
Paper `e1a0fd5`, the second term of
`eq:cylinder-datum-derivative`, lines 819–823. -/
theorem cylinder_coefficient_amplitude_bound {b mu A M K eps : ℝ}
    (hb : 0 < b) (hK : 0 < K) (hgap : K⁻¹ ≤ 1 - mu)
    (hmu0 : 0 ≤ mu) (hmu : mu ≤ eps) (hM : 0 ≤ M) (hA : |A| ≤ M) :
    |varkappaOf b mu / (1 - mu) * A| ≤ M * K * eps / b := by
  have hg : 0 < 1 - mu := (inv_pos.mpr hK).trans_le hgap
  have heps0 : 0 ≤ eps := hmu0.trans hmu
  have hm : 0 ≤ mu / b := div_nonneg hmu0 hb.le
  have heq : |varkappaOf b mu / (1 - mu) * A| =
      |A| * (mu / b) * (1 - mu)⁻¹ := by
    dsimp [varkappaOf]
    rw [abs_mul, abs_div, abs_of_nonneg hm, abs_of_pos hg]
    ring
  have hi : (1 - mu)⁻¹ ≤ K := by
    simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr hK) hgap
  rw [heq]
  calc
    _ ≤ M * (eps / b) * K := by
      gcongr
    _ = _ := by ring

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Integrate the separated cylinder derivative to obtain TV ≤ Cε.
All analytic premises are the proved cylinder trace calculus; the remainder
premise is the delayed dilution estimate. Paper `e1a0fd5`,
`eq:late-cylinder-variation`, equations.tex lines 819–833. -/
theorem late_variation_from_trace_bounds {v : ℝ → ℝ} {K M R H b eps a0 a1 : ℝ}
    (hK : LateCylinderGeometry ui S K) (hM : 0 ≤ M) (hR : 0 ≤ R) (_hH : 0 ≤ H)
    (hb : 0 < b) (heps : 0 < eps) (ha : a0 ≤ a1)
    (hv : ContinuousOn v (Icc a0 a1))
    (hp : ∀ u ∈ Icc a0 a1, (u, v u) ∈ pastTriangle ui)
    (hr : ∀ u ∈ Icc a0 a1, S.r u (v u) = b)
    (hmu : ∀ u ∈ Icc a0 a1, S.mu u (v u) ≤ eps)
    (hamp : ∀ u ∈ Icc a0 a1, |outgoingAmplitude S u (v u)| ≤ M)
    (hrem : ∀ u ∈ Icc a0 a1, |radialDatumRemainderIntegral ui S u (v u)| ≤ R * eps / b)
    (hP : AbsolutelyContinuousOnInterval (lateCylinderDatum S v) a0 a1)
    (hF : AbsolutelyContinuousOnInterval (fun u => S.dvpsi ui (v u)) a0 a1)
    (hd : ∀ᵐ u, u ∈ Ioo a0 a1 → deriv (lateCylinderDatum S v) u =
      deriv (fun s => S.dvpsi ui (v s)) u / S.lam u (v u) + (-S.nu u (v u)) *
        (radialDatumRemainderIntegral ui S u (v u) +
          S.varkappa u (v u) / (1 - S.mu u (v u)) * outgoingAmplitude S u (v u)))
    (htail : (∫ u in a0..a1, |deriv (fun s => S.dvpsi ui (v s)) u|) ≤ eps)
    (htime : lateCylinderTime S v a0 a1 ≤ H * b) :
    eVariationOn (lateCylinderDatum S v) (Icc a0 a1) ≤
      ENNReal.ofReal ((K + (R + M * K) * H) * eps) := by
  have hK0 : 0 < K := zero_lt_one.trans_le hK.1
  let F := fun u => S.dvpsi ui (v u)
  let N := fun u => -S.nu u (v u)
  let T := (R + M * K) * eps / b
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hNc : ContinuousOn N (Icc a0 a1) :=
    (h.regularCenter.continuous_nu.comp (continuousOn_id.prodMk hv) hp).neg
  have hNi := hNc.intervalIntegrable_of_Icc (μ := volume) ha
  have hFi := hF.intervalIntegrable_deriv.abs
  have hi : (∫ u in a0..a1, |deriv (lateCylinderDatum S v) u|) ≤
      ∫ u in a0..a1, K * |deriv F u| + T * N u := by
    apply intervalIntegral.integral_mono_ae_restrict ha hP.intervalIntegrable_deriv.abs
      ((hFi.const_mul K).add (hNi.const_mul T))
    rw [Filter.EventuallyLE, ← restrict_Ioo_eq_restrict_Icc,
      ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hd] with u hdu hu
    have huC := Ioo_subset_Icc_self hu
    have hl := h.lam_pos (hp u huC)
    have hn := neg_pos.mpr (h.nu_neg (hp u huC))
    have hlInv : (S.lam u (v u))⁻¹ ≤ K := by
      simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr hK0) (hK.2 _ (hp u huC)).1
    have hcoeff : |S.varkappa u (v u) / (1 - S.mu u (v u)) * outgoingAmplitude S u (v u)| ≤
        M * K * eps / b := by
      rw [SSFields.varkappa, hr u huC]
      exact cylinder_coefficient_amplitude_bound hb hK0 (hK.2 _ (hp u huC)).2.1
        (h.mu_bounds (hp u huC)).1 (hmu u huC) hM (hamp u huC)
    have hsmooth : |radialDatumRemainderIntegral ui S u (v u) +
        S.varkappa u (v u) / (1 - S.mu u (v u)) * outgoingAmplitude S u (v u)| ≤ T := by
      exact (abs_add_le _ _).trans ((add_le_add (hrem u huC) hcoeff).trans_eq
        (by dsimp [T]; ring))
    rw [hdu hu]
    calc
      _ ≤ |deriv F u / S.lam u (v u)| +
          |(-S.nu u (v u)) * (radialDatumRemainderIntegral ui S u (v u) +
            S.varkappa u (v u) / (1 - S.mu u (v u)) * outgoingAmplitude S u (v u))| :=
        abs_add_le _ _
      _ ≤ K * |deriv F u| + T * N u := by
        rw [abs_div, abs_of_pos hl, abs_mul, abs_of_pos hn]
        have hrough := mul_le_mul_of_nonneg_left hlInv (abs_nonneg (deriv F u))
        have hs := mul_le_mul_of_nonneg_left hsmooth hn.le
        dsimp only [N]
        simpa only [div_eq_mul_inv, mul_comm] using add_le_add hrough hs
  rw [intervalIntegral.integral_add (hFi.const_mul K) (hNi.const_mul T),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hi
  have hrough := mul_le_mul_of_nonneg_left htail hK0.le
  have hsmooth := mul_le_mul_of_nonneg_left htime hT
  have heq : T * (H * b) = (R + M * K) * H * eps := by dsimp [T]; field_simp
  rw [heq] at hsmooth
  have hbound : (∫ u in a0..a1, |deriv (lateCylinderDatum S v) u|) ≤
      (K + (R + M * K) * H) * eps := by
    dsimp only [lateCylinderTime] at hsmooth
    nlinarith only [hi, hrough, hsmooth]
  exact (ac_variation_le_integral_abs_deriv ha hP).trans (ENNReal.ofReal_le_ofReal hbound)

end StandingFull

end AcExtensionPrinciple

end
