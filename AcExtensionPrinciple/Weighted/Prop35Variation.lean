module

public import AcExtensionPrinciple.Decay.ScalarVariation
public import AcExtensionPrinciple.ACDatum.Propagation
public import AcExtensionPrinciple.Weighted.ClassInitialTransport
public import AcExtensionPrinciple.Weighted.Lemma33Remainder
public import AcExtensionPrinciple.Renormalized.ClassSplitting

/-!
# Absorbing the cubic contribution to outgoing variation

Helpers for paper `e1a0fd5`, `prop:small-outgoing-bv-cones`,
`equations.tex` lines 1333–1345. The Hardy conclusion is an explicit
Lemma 3.1 input, with its integrability stated to avoid undefined integrals.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- The cubic Hardy contribution can be absorbed in a finite variation.
Paper `e1a0fd5`, `eq:outgoing-variation-remainder`, lines 1338–1345.
Here `g` is the nonnegative Hardy integrand, and `a,b` are the initial
and remainder contributions to the outgoing derivative. -/
theorem ac_variation_le_of_cubic_hardy {P a b g : ℝ → ℝ} {u C ε : ℝ}
    (hu : u ≤ 0) (hP : AbsolutelyContinuousOnInterval P u 0)
    (ha : IntervalIntegrable a volume u 0) (hb : IntervalIntegrable b volume u 0)
    (hg : IntervalIntegrable g volume u 0)
    (hderiv : ∀ᵐ v ∂volume.restrict (Ioc u 0),
      |deriv P v| ≤ C * (|a v| + |b v|) + ε ^ 2 * g v)
    (hHardy : (∫ v in u..0, g v) ≤ (eVariationOn P (Icc u 0)).toReal)
    (hε : ε ^ 2 < 1) :
    eVariationOn P (Icc u 0) ≤ ENNReal.ofReal
      (C / (1 - ε ^ 2) * ((∫ v in u..0, |a v|) + ∫ v in u..0, |b v|)) := by
  have hV : eVariationOn P (Icc u 0) ≠ ⊤ := by
    have hbv : BoundedVariationOn P (Icc u 0) := by
      simpa only [uIcc_of_le hu] using hP.boundedVariationOn
    exact hbv
  have hd : (∫ v in u..0, |deriv P v|) ≤
      C * ((∫ v in u..0, |a v|) + ∫ v in u..0, |b v|) +
        ε ^ 2 * ∫ v in u..0, g v := by
    calc
      _ ≤ ∫ v in u..0, C * (|a v| + |b v|) + ε ^ 2 * g v :=
        intervalIntegral.integral_mono_ae_restrict hu hP.intervalIntegrable_deriv.abs
          (((ha.abs.add hb.abs).const_mul C).add (hg.const_mul _))
          (by
            rw [← restrict_Ioc_eq_restrict_Icc]
            exact hderiv)
      _ = _ := by
        rw [intervalIntegral.integral_add ((ha.abs.add hb.abs).const_mul C)
          (hg.const_mul _), intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_add ha.abs hb.abs]
  have hv := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (ac_variation_le_integral_abs_deriv hu hP)
  rw [ENNReal.toReal_ofReal (intervalIntegral.integral_nonneg hu
    (fun _ _ => abs_nonneg _))] at hv
  have hh := mul_le_mul_of_nonneg_left hHardy (sq_nonneg ε)
  have hbnd : (eVariationOn P (Icc u 0)).toReal ≤
      C / (1 - ε ^ 2) * ((∫ v in u..0, |a v|) + ∫ v in u..0, |b v|) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (sub_pos.mpr hε)).mpr
    nlinarith
  rw [← ENNReal.ofReal_toReal hV]
  exact ENNReal.ofReal_le_ofReal hbnd

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The outgoing derivative decomposes into the two renormalized pieces
and the cubic term. Paper `e1a0fd5`, lines 1333–1337.
The derivative representative is exactly `radialDatumDerivative`. -/
theorem outgoing_derivative_renormalized_splitting {u v : ℝ}
    (hu : ui ≤ u) (hu0 : u < 0) (huv : u < v) (hv0 : v ≤ 0) :
    deriv (S.outgoingDatum u) v =
      (S.renormalizedInitial S.radialDatumDerivative ui u v +
        S.renormalizedRemainder S.radialDatumDerivative ui u v) / (1 - S.mu u v) +
      S.lam u v / S.r u v * (S.r u v / S.lam u v * S.dvphi u v) ^ 3 := by
  have hp : (u, v) ∈ pastTriangle ui := ⟨hu, hu0, huv.le, hv0⟩
  have hl := (h.lam_pos hp).ne'
  have hr := (h.r_pos hp huv).ne'
  have hm := (sub_pos.mpr (h.mu_bounds hp).2).ne'
  dsimp [SSFields.renormalizedRemainder, SSFields.renormalizedDerivative,
    Renormalized.renormalizedDerivativeOf, SSFields.radialDatumDerivative, SSFields.mu] at *
  field_simp [hl, hr, hm]
  ring

/-- The class-level outgoing variation estimate after absorbing the cubic
Hardy contribution. Paper `e1a0fd5`, `eq:outgoing-variation-remainder`,
lines 1333–1345. The explicit integrability/Hardy inputs are the Lemma 3.1
Hardy conclusion and Lemma 3.2 cone L¹ conclusions. -/
theorem outgoingVariation_le_initial_and_remainder_of_hardy
    {u₀ u δ ε : ℝ} (hu : ui ≤ u) (hu0 : u < 0) (hu₀ : u₀ ≤ u)
    (hε : ε ^ 2 < 1)
    (hsmall : WeightedLateSmallness ui S u₀ δ ε)
    (hi : IntervalIntegrable
      (S.renormalizedDerivative S.radialDatumDerivative ui) volume u 0)
    (hR : IntervalIntegrable
      (S.renormalizedRemainder S.radialDatumDerivative ui u) volume u 0)
    (hg : IntervalIntegrable (fun v => S.lam u v / S.r u v *
      |S.r u v / S.lam u v * S.dvphi u v|) volume u 0)
    (hHardy : (∫ v in u..0, S.lam u v / S.r u v *
      |S.r u v / S.lam u v * S.dvphi u v|) ≤ (S.outgoingVariation u).toReal) :
    S.outgoingVariation u ≤ ENNReal.ofReal
      ((weightedGapConstant ui S)⁻¹ * ((weightedGapConstant ui S)⁻¹ + 1) /
        (1 - ε ^ 2) * ((∫ v in u..0,
          |S.renormalizedDerivative S.radialDatumDerivative ui v|) +
          ∫ v in u..0, |S.renormalizedRemainder S.radialDatumDerivative ui u v|)) := by
  let c := (weightedGapConstant ui S)⁻¹
  have hc : 0 < c := inv_pos.mpr h.weightedGapConstant_pos
  apply ac_variation_le_of_cubic_hardy hu0.le (h.normalized_datum_ac_out hu hu0)
    hi hR hg ?_ hHardy hε
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
  have hp : (u, v) ∈ pastTriangle ui := ⟨hu, hu0, hv.1.le, hv.2⟩
  have hr := h.r_pos hp hv.1
  have hl := h.lam_pos hp
  have hgap := sub_pos.mpr (h.mu_bounds hp).2
  have hin := h.weightedTransportedDatum_abs_le hp
    (S.renormalizedDerivative S.radialDatumDerivative ui)
  change |S.renormalizedInitial S.radialDatumDerivative ui u v| ≤
    c * |S.renormalizedDerivative S.radialDatumDerivative ui v| at hin
  have ha := ((hsmall (u, v) hp hu₀).2.trans' (le_add_of_nonneg_right
    (abs_nonneg (weightedIncomingAmplitude S u v))))
  have hcubic : |S.lam u v / S.r u v *
      (S.r u v / S.lam u v * S.dvphi u v) ^ 3| ≤
        ε ^ 2 * (S.lam u v / S.r u v * |S.r u v / S.lam u v * S.dvphi u v|) := by
    rw [abs_mul, abs_of_pos (div_pos hl hr), abs_pow]
    have hs := pow_le_pow_left₀ (abs_nonneg _) ha 2
    calc
      _ = (S.lam u v / S.r u v * |S.r u v / S.lam u v * S.dvphi u v|) *
          |S.r u v / S.lam u v * S.dvphi u v| ^ 2 := by ring
      _ ≤ (S.lam u v / S.r u v * |S.r u v / S.lam u v * S.dvphi u v|) * ε ^ 2 := by
        gcongr
      _ = _ := by ring
  have hlinear : |(S.renormalizedInitial S.radialDatumDerivative ui u v +
      S.renormalizedRemainder S.radialDatumDerivative ui u v) / (1 - S.mu u v)| ≤
        c * (c + 1) * (|S.renormalizedDerivative S.radialDatumDerivative ui v| +
          |S.renormalizedRemainder S.radialDatumDerivative ui u v|) := by
    rw [abs_div, abs_of_pos hgap]
    calc
      _ ≤ (|S.renormalizedInitial S.radialDatumDerivative ui u v| +
          |S.renormalizedRemainder S.radialDatumDerivative ui u v|) / (1 - S.mu u v) :=
        div_le_div_of_nonneg_right (abs_add_le _ _) hgap.le
      _ ≤ (c * |S.renormalizedDerivative S.radialDatumDerivative ui v| +
          |S.renormalizedRemainder S.radialDatumDerivative ui u v|) /
          weightedGapConstant ui S := by
        apply div_le_div₀ (by positivity) (add_le_add hin le_rfl)
          h.weightedGapConstant_pos (h.mass_gap_lower hp)
      _ = c * (c * |S.renormalizedDerivative S.radialDatumDerivative ui v| +
          |S.renormalizedRemainder S.radialDatumDerivative ui u v|) := by
        dsimp [c]
        ring
      _ ≤ _ := by
        nlinarith [mul_nonneg hc.le (abs_nonneg
          (S.renormalizedDerivative S.radialDatumDerivative ui v)),
          mul_nonneg (sq_nonneg c) (abs_nonneg
          (S.renormalizedRemainder S.radialDatumDerivative ui u v))]
  change |deriv (S.outgoingDatum u) v| ≤
    c * (c + 1) * (|S.renormalizedDerivative S.radialDatumDerivative ui v| +
      |S.renormalizedRemainder S.radialDatumDerivative ui u v|) +
      ε ^ 2 * (S.lam u v / S.r u v * |S.r u v / S.lam u v * S.dvphi u v|)
  rw [h.outgoing_derivative_renormalized_splitting hu hu0 hv.1 hv.2]
  exact (abs_add_le _ _).trans (add_le_add hlinear hcubic)

end StandingFull

end AcExtensionPrinciple

end
