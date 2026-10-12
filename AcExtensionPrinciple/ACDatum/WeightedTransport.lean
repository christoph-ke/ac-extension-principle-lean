module

public import AcExtensionPrinciple.ACDatum.DerivativeRepresentation
public import AcExtensionPrinciple.ACDatum.Remainder

/-!
# Incoming transport of the explicitly differentiated datum

Paper `e1a0fd5`, `eq:radial-datum-transport`, lines 564–570, 594–603.
The incoming primitives of the outgoing derivatives avoid any assumed
commutation theorem for weak mixed derivatives.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Incoming transport of the outgoing λ derivative, derived from its
integral representation. Paper `e1a0fd5`, lines 594–601. -/
theorem lambdaOutgoingDerivative_ae_transport {u v : ℝ}
    (hu : ui ≤ u) (hu0 : u < 0) (huv : u < v) (hv : v < 0) :
    ∀ᵐ s, s ∈ Ioo ui u → HasDerivAt (fun t => lambdaOutgoingDerivative ui S t v)
      (lambdaOutgoingDerivative ui S s v * incomingDatumCoeff S s v +
        S.lam s v * outgoingDatumCoeffDerivative S s v) s := by
  have hl := intervalPrimitive_ae_hasDerivAt hu
    (fun x hx => h.regularCenter.localBV.lam_in v ui x hx.1
      (inSeg_subset_offAxis le_rfl (hx.2.trans_lt hu0) (hx.2.trans_lt huv) hv.le))
  have hi : IntervalIntegrable (fun s => outgoingDatumCoeffDerivative S s v) volume ui u :=
    (h.outgoingDatumCoeffDerivative_continuous_in hu hu0 huv hv).intervalIntegrable_of_Icc hu
  filter_upwards [hl, hi.ae_hasDerivAt_integral] with s hls his
  intro hs
  have hd := his (by simpa only [uIcc_of_le hu] using Ioo_subset_Icc_self hs)
    ui left_mem_uIcc
  convert (hls hs).mul hd using 1
  · funext t
    simp only [lambdaOutgoingDerivative, Pi.mul_apply]
  · rw [S.radiusCoeff_eq_lam_gamma]
    dsimp only [lambdaOutgoingDerivative, incomingDatumCoeff]
    ring

/-- The weighted radial datum has source λ²F in incoming transport.
Paper `e1a0fd5`, `eq:radial-datum-transport`, lines 564–570 and 594–603. -/
theorem weightedRadialDatum_ae_transport {u v : ℝ}
    (hu : ui ≤ u) (hu0 : u < 0) (huv : u < v) (hv : v < 0) :
    ∀ᵐ s, s ∈ Ioo ui u → HasDerivAt (fun t => weightedRadialDatum ui S t v)
      (S.lam s v ^ 2 * radialDatumSource S s v) s := by
  have hp := h.normalized_datum_ae_transport hu le_rfl hu0 huv hv.le
  have hl := h.lambdaOutgoingDerivative_ae_transport hu hu0 huv hv
  have hi : IntervalIntegrable (fun s => correctionIntegrandDerivative ui S s v) volume ui u :=
    (h.correctionIntegrandDerivative_continuous_in hu hu0 huv hv).intervalIntegrable_of_Icc hu
  filter_upwards [hp, hl, hi.ae_hasDerivAt_integral] with s hps hls his
  intro hs
  have hdc := his (by simpa only [uIcc_of_le hu] using Ioo_subset_Icc_self hs)
    ui left_mem_uIcc
  have hr0 := h.r_pos ⟨hs.1.le, hs.2.trans hu0, (hs.2.trans huv).le, hv.le⟩ (hs.2.trans huv)
  have hl0 := h.lam_pos (p := (s, v))
    ⟨hs.1.le, hs.2.trans hu0, (hs.2.trans huv).le, hv.le⟩
  convert ((hasDerivAt_const s (deriv (S.dvpsi ui) v)).add hdc).sub
    ((hps hs).mul (hls hs)) using 1
  · funext t
    simp only [weightedRadialDatum, datumCorrectionOutgoingDerivative,
      Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
  · dsimp only [correctionIntegrandDerivative, incomingDatumCoeff,
      outgoingDatumCoeffDerivative, radialDatumSource, SSFields.varkappa,
      varkappaOf, SSFields.dvphi, SSFields.theta]
    field_simp [hr0.ne', hl0.ne']
    ring

/-- Integral form of the differentiated weighted transport, with no q
transport premise. Paper `e1a0fd5`, lines 570, 572–574 and 603. -/
theorem weightedRadialDatum_transport_primitive {u v : ℝ}
    (hu : ui ≤ u) (hu0 : u < 0) (huv : u < v) (hv : v < 0) :
    IntervalPrimitive (fun s => weightedRadialDatum ui S s v)
      (fun s => S.lam s v ^ 2 * radialDatumSource S s v) ui u :=
  ac_integral_eq_sub hu (h.weightedRadialDatum_ac_in hu hu0 huv hv)
    (h.weightedRadialDatum_ae_transport hu hu0 huv hv)

end StandingFull

end AcExtensionPrinciple

end
