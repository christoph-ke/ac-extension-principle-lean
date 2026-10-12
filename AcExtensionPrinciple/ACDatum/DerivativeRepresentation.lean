module

public import AcExtensionPrinciple.ACDatum.Propagation

/-!
# Explicit representation of the radial derivative

Paper `e1a0fd5`, `eq:radial-datum-derivative` and
`eq:rough-derivative-decomposition`, lines 557–574, 594–603.
Differentiation occurs only at labels where the initial AC datum is
differentiable. The remaining terms have ordinary continuous derivatives.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- Explicit numerator λ²q, separating the initial derivative from the smooth
incoming correction. Paper `e1a0fd5`, lines 572 and 594–603. -/
@[expose] noncomputable def weightedRadialDatum
    (ui : ℝ) (S : SSFields) (u v : ℝ) : ℝ :=
  deriv (S.dvpsi ui) v + datumCorrectionOutgoingDerivative ui S u v -
    (S.dvpsi u v / S.lam u v) * lambdaOutgoingDerivative ui S u v

/-- The weighted derivative's initial value is the rough initial derivative.
Paper `e1a0fd5`, `eq:rough-derivative-decomposition`, lines 572–574. -/
theorem weightedRadialDatum_initial (ui : ℝ) (S : SSFields) (v : ℝ) :
    weightedRadialDatum ui S ui v = deriv (S.dvpsi ui) v := by
  simp [weightedRadialDatum, datumCorrectionOutgoingDerivative, lambdaOutgoingDerivative]

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The explicit representation agrees with q at every proper point of a
label where the initial datum is differentiable. Paper `e1a0fd5`,
`eq:radial-datum-derivative` and lines 572, 594–603. -/
theorem radialDatumDerivative_eq_weighted {u v : ℝ} (hu : ui ≤ u) (hu0 : u < 0)
    (huv : u < v) (hv : v < 0)
    (hinit : HasDerivAt (S.dvpsi ui) (deriv (S.dvpsi ui) v) v) :
    radialDatumDerivative S u v = weightedRadialDatum ui S u v / S.lam u v ^ 2 := by
  have hc := h.datumCorrection_hasDerivAt_out hu hu0 huv hv
  have hl := h.lam_hasDerivAt_out hu hu0 huv hv
  have he : (fun x => S.dvpsi ui x + datumCorrection ui S u x) =ᶠ[𝓝 v] S.dvpsi u := by
    filter_upwards [Ioo_mem_nhds huv hv] with x hx
    exact (h.dvpsi_eq_initial_add_correction hu hu0 hx.1 hx.2.le).symm
  have hd := (hinit.add hc).congr_of_eventuallyEq he.symm
  have hl0 := h.lam_pos (p := (u, v)) ⟨hu, hu0, huv.le, hv.le⟩
  have hq := hd.fun_div hl hl0.ne'
  rw [radialDatumDerivative, hq.deriv]
  dsimp only [weightedRadialDatum]
  field_simp [hl0.ne']

/-- Incoming continuity of the outgoing transport-coefficient derivative.
Paper `e1a0fd5`, lines 596–601. -/
theorem outgoingDatumCoeffDerivative_continuous_in {u v : ℝ}
    (hu : ui ≤ u) (hu0 : u < 0) (huv : u < v) (hv : v < 0) :
    ContinuousOn (fun s => outgoingDatumCoeffDerivative S s v) (Icc ui u) := by
  obtain ⟨a, b, hua, hav, hvb, hb⟩ := exists_proper_outgoing_neighborhood huv hv
  exact (h.outgoingDatumCoeffDerivative_continuous_rectangle hu
    (hav.le.trans hvb.le) hu0 hua hb.le).comp
      (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => ⟨hs, ⟨hav.le, hvb.le⟩⟩)

/-- Incoming continuity of the differentiated scalar integrand.
Paper `e1a0fd5`, lines 594–601. -/
theorem correctionIntegrandDerivative_continuous_in {u v : ℝ}
    (hu : ui ≤ u) (hu0 : u < 0) (huv : u < v) (hv : v < 0) :
    ContinuousOn (fun s => correctionIntegrandDerivative ui S s v) (Icc ui u) := by
  obtain ⟨a, b, hua, hav, hvb, hb⟩ := exists_proper_outgoing_neighborhood huv hv
  exact (h.correctionIntegrandDerivative_continuous_rectangle hu
    (hav.le.trans hvb.le) hu0 hua hb.le).comp
      (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => ⟨hs, ⟨hav.le, hvb.le⟩⟩)

/-- Incoming AC of the outgoing λ derivative, without mixed-derivative
assumptions. Paper `e1a0fd5`, lines 594–601. -/
theorem lambdaOutgoingDerivative_ac_in {u v : ℝ} (hu : ui ≤ u) (hu0 : u < 0)
    (huv : u < v) (hv : v < 0) :
    AbsolutelyContinuousOnInterval (fun s => lambdaOutgoingDerivative ui S s v) ui u := by
  have hi : IntervalIntegrable (fun s => outgoingDatumCoeffDerivative S s v) volume ui u :=
    (h.outgoingDatumCoeffDerivative_continuous_in hu hu0 huv hv).intervalIntegrable_of_Icc hu
  exact (h.lam_ac_in hu le_rfl hu0 huv hv.le).fun_mul
    (hi.absolutelyContinuousOnInterval_intervalIntegral (c := ui) left_mem_uIcc)

/-- Incoming AC of the differentiated scalar correction.
Paper `e1a0fd5`, lines 594–601. -/
theorem datumCorrectionOutgoingDerivative_ac_in {u v : ℝ}
    (hu : ui ≤ u) (hu0 : u < 0) (huv : u < v) (hv : v < 0) :
    AbsolutelyContinuousOnInterval (fun s => datumCorrectionOutgoingDerivative ui S s v) ui u := by
  have hi : IntervalIntegrable (fun s => correctionIntegrandDerivative ui S s v) volume ui u :=
    (h.correctionIntegrandDerivative_continuous_in hu hu0 huv hv).intervalIntegrable_of_Icc hu
  exact hi.absolutelyContinuousOnInterval_intervalIntegral (c := ui) left_mem_uIcc

/-- The explicit weighted datum is AC on every proper incoming segment.
Paper `e1a0fd5`, `eq:radial-datum-transport`, lines 564–570. -/
theorem weightedRadialDatum_ac_in {u v : ℝ} (hu : ui ≤ u) (hu0 : u < 0)
    (huv : u < v) (hv : v < 0) :
    AbsolutelyContinuousOnInterval (fun s => weightedRadialDatum ui S s v) ui u :=
  (((LipschitzWith.const (deriv (S.dvpsi ui) v)).lipschitzOnWith.absolutelyContinuousOnInterval).add
    (h.datumCorrectionOutgoingDerivative_ac_in hu hu0 huv hv)).sub
      ((h.normalized_datum_ac_in hu le_rfl hu0 huv hv.le).fun_mul
        (h.lambdaOutgoingDerivative_ac_in hu hu0 huv hv))

end StandingFull

end AcExtensionPrinciple

end
