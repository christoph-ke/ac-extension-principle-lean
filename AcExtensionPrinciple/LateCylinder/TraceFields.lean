module

public import AcExtensionPrinciple.LateCylinder.CurveCalculus

/-!
# Smooth coefficients of the separated cylinder datum

Paper `e1a0fd5`, `eq:separated-datum-derivative`, lines 731–737,
and `eq:cylinder-datum-derivative`, lines 819–822.
Only the initial one-dimensional datum is rough. The expansion and incoming
correction have continuous partial derivatives on the open off-axis domain.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- Rectangle continuity gives ordinary continuity at every interior point.
Paper `e1a0fd5`, local calculus at lines 731–737. -/
theorem late_continuousOn_of_rectangles {ui : ℝ} {F : ℝ → ℝ → ℝ}
    (hc : ∀ U a b, ui ≤ U → a ≤ b → U < 0 → U < a → b ≤ 0 →
      ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (Icc ui U ×ˢ Icc a b)) :
    ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (late_cylinderInterior ui) := by
  intro p hp
  obtain ⟨a, b, hua, hav, hvb, hb⟩ := exists_proper_outgoing_neighborhood hp.2.1 hp.2.2
  let U := (p.1 + a) / 2
  have huU : p.1 < U := by dsimp [U]; linarith
  have hUa : U < a := by dsimp [U]; linarith
  have hU0 : U < 0 := hUa.trans (hav.trans hp.2.2)
  have hn : Icc ui U ×ˢ Icc a b ∈ 𝓝 p :=
    prod_mem_nhds (Icc_mem_nhds hp.1 huU) (Icc_mem_nhds hav hvb)
  have hpcont := (hc U a b (hp.1.trans huU).le
    (hav.trans hvb).le hU0 hUa hb.le).continuousAt hn
  exact hpcont.continuousWithinAt

/-- Continuous partial derivatives give the total derivative used along
cylinders. Paper `e1a0fd5`, chain rule at lines 731–737 and 819–822. -/
theorem late_total_derivative_of_partials {ui : ℝ} {F Fu Fv : ℝ → ℝ → ℝ}
    (hu : ∀ p ∈ late_cylinderInterior ui, HasDerivAt (fun s => F s p.2) (Fu p.1 p.2) p.1)
    (hv : ∀ p ∈ late_cylinderInterior ui, HasDerivAt (F p.1) (Fv p.1 p.2) p.2)
    (hcu : ContinuousOn (fun p : ℝ × ℝ => Fu p.1 p.2) (late_cylinderInterior ui))
    (hcv : ContinuousOn (fun p : ℝ × ℝ => Fv p.1 p.2) (late_cylinderInterior ui))
    {p : ℝ × ℝ} (hp : p ∈ late_cylinderInterior ui) :
    HasStrictFDerivAt (fun p : ℝ × ℝ => F p.1 p.2)
      ((late_cylinderLinear (Fu p.1 p.2)).coprod (late_cylinderLinear (Fv p.1 p.2))) p := by
  have hn := (isOpen_late_cylinderInterior ui).mem_nhds hp
  apply hasStrictFDerivAt_uncurry_coprod
    (f₁ := fun u v => late_cylinderLinear (Fu u v))
    (f₂ := fun u v => late_cylinderLinear (Fv u v))
  · filter_upwards [hn] with q hq
    exact (hu q hq).hasFDerivAt
  · filter_upwards [hn] with q hq
    exact (hv q hq).hasFDerivAt
  · exact ContinuousLinearMap.toSpanSingletonCLE.continuous.continuousAt.comp
      (hcu.continuousAt hn)
  · exact ContinuousLinearMap.toSpanSingletonCLE.continuous.continuousAt.comp
      (hcv.continuousAt hn)

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Continuity of the incoming wave coefficient away from the axis.
Paper `e1a0fd5`, lines 731–737 and 819–822. -/
theorem late_radiusCoeff_continuous :
    ContinuousOn (fun p : ℝ × ℝ => S.radiusCoeff p.1 p.2) (late_cylinderInterior ui) := by
  have hc : ContinuousOn (fun p : ℝ × ℝ => incomingDatumCoeff S p.1 p.2)
      (late_cylinderInterior ui) := late_continuousOn_of_rectangles
    (fun U _a _b _hui _hab hU hUa hb => h.incomingDatumCoeff_continuous_rectangle hU hUa hb)
  apply ((h.regularCenter.continuous_lam.mono (late_cylinderInterior_subset ui)).mul hc).congr
  intro p hp
  dsimp only
  rw [S.radiusCoeff_eq_lam_gamma]
  dsimp only [Pi.mul_apply, incomingDatumCoeff]
  ring

/-- Incoming partial derivative of λ from its characteristic primitive.
Paper `e1a0fd5`, lines 731–737 and `eq:radius`. -/
theorem late_lam_hasDerivAt_in {u v : ℝ} (hp : (u, v) ∈ late_cylinderInterior ui) :
    HasDerivAt (fun s => S.lam s v) (S.radiusCoeff u v) u := by
  let d := (u + v) / 2
  have hud : u < d := by dsimp [d]; linarith [hp.2.1]
  have hdv : d < v := by dsimp [d]; linarith [hp.2.1]
  have hs := properRectangle_subset_triangle (ui := ui) (hdv.trans hp.2.2) hdv hp.2.2.le
  have hc := ((h.regularCenter.continuous_lam.mono hs).mul
    (h.incomingDatumCoeff_continuous_rectangle (hdv.trans hp.2.2) hdv hp.2.2.le)).comp
    (continuous_id.prodMk continuous_const).continuousOn
    (fun s hss => ⟨hss, ⟨le_rfl, le_rfl⟩⟩)
  have hcc : ContinuousOn (fun s => S.radiusCoeff s v) (Icc ui d) := hc.congr
    (fun s _hs => by
      dsimp only [Function.comp_apply, Pi.mul_apply, id_eq, incomingDatumCoeff]
      rw [S.radiusCoeff_eq_lam_gamma]
      ring)
  apply intervalPrimitive_hasDerivAt ⟨hp.1, hud⟩ hcc
  intro s hss
  exact h.regularCenter.localBV.lam_in v ui s hss.1
    (inSeg_subset_offAxis le_rfl (hss.2.trans_lt (hdv.trans hp.2.2))
      (hss.2.trans_lt hdv) hp.2.2.le)

/-- Incoming partial derivative of the smooth correction.
Paper `e1a0fd5`, lines 422–424 and 731–737. -/
theorem late_correction_hasDerivAt_in {u v : ℝ} (hp : (u, v) ∈ late_cylinderInterior ui) :
    HasDerivAt (fun s => datumCorrection ui S s v) (S.radiusCoeff u v * S.phi u v) u := by
  let d := (u + v) / 2
  have hud : u < d := by dsimp [d]; linarith [hp.2.1]
  have hdv : d < v := by dsimp [d]; linarith [hp.2.1]
  have hs := properRectangle_subset_triangle (ui := ui) (hdv.trans hp.2.2) hdv hp.2.2.le
  have hc := (((h.regularCenter.continuous_lam.mono hs).mul
    (h.incomingDatumCoeff_continuous_rectangle (hdv.trans hp.2.2) hdv hp.2.2.le)).mul
      (h.regularCenter.continuous_phi.mono hs)).comp
    (continuous_id.prodMk continuous_const).continuousOn
    (fun s hss => ⟨hss, ⟨le_rfl, le_rfl⟩⟩)
  have hi := (hc.mono (Icc_subset_Icc le_rfl hud.le)).intervalIntegrable_of_Icc
    (μ := volume) hp.1.le
  have hd := intervalIntegral.integral_hasDerivAt_right hi
    ⟨Icc ui d, Icc_mem_nhds hp.1 hud, hc.aestronglyMeasurable measurableSet_Icc⟩
    (hc.continuousAt (Icc_mem_nhds hp.1 hud))
  convert hd using 1
  · rfl
  · dsimp only [Function.comp_apply, Pi.mul_apply, id_eq, incomingDatumCoeff]
    rw [S.radiusCoeff_eq_lam_gamma]
    ring

/-- λ has continuous total derivatives on the interior off-axis domain.
Paper `e1a0fd5`, lines 731–737. -/
theorem late_lam_hasStrictFDerivAt {p : ℝ × ℝ} (hp : p ∈ late_cylinderInterior ui) :
    HasStrictFDerivAt (fun p : ℝ × ℝ => S.lam p.1 p.2)
      ((late_cylinderLinear (S.radiusCoeff p.1 p.2)).coprod
        (late_cylinderLinear (lambdaOutgoingDerivative ui S p.1 p.2))) p := by
  apply late_total_derivative_of_partials
    (fun _q hq => h.late_lam_hasDerivAt_in hq)
    (fun _q hq => h.lam_hasDerivAt_out hq.1.le (hq.2.1.trans hq.2.2) hq.2.1 hq.2.2)
    h.late_radiusCoeff_continuous
    (late_continuousOn_of_rectangles (fun _U _a _b hui hab hU hUa hb =>
      h.lambdaOutgoingDerivative_continuous_rectangle hui hab hU hUa hb)) hp

/-- The smooth correction has continuous total derivatives.
Paper `e1a0fd5`, lines 731–737. -/
theorem late_correction_hasStrictFDerivAt {p : ℝ × ℝ} (hp : p ∈ late_cylinderInterior ui) :
    HasStrictFDerivAt (fun p : ℝ × ℝ => datumCorrection ui S p.1 p.2)
      ((late_cylinderLinear (S.radiusCoeff p.1 p.2 * S.phi p.1 p.2)).coprod
        (late_cylinderLinear (datumCorrectionOutgoingDerivative ui S p.1 p.2))) p := by
  apply late_total_derivative_of_partials
    (F := datumCorrection ui S)
    (Fu := fun u v => S.radiusCoeff u v * S.phi u v)
    (Fv := datumCorrectionOutgoingDerivative ui S)
    (fun _q hq => h.late_correction_hasDerivAt_in hq)
    (fun _q hq => h.datumCorrection_hasDerivAt_out
      hq.1.le (hq.2.1.trans hq.2.2) hq.2.1 hq.2.2)
    (h.late_radiusCoeff_continuous.mul
      (h.regularCenter.continuous_phi.mono (late_cylinderInterior_subset ui)))
    (late_continuousOn_of_rectangles (fun _U _a _b hui hab hU hUa hb =>
      h.datumCorrectionOutgoingDerivative_continuous_rectangle hui hab hU hUa hb)) hp

/-- Identify the smooth outgoing remainder at every interior incoming label,
without exceptional sets for the initial datum. Paper `e1a0fd5`,
`eq:rough-derivative-decomposition`, lines 572–574 and 731–737. -/
theorem late_smooth_remainder_identity {u v : ℝ} (hu : ui ≤ u) (hu0 : u < 0)
    (huv : u < v) (hv : v < 0) :
    datumCorrectionOutgoingDerivative ui S u v -
      (S.dvpsi u v / S.lam u v) * lambdaOutgoingDerivative ui S u v =
        S.lam u v ^ 2 * radialDatumRemainderIntegral ui S u v := by
  have he := (h.weightedRadialDatum_transport_primitive hu hu0 huv hv).2
  dsimp only at he
  rw [weightedRadialDatum_initial] at he
  dsimp only [weightedRadialDatum] at he
  have hl := h.lam_pos (p := (u, v)) ⟨hu, hu0, huv.le, hv.le⟩
  dsimp [radialDatumRemainderIntegral]
  rw [mul_div_cancel₀ _ (pow_ne_zero 2 hl.ne')]
  linarith

end StandingFull

end AcExtensionPrinciple

end
