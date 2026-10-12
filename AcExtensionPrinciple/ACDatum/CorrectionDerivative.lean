module

public import AcExtensionPrinciple.ACDatum.LambdaDerivative

/-!
# Differentiation of the incoming scalar correction

Paper `e1a0fd5`, `equations.tex` lines 422–426 and 594–601.
All three differentiated factors have continuous derivatives on proper
off-axis rectangles; the initial rough datum is kept separate.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory

/-- Outgoing derivative of the integrand in the incoming scalar correction.
Paper `e1a0fd5`, lines 422–424 and 594–601. -/
@[expose] noncomputable def correctionIntegrandDerivative
    (ui : ℝ) (S : SSFields) (u v : ℝ) : ℝ :=
  lambdaOutgoingDerivative ui S u v * incomingDatumCoeff S u v * S.phi u v +
    S.lam u v * outgoingDatumCoeffDerivative S u v * S.phi u v +
    S.lam u v * incomingDatumCoeff S u v * S.dvphi u v

/-- Outgoing derivative of the incoming correction. Paper `e1a0fd5`,
lines 422–424 and 594–601. -/
@[expose] noncomputable def datumCorrectionOutgoingDerivative
    (ui : ℝ) (S : SSFields) (u v : ℝ) : ℝ :=
  ∫ s in ui..u, correctionIntegrandDerivative ui S s v

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Continuity of the differentiated incoming integrand on proper rectangles.
Paper `e1a0fd5`, lines 594–601. -/
theorem correctionIntegrandDerivative_continuous_rectangle {U a b : ℝ}
    (hui : ui ≤ U) (hab : a ≤ b) (hU : U < 0) (hUa : U < a) (hb : b ≤ 0) :
    ContinuousOn (fun p : ℝ × ℝ => correctionIntegrandDerivative ui S p.1 p.2)
      (Icc ui U ×ˢ Icc a b) := by
  have hs := properRectangle_subset_triangle (ui := ui) hU hUa hb
  have hl := h.regularCenter.continuous_lam.mono hs
  have hf := h.regularCenter.continuous_phi.mono hs
  have hld := h.lambdaOutgoingDerivative_continuous_rectangle hui hab hU hUa hb
  have hc := h.incomingDatumCoeff_continuous_rectangle hU hUa hb
  have hcd := h.outgoingDatumCoeffDerivative_continuous_rectangle hui hab hU hUa hb
  have hfd := h.dvphi_continuous_rectangle hui hab hU hUa hb
  exact (((hld.mul hc).mul hf).add ((hl.mul hcd).mul hf)).add ((hl.mul hc).mul hfd)

/-- Continuity of the outgoing derivative of the incoming correction.
Paper `e1a0fd5`, lines 594–601. -/
theorem datumCorrectionOutgoingDerivative_continuous_rectangle {U a b : ℝ}
    (hui : ui ≤ U) (hab : a ≤ b) (hU : U < 0) (hUa : U < a) (hb : b ≤ 0) :
    ContinuousOn (fun p : ℝ × ℝ => datumCorrectionOutgoingDerivative ui S p.1 p.2)
      (Icc ui U ×ˢ Icc a b) :=
  rectangle_integral_continuous hui hab
    (h.correctionIntegrandDerivative_continuous_rectangle hui hab hU hUa hb)

/-- The incoming scalar correction has its outgoing derivative at every
interior off-axis point. Paper `e1a0fd5`, lines 594–601. -/
theorem datumCorrection_hasDerivAt_out {u v : ℝ} (hu : ui ≤ u) (hu0 : u < 0)
    (huv : u < v) (hv : v < 0) :
    HasDerivAt (datumCorrection ui S u) (datumCorrectionOutgoingDerivative ui S u v) v := by
  obtain ⟨a, b, hua, hav, hvb, hb⟩ := exists_proper_outgoing_neighborhood huv hv
  have hs := properRectangle_subset_triangle (ui := ui) hu0 hua hb.le
  have hf : ContinuousOn
      (fun p : ℝ × ℝ => S.lam p.1 p.2 * incomingDatumCoeff S p.1 p.2 * S.phi p.1 p.2)
      (Icc ui u ×ˢ Icc a b) := ((h.regularCenter.continuous_lam.mono hs).mul
    (h.incomingDatumCoeff_continuous_rectangle hu0 hua hb.le)).mul
      (h.regularCenter.continuous_phi.mono hs)
  apply rectangle_integral_hasDerivAt ⟨hu, le_rfl⟩ ⟨hav, hvb⟩ hf
    (h.correctionIntegrandDerivative_continuous_rectangle hu (hav.le.trans hvb.le) hu0 hua hb.le)
  intro s hss x hx
  have hs0 := hss.2.trans_lt hu0
  have hsx := hss.2.trans_lt (hua.trans hx.1)
  have hx0 := hx.2.trans hb
  convert ((h.lam_hasDerivAt_out hss.1 hs0 hsx hx0).mul
    (h.incomingDatumCoeff_hasDerivAt_out hss.1 hs0 hsx hx0)).mul
    (h.phi_hasDerivAt_out hss.1 hs0 hsx hx0) using 1
  dsimp only [correctionIntegrandDerivative]
  simp only [Pi.mul_apply]
  ring

/-- The smooth incoming correction is AC on every proper closed outgoing
interval away from both endpoints. Paper `e1a0fd5`, lines 594–601. -/
theorem datumCorrection_ac_out {u a b : ℝ} (hu : ui ≤ u) (hu0 : u < 0)
    (hua : u < a) (hab : a ≤ b) (hb : b < 0) :
    AbsolutelyContinuousOnInterval (datumCorrection ui S u) a b := by
  have hg : ContinuousOn (datumCorrectionOutgoingDerivative ui S u) (Icc a b) :=
    (h.datumCorrectionOutgoingDerivative_continuous_rectangle hu hab hu0 hua hb.le).comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun x hx => ⟨⟨hu, le_rfl⟩, hx⟩)
  exact ac_of_continuous_hasDerivAt hab hg
    (fun x hx => h.datumCorrection_hasDerivAt_out hu hu0 (hua.trans_le hx.1) (hx.2.trans_lt hb))

/-- Outgoing AC of the normalized datum on every proper interior interval.
Paper `e1a0fd5`, `lem:ac-datum-propagation`, line 601. -/
theorem normalized_datum_ac_out_interior {u a b : ℝ} (hu : ui ≤ u) (hu0 : u < 0)
    (hua : u < a) (hab : a ≤ b) (hb : b < 0) :
    AbsolutelyContinuousOnInterval (fun v => S.dvpsi u v / S.lam u v) a b := by
  have hi := h.initial_ac_data.mono (show uIcc a b ⊆ uIcc ui 0 by
    rw [uIcc_of_le hab, uIcc_of_le h.initial_negative.le]
    exact Icc_subset_Icc (hu.trans hua.le) hb.le)
  have hc := h.datumCorrection_ac_out hu hu0 hua hab hb
  have hlam := h.regularCenter.ac_lam_out u a b hab
    (outSeg_subset_triangle hu hu0 hua.le hb.le)
  have hinv := positive_ac_inv hlam (fun v hv => by
    rw [uIcc_of_le hab] at hv
    exact h.lam_pos (p := (u, v)) ⟨hu, hu0, (hua.trans_le hv.1).le, hv.2.trans hb.le⟩)
  apply ((hi.add hc).fun_mul hinv).congr
  intro v hv
  rw [uIcc_of_le hab] at hv
  change (S.dvpsi ui v + datumCorrection ui S u v) * (S.lam u v)⁻¹ =
    S.dvpsi u v / S.lam u v
  rw [h.dvpsi_eq_initial_add_correction hu hu0 (hua.trans_le hv.1) (hv.2.trans hb.le)]
  exact (div_eq_mul_inv _ _).symm

end StandingFull

end AcExtensionPrinciple

end
