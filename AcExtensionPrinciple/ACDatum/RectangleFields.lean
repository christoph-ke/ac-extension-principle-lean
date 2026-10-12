module

public import AcExtensionPrinciple.ACDatum.IncomingPrimitives
public import AcExtensionPrinciple.ACDatum.RectangleIntegral

/-!
# Continuous fields on proper off-axis rectangles

Paper `e1a0fd5`, `equations.tex` lines 395–426 and 594–601.
The incoming representation gives joint continuity of ∂ᵥψ directly from
the initial datum and the continuous geometric and scalar coefficients.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory

/-- Incoming coefficient γϰ in normalized scalar transport. Paper `e1a0fd5`,
`eq:scalar-bound-linear-transport`, lines 416–418. -/
@[expose] noncomputable def incomingDatumCoeff (S : SSFields) (u v : ℝ) : ℝ :=
  S.gamma u v * S.varkappa u v

/-- Smooth correction to the rough initial datum in its incoming representation.
Paper `e1a0fd5`, `equations.tex` lines 422–424. -/
@[expose] noncomputable def datumCorrection (ui : ℝ) (S : SSFields) (u v : ℝ) : ℝ :=
  ∫ s in ui..u, S.lam s v * incomingDatumCoeff S s v * S.phi s v

/-- A proper incoming rectangle lies off the regular axis. Paper `e1a0fd5`,
`equations.tex` line 395. -/
theorem properRectangle_subset_triangle {ui U a b : ℝ}
    (hU : U < 0) (hUa : U < a) (hb : b ≤ 0) :
    Icc ui U ×ˢ Icc a b ⊆ pastTriangle ui := by
  intro p hp
  exact ⟨hp.1.1, hp.1.2.trans_lt hU, (hp.1.2.trans_lt (hUa.trans_le hp.2.1)).le,
    hp.2.2.trans hb⟩

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Joint continuity of the incoming normalized transport coefficient on each
proper rectangle. Paper `e1a0fd5`, lines 422–426, 594–601. -/
theorem incomingDatumCoeff_continuous_rectangle {U a b : ℝ}
    (hU : U < 0) (hUa : U < a) (hb : b ≤ 0) :
    ContinuousOn (fun p : ℝ × ℝ => incomingDatumCoeff S p.1 p.2) (Icc ui U ×ˢ Icc a b) := by
  have hs := properRectangle_subset_triangle (ui := ui) hU hUa hb
  have hr := h.regularCenter.continuous_r.mono hs
  have hm := h.regularCenter.continuous_m.mono hs
  have hn := h.regularCenter.continuous_nu.mono hs
  have hr0 : ∀ p ∈ Icc ui U ×ˢ Icc a b, S.r p.1 p.2 ≠ 0 := by
    intro p hp
    exact (h.r_pos (hs hp) (hp.1.2.trans_lt (hUa.trans_le hp.2.1))).ne'
  have hmu : ContinuousOn (fun p : ℝ × ℝ => S.mu p.1 p.2) (Icc ui U ×ˢ Icc a b) :=
    (continuousOn_const.mul hm).div hr hr0
  have hgap : ∀ p ∈ Icc ui U ×ˢ Icc a b, 1 - S.mu p.1 p.2 ≠ 0 :=
    fun p hp => (sub_pos.mpr (h.mu_bounds (hs hp)).2).ne'
  exact (hn.div (continuousOn_const.sub hmu) hgap).mul (hmu.div hr hr0)

/-- Joint continuity of the incoming correction, including its initial edge
and the terminal incoming label. Paper `e1a0fd5`, lines 422–426. -/
theorem datumCorrection_continuous_rectangle {U a b : ℝ}
    (hui : ui ≤ U) (hab : a ≤ b) (hU : U < 0) (hUa : U < a) (hb : b ≤ 0) :
    ContinuousOn (fun p : ℝ × ℝ => datumCorrection ui S p.1 p.2) (Icc ui U ×ˢ Icc a b) := by
  have hs := properRectangle_subset_triangle (ui := ui) hU hUa hb
  exact rectangle_integral_continuous
    (F := fun s v => S.lam s v * incomingDatumCoeff S s v * S.phi s v) hui hab
    (((h.regularCenter.continuous_lam.mono hs).mul
      (h.incomingDatumCoeff_continuous_rectangle hU hUa hb)).mul
        (h.regularCenter.continuous_phi.mono hs))

/-- The unnormalized datum equals the rough initial datum plus a continuous
incoming correction. Paper `e1a0fd5`, lines 422–424. -/
theorem dvpsi_eq_initial_add_correction {u v : ℝ} (hu : ui ≤ u)
    (hu0 : u < 0) (huv : u < v) (hv0 : v ≤ 0) :
    S.dvpsi u v = S.dvpsi ui v + datumCorrection ui S u v := by
  have he := (h.regularCenter.localBV.dvpsi_in v ui u hu
    (inSeg_subset_offAxis le_rfl hu0 huv hv0)).2
  dsimp only at he
  simp only [S.radiusCoeff_eq_lam_gamma] at he
  dsimp [datumCorrection, incomingDatumCoeff]
  simp only [mul_assoc] at he ⊢
  linarith

/-- Joint continuity of ∂ᵥψ on each proper rectangle follows from the initial
AC datum and its incoming representation. Paper `e1a0fd5`, lines 422–426. -/
theorem dvpsi_continuous_rectangle {U a b : ℝ}
    (hui : ui ≤ U) (hab : a ≤ b) (hU : U < 0) (hUa : U < a) (hb : b ≤ 0) :
    ContinuousOn (fun p : ℝ × ℝ => S.dvpsi p.1 p.2) (Icc ui U ×ˢ Icc a b) := by
  have hf : ContinuousOn (fun p : ℝ × ℝ => S.dvpsi ui p.2) (Icc ui U ×ˢ Icc a b) := by
    apply h.initial_ac_data.continuousOn.comp continuous_snd.continuousOn
    intro p hp
    rw [uIcc_of_le h.initial_negative.le]
    exact ⟨(hui.trans_lt hUa).le.trans hp.2.1, hp.2.2.trans hb⟩
  apply (hf.add (h.datumCorrection_continuous_rectangle hui hab hU hUa hb)).congr
  intro p hp
  exact h.dvpsi_eq_initial_add_correction hp.1.1 (hp.1.2.trans_lt hU)
    (hp.1.2.trans_lt (hUa.trans_le hp.2.1)) (hp.2.2.trans hb)

end StandingFull

end AcExtensionPrinciple

end
