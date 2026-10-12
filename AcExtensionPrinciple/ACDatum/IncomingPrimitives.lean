module

public import AcExtensionPrinciple.ACDatum.InitialTail

/-!
# Incoming integral identities used in AC propagation

Paper commit `e1a0fd5`, `equations.tex`
lines 414–426 and 603. All results in this file follow from the standing
assumptions, without assuming the differentiated datum transport.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- The wave coefficient is λ γ ϰ. Paper `e1a0fd5`, `eq:radius` and
the incoming representation at lines 422–424. -/
theorem SSFields.radiusCoeff_eq_lam_gamma (S : SSFields) (u v : ℝ) :
    S.radiusCoeff u v = S.lam u v * S.gamma u v * S.varkappa u v := by
  rw [S.radiusCoeff_eq]
  simp only [SSFields.kappa, SSFields.gamma, SSFields.varkappa]
  rw [radius_coefficient_eq]
  ring

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The incoming representation suggested for proving outgoing AC, valid at
every off-axis point, including the terminal incoming ray. Paper `e1a0fd5`,
`equations.tex` lines 422–424. -/
theorem normalized_datum_incoming_representation {u v : ℝ}
    (hu : ui ≤ u) (hu0 : u < 0) (huv : u < v) (hv0 : v ≤ 0) :
    S.dvpsi u v / S.lam u v = (1 / S.lam u v) *
      (S.dvpsi ui v + ∫ s in ui..u,
        S.lam s v * S.gamma s v * S.varkappa s v * S.phi s v) := by
  have he := (h.regularCenter.localBV.dvpsi_in v ui u hu
    (inSeg_subset_offAxis le_rfl hu0 huv hv0)).2
  dsimp only at he
  simp only [S.radiusCoeff_eq_lam_gamma] at he
  have hd : S.dvpsi u v = S.dvpsi ui v +
      ∫ s in ui..u, S.lam s v * S.gamma s v * S.varkappa s v * S.phi s v := by
    linarith
  rw [hd]
  ring

/-- The unnormalized datum is AC along each off-axis incoming segment.
Paper `e1a0fd5`, lines 222 and 422–424. -/
theorem dvpsi_ac_in {v a b : ℝ} (hab : a ≤ b) (ha : ui ≤ a)
    (hb0 : b < 0) (hbv : b < v) (hv0 : v ≤ 0) :
    AbsolutelyContinuousOnInterval (fun s => S.dvpsi s v) a b := by
  apply intervalPrimitive_ac (g := fun s => S.radiusCoeff s v * S.phi s v) hab
  intro x hx
  exact h.regularCenter.localBV.dvpsi_in v a x hx.1
    (inSeg_subset_offAxis ha (hx.2.trans_lt hb0) (hx.2.trans_lt hbv) hv0)

/-- The normalized datum is AC along incoming segments, directly from the
integral class. Paper `e1a0fd5`, `eq:scalar-bound-linear-transport`, line 416. -/
theorem normalized_datum_ac_in {v a b : ℝ} (hab : a ≤ b) (ha : ui ≤ a)
    (hb0 : b < 0) (hbv : b < v) (hv0 : v ≤ 0) :
    AbsolutelyContinuousOnInterval (fun s => S.dvpsi s v / S.lam s v) a b := by
  have hi := h.dvpsi_ac_in hab ha hb0 hbv hv0
  have hl := h.lam_ac_in hab ha hb0 hbv hv0
  have hinv := positive_ac_inv hl (fun s hs => by
    rw [uIcc_of_le hab] at hs
    exact h.lam_pos (p := (s, v))
      ⟨ha.trans hs.1, hs.2.trans_lt hb0, (hs.2.trans_lt hbv).le, hv0⟩)
  simpa [div_eq_mul_inv] using hi.fun_mul hinv

/-- The normalized scalar transport holds a.e. on every off-axis incoming
segment. Paper `e1a0fd5`, `eq:scalar-bound-linear-transport`, lines 416–418. -/
theorem normalized_datum_ae_transport {v a b : ℝ} (hab : a ≤ b) (ha : ui ≤ a)
    (hb0 : b < 0) (hbv : b < v) (hv0 : v ≤ 0) :
    ∀ᵐ s, s ∈ Ioo a b → HasDerivAt (fun t => S.dvpsi t v / S.lam t v)
      (-(S.gamma s v * S.varkappa s v) *
        (S.dvpsi s v / S.lam s v - S.phi s v)) s := by
  have hd := intervalPrimitive_ae_hasDerivAt hab
    (fun x hx => h.regularCenter.localBV.dvpsi_in v a x hx.1
      (inSeg_subset_offAxis ha (hx.2.trans_lt hb0) (hx.2.trans_lt hbv) hv0))
  have hl := intervalPrimitive_ae_hasDerivAt hab
    (fun x hx => h.regularCenter.localBV.lam_in v a x hx.1
      (inSeg_subset_offAxis ha (hx.2.trans_lt hb0) (hx.2.trans_lt hbv) hv0))
  filter_upwards [hd, hl] with s hds hls
  intro hs
  have hp : (s, v) ∈ pastTriangle ui :=
    ⟨ha.trans hs.1.le, hs.2.trans hb0, (hs.2.trans hbv).le, hv0⟩
  convert (hds hs).div (hls hs) (h.lam_pos hp).ne' using 1
  rw [S.radiusCoeff_eq_lam_gamma]
  field_simp [(h.lam_pos hp).ne']
  ring

/-- Integral form of the first-order normalized scalar transport.
Paper `e1a0fd5`, `eq:scalar-bound-linear-transport`, lines 416–418 and 426. -/
theorem normalized_datum_transport_primitive {v a b : ℝ} (hab : a ≤ b) (ha : ui ≤ a)
    (hb0 : b < 0) (hbv : b < v) (hv0 : v ≤ 0) :
    IntervalPrimitive (fun s => S.dvpsi s v / S.lam s v)
      (fun s => -(S.gamma s v * S.varkappa s v) *
        (S.dvpsi s v / S.lam s v - S.phi s v)) a b :=
  ac_integral_eq_sub hab (h.normalized_datum_ac_in hab ha hb0 hbv hv0)
    (h.normalized_datum_ae_transport hab ha hb0 hbv hv0)

/-- Reciprocal radius primitive along incoming characteristics, obtained
without extra differentiability assumptions. Paper `e1a0fd5`,
`eq:derivative-remainder-bound`, proof line 603. -/
theorem reciprocal_radius_primitive {v a b : ℝ} (hab : a ≤ b) (ha : ui ≤ a)
    (hb0 : b < 0) (hbv : b < v) (hv0 : v ≤ 0) :
    IntervalPrimitive (fun s => 1 / S.r s v)
      (fun s => -S.nu s v / S.r s v ^ 2) a b := by
  have hr := intervalPrimitive_ac hab
    (fun x hx => h.regularCenter.localBV.radius_in v a x hx.1
      (inSeg_subset_triangle ha (hx.2.trans_lt hb0) (hx.2.trans_lt hbv).le hv0))
  have hinv := positive_ac_inv hr (fun s hs => by
    rw [uIcc_of_le hab] at hs
    exact h.r_pos ⟨ha.trans hs.1, hs.2.trans_lt hb0,
      (hs.2.trans_lt hbv).le, hv0⟩ (hs.2.trans_lt hbv))
  apply ac_integral_eq_sub hab (by simpa only [one_div] using hinv)
  have hd := intervalPrimitive_ae_hasDerivAt hab
    (fun x hx => h.regularCenter.localBV.radius_in v a x hx.1
      (inSeg_subset_triangle ha (hx.2.trans_lt hb0) (hx.2.trans_lt hbv).le hv0))
  filter_upwards [hd] with s hds
  intro hs
  have hp : (s, v) ∈ pastTriangle ui :=
    ⟨ha.trans hs.1.le, hs.2.trans hb0, (hs.2.trans hbv).le, hv0⟩
  convert (hds hs).inv (h.r_pos hp (hs.2.trans hbv)).ne' using 1
  funext t
  exact one_div _

/-- The incoming remainder majorant is exactly the difference of reciprocal
radii. Paper `e1a0fd5`, `eq:derivative-remainder-bound`, lines 578–581 and 603. -/
theorem incoming_reciprocal_integral {u v : ℝ} (hu : ui ≤ u) (hu0 : u < 0)
    (huv : u < v) (hv0 : v ≤ 0) :
    (∫ s in ui..u, -S.nu s v / S.r s v ^ 2) =
      1 / S.r u v - 1 / S.r ui v :=
  (h.reciprocal_radius_primitive hu le_rfl hu0 huv hv0).2.symm

/-- The reciprocal-radius integral is at most the final inverse radius.
Paper `e1a0fd5`, `eq:derivative-remainder-bound`, lines 578–581. -/
theorem incoming_reciprocal_integral_le {u v : ℝ} (hu : ui ≤ u) (hu0 : u < 0)
    (huv : u < v) (hv0 : v ≤ 0) :
    (∫ s in ui..u, -S.nu s v / S.r s v ^ 2) ≤ 1 / S.r u v := by
  rw [h.incoming_reciprocal_integral hu hu0 huv hv0]
  have hr := h.r_pos (u := ui) (v := v)
    ⟨le_rfl, h.initial_negative, (hu.trans_lt huv).le, hv0⟩ (hu.trans_lt huv)
  exact sub_le_self _ (one_div_nonneg.mpr hr.le)

end StandingFull

end AcExtensionPrinciple

end
