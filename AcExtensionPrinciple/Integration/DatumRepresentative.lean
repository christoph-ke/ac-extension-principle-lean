module

public import AcExtensionPrinciple.ACDatum.UniformRemainder
public import AcExtensionPrinciple.Renormalized.ClassDatumInputs
public import AcExtensionPrinciple.ScalarBound.Uniform

/-!
# A transported representative for the radial derivative

Paper `e1a0fd5`, `lem:ac-datum-propagation`, lines 555–603.
The explicit incoming integral chooses values at the exceptional initial
labels, including the terminal label. It agrees with the radial derivative
almost everywhere on every outgoing cone and supplies the all-label interface
used in Section 3.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory

/-- Incoming integral representative of q, including exceptional labels.
Paper `e1a0fd5`, `eq:rough-derivative-decomposition`, lines 572–574 and 603. -/
@[expose] noncomputable def transportedRadialDatum
    (ui : ℝ) (S : SSFields) (u v : ℝ) : ℝ :=
  (deriv (S.dvpsi ui) v + ∫ s in ui..u, S.lam s v ^ 2 * radialDatumSource S s v) /
    S.lam u v ^ 2

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Lemma 2.2's uniform remainder bound with Lemma 2.1 discharged.
Paper `e1a0fd5`, `eq:derivative-remainder-bound`, lines 578–581. -/
theorem radialDatumRemainderIntegral_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ u v, ui ≤ u → u < 0 → u < v → v ≤ 0 →
      |radialDatumRemainderIntegral ui S u v| ≤
        C * (∫ s in ui..u, -S.nu s v / S.r s v ^ 2) ∧
      C * (∫ s in ui..u, -S.nu s v / S.r s v ^ 2) ≤ C / S.r u v := by
  obtain ⟨M, hM⟩ := h.uniform_scalar_bound
  exact h.radialDatumRemainderIntegral_bound_of_scalar hM

/-- The integral representative is AC on every proper incoming segment.
Paper `e1a0fd5`, `eq:radial-datum-transport`, lines 564–570 and 603. -/
theorem transportedRadialDatum_ac_in {v a b : ℝ} (hab : a ≤ b)
    (ha : ui ≤ a) (hb0 : b < 0) (hbv : b < v) (hv0 : v ≤ 0) :
    AbsolutelyContinuousOnInterval (fun u => transportedRadialDatum ui S u v) a b := by
  have hib : ui ≤ b := ha.trans hab
  have hl := h.lam_ac_in hib le_rfl hb0 hbv hv0
  have hi := positive_ac_inv hl (fun s hs => by
    rw [uIcc_of_le hib] at hs
    exact h.lam_pos (p := (s, v))
      ⟨hs.1, hs.2.trans_lt hb0, (hs.2.trans_lt hbv).le, hv0⟩)
  have hc := continuous_in h.regularCenter.continuous_lam
    (inSeg_subset_triangle le_rfl hb0 hbv.le hv0)
  have hF : ContinuousOn (fun s => S.lam s v ^ 2 * radialDatumSource S s v)
      (Icc ui b) := (hc.pow 2).mul
    (h.radialDatumSource_continuous_in hib le_rfl hb0 hbv hv0)
  have hI := (hF.intervalIntegrable_of_Icc hib).absolutelyContinuousOnInterval_intervalIntegral
    (c := ui) left_mem_uIcc
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => deriv (S.dvpsi ui) v) ui b :=
    (LipschitzWith.const (deriv (S.dvpsi ui) v)).lipschitzOnWith.absolutelyContinuousOnInterval
  have hAC := (hconst.add hI).fun_mul (hi.fun_mul hi)
  have hAC' : AbsolutelyContinuousOnInterval
      (fun u => transportedRadialDatum ui S u v) ui b := by
    simpa only [transportedRadialDatum, div_eq_mul_inv, pow_two, mul_inv_rev,
      Pi.add_apply] using hAC
  apply hAC'.mono
  rw [uIcc_of_le hab, uIcc_of_le hib]
  exact Icc_subset_Icc ha le_rfl

/-- Incoming transport of the integral representative at every label.
Paper `e1a0fd5`, `eq:radial-datum-transport`, lines 564–570 and 603. -/
theorem transportedRadialDatum_ae_transport {v a b : ℝ} (hab : a ≤ b)
    (ha : ui ≤ a) (hb0 : b < 0) (hbv : b < v) (hv0 : v ≤ 0) :
    ∀ᵐ s, s ∈ Ioo a b → HasDerivAt (fun u => transportedRadialDatum ui S u v)
      (-2 * S.gamma s v * S.varkappa s v * transportedRadialDatum ui S s v -
        (S.gamma s v / S.r s v ^ 2) * (S.r s v / S.lam s v * S.dvphi s v) *
          ((S.r s v / S.lam s v * S.dvphi s v) ^ 2 - 3 * S.mu s v)) s := by
  have hib : ui ≤ b := ha.trans hab
  have hc := continuous_in h.regularCenter.continuous_lam
    (inSeg_subset_triangle le_rfl hb0 hbv.le hv0)
  have hF : ContinuousOn (fun s => S.lam s v ^ 2 * radialDatumSource S s v)
      (Icc ui b) := (hc.pow 2).mul
    (h.radialDatumSource_continuous_in hib le_rfl hb0 hbv hv0)
  have hI := (hF.intervalIntegrable_of_Icc hib).ae_hasDerivAt_integral
  have hl := intervalPrimitive_ae_hasDerivAt hab
    (fun x hx => h.regularCenter.localBV.lam_in v a x hx.1
      (inSeg_subset_offAxis ha (hx.2.trans_lt hb0) (hx.2.trans_lt hbv) hv0))
  filter_upwards [hI, hl] with s hsI hsL
  intro hs
  have hs' : s ∈ uIcc ui b := by
    rw [uIcc_of_le hib]
    exact ⟨ha.trans hs.1.le, hs.2.le⟩
  have hd := hsI hs' ui left_mem_uIcc
  have hp : (s, v) ∈ pastTriangle ui :=
    ⟨ha.trans hs.1.le, hs.2.trans hb0, (hs.2.trans hbv).le, hv0⟩
  have hl0 := (h.lam_pos hp).ne'
  have hr0 := (h.r_pos hp (hs.2.trans hbv)).ne'
  convert ((hasDerivAt_const s (deriv (S.dvpsi ui) v)).add hd).div
    ((hsL hs).pow 2) (pow_ne_zero 2 hl0) using 1
  · rfl
  · rw [S.radiusCoeff_eq_lam_gamma]
    simp only [Pi.pow_apply, Pi.add_apply]
    dsimp only [transportedRadialDatum, radialDatumSource, SSFields.dvphi]
    field_simp [hl0, hr0]
    ring

/-- All proper incoming integral identities, including the terminal label.
Paper `e1a0fd5`, `eq:radial-datum-transport`, lines 564–570. -/
theorem transportedRadialDatum_incoming_primitive {v a b : ℝ} (hab : a ≤ b)
    (ha : ui ≤ a) (hb0 : b < 0) (hbv : b < v) (hv0 : v ≤ 0) :
    IntervalPrimitive (fun u => transportedRadialDatum ui S u v)
      (fun u => -2 * S.gamma u v * S.varkappa u v * transportedRadialDatum ui S u v -
        (S.gamma u v / S.r u v ^ 2) * (S.r u v / S.lam u v * S.dvphi u v) *
          ((S.r u v / S.lam u v * S.dvphi u v) ^ 2 - 3 * S.mu u v)) a b :=
  ac_integral_eq_sub hab (h.transportedRadialDatum_ac_in hab ha hb0 hbv hv0)
    (h.transportedRadialDatum_ae_transport hab ha hb0 hbv hv0)

/-- Every outgoing cone has the same radial derivative almost everywhere.
Paper `e1a0fd5`, `eq:radial-datum-derivative`, lines 557–558 and 572–574. -/
theorem transportedRadialDatum_radial_eq {u : ℝ} (hu : ui ≤ u) (hu0 : u < 0) :
    transportedRadialDatum ui S u =ᵐ[volume.restrict (Ioc u 0)]
      S.radialDatumDerivative u := by
  have he := h.radialDatumDerivative_ae_decomposition
  apply (ae_restrict_iff' measurableSet_Ioc).mpr
  filter_upwards [he, volume.ae_ne (0 : ℝ)] with v hv hv0
  intro hvI
  have hv' : v ∈ Ioo ui 0 := ⟨hu.trans_lt hvI.1, lt_of_le_of_ne hvI.2 hv0⟩
  have hd := hv hv' u hu hu0 hvI.1
  change transportedRadialDatum ui S u v = radialDatumDerivative S u v
  rw [hd]
  simp only [transportedRadialDatum, radialDatumRemainderIntegral, add_div]

/-- Bridge from Lemma 2.2 to the all-label Section 3 interface.
Paper `e1a0fd5`, `lem:ac-datum-propagation`, lines 555–603. -/
theorem sectionThreeDatumInputs :
    SectionThreeDatumInputs ui S (transportedRadialDatum ui S) where
  outgoing_ac := fun _ hu hu0 => h.normalized_datum_ac_out hu hu0
  radial_eq := fun _ hu hu0 => h.transportedRadialDatum_radial_eq hu hu0
  incoming_primitive := fun _ _ _ hab ha hb0 hbv hv0 =>
    h.transportedRadialDatum_incoming_primitive hab ha hb0 hbv hv0

end StandingFull

end AcExtensionPrinciple

end
