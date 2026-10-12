module

public import AcExtensionPrinciple.ACDatum.RectangleFields
public import AcExtensionPrinciple.Renormalized.OutgoingIdentities

/-!
# Outgoing coefficient calculus at local BV regularity

Paper `e1a0fd5`, `eq:transport-coefficient-derivative`, lines 594–601.
Continuous characteristic integrands upgrade the relevant primitives to
pointwise derivatives away from both coordinate endpoints.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- Outgoing derivative of γϰ. Paper `e1a0fd5`,
`eq:transport-coefficient-derivative`, lines 596–599. -/
@[expose] noncomputable def outgoingDatumCoeffDerivative (S : SSFields) (u v : ℝ) : ℝ :=
  S.lam u v * (S.gamma u v / S.r u v ^ 2) *
    ((S.theta u v / S.lam u v) ^ 2 - 2 * S.mu u v)

/-- There is a proper compact outgoing neighborhood of each interior off-axis
point. Paper `e1a0fd5`, line 594. -/
theorem exists_proper_outgoing_neighborhood {u v : ℝ} (huv : u < v) (hv : v < 0) :
    ∃ a b : ℝ, u < a ∧ a < v ∧ v < b ∧ b < 0 := by
  refine ⟨(u + v) / 2, v / 2, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- ∂ᵥψ is continuous on every proper off-axis outgoing segment.
Paper `e1a0fd5`, lines 422–426 and 594–601. -/
theorem dvpsi_continuous_out {u a b : ℝ} (hu : ui ≤ u) (hu0 : u < 0)
    (hua : u < a) (hab : a ≤ b) (hb : b ≤ 0) : ContinuousOn (S.dvpsi u) (Icc a b) :=
  (h.dvpsi_continuous_rectangle hu hab hu0 hua hb).comp
    (continuous_const.prodMk continuous_id).continuousOn
    (fun _v hv => ⟨⟨hu, le_rfl⟩, hv⟩)

/-- Pointwise outgoing radius derivative in the coordinate interior.
Paper `e1a0fd5`, line 222 and `eq:radius`. -/
theorem acdatum_radius_hasDerivAt_out {u v : ℝ} (hu : ui ≤ u) (hu0 : u < 0)
    (huv : u < v) (hv : v < 0) : HasDerivAt (S.r u) (S.lam u v) v := by
  obtain ⟨a, b, hua, hav, hvb, hb⟩ := exists_proper_outgoing_neighborhood huv hv
  apply intervalPrimitive_hasDerivAt ⟨hav, hvb⟩
    (continuous_out h.regularCenter.continuous_lam
      (outSeg_subset_triangle hu hu0 hua.le hb.le))
  intro x hx
  exact h.regularCenter.localBV.radius_out u a x hx.1
    (outSeg_subset_triangle hu hu0 hua.le (hx.2.trans hb.le))

/-- Pointwise outgoing derivative of ψ from its integral equation.
Paper `e1a0fd5`, line 222 and `eq:wave-psi`. -/
theorem psi_hasDerivAt_out {u v : ℝ} (hu : ui ≤ u) (hu0 : u < 0)
    (huv : u < v) (hv : v < 0) :
    HasDerivAt (fun x => S.r u x * S.phi u x) (S.dvpsi u v) v := by
  obtain ⟨a, b, hua, hav, hvb, hb⟩ := exists_proper_outgoing_neighborhood huv hv
  apply intervalPrimitive_hasDerivAt ⟨hav, hvb⟩
    (h.dvpsi_continuous_out hu hu0 hua (hav.le.trans hvb.le) hb.le)
  intro x hx
  exact h.regularCenter.localBV.psi_out u a x hx.1
    (outSeg_subset_triangle hu hu0 hua.le (hx.2.trans hb.le))

/-- The scalar derivative field agrees with the pointwise outgoing derivative
away from the axis. Paper `e1a0fd5`, lines 222 and 594–601. -/
theorem phi_hasDerivAt_out {u v : ℝ} (hu : ui ≤ u) (hu0 : u < 0)
    (huv : u < v) (hv : v < 0) : HasDerivAt (S.phi u) (S.dvphi u v) v := by
  have hr := h.acdatum_radius_hasDerivAt_out hu hu0 huv hv
  have hp := h.psi_hasDerivAt_out hu hu0 huv hv
  have hr0 := h.r_pos ⟨hu, hu0, huv.le, hv.le⟩ huv
  have hd := hp.div hr hr0.ne'
  have he : (fun x => (S.r u x * S.phi u x) / S.r u x) =ᶠ[𝓝 v] S.phi u := by
    filter_upwards [hr.continuousAt.eventually_ne hr0.ne'] with x hx
    exact mul_div_cancel_left₀ _ hx
  convert hd.congr_of_eventuallyEq he.symm using 1
  dsimp [SSFields.dvphi, SSFields.theta]
  field_simp [hr0.ne']

/-- Continuity of the outgoing mass integrand on each proper segment.
Paper `e1a0fd5`, `eq:mass`, lines 594–601. -/
theorem massV_continuous_out {u a b : ℝ} (hu : ui ≤ u) (hu0 : u < 0)
    (hua : u < a) (hab : a ≤ b) (hb : b ≤ 0) : ContinuousOn (S.massV u) (Icc a b) := by
  have hs := outSeg_subset_triangle hu hu0 hua.le hb
  have hr := continuous_out h.regularCenter.continuous_r hs
  have hm := continuous_out h.regularCenter.continuous_m hs
  have hl := continuous_out h.regularCenter.continuous_lam hs
  have hf := continuous_out h.regularCenter.continuous_phi hs
  have hd := h.dvpsi_continuous_out hu hu0 hua hab hb
  have hp : ∀ v ∈ Icc a b, (u, v) ∈ pastTriangle ui := fun v hv =>
    ⟨hu, hu0, (hua.trans_le hv.1).le, hv.2.trans hb⟩
  have hmu : ContinuousOn (S.mu u) (Icc a b) :=
    (continuousOn_const.mul hm).div hr (fun v hv => (h.r_pos (hp v hv) (hua.trans_le hv.1)).ne')
  have ht : ContinuousOn (S.theta u) (Icc a b) := hd.sub (hl.mul hf)
  exact ((continuousOn_const.sub hmu).mul (ht.pow 2)).div (continuousOn_const.mul hl)
    (fun v hv => mul_ne_zero (by norm_num) (h.lam_pos (hp v hv)).ne')

/-- Pointwise mass derivative from the continuous mass integrand.
Paper `e1a0fd5`, `eq:mass`, lines 594–601. -/
theorem mass_hasDerivAt_out {u v : ℝ} (hu : ui ≤ u) (hu0 : u < 0)
    (huv : u < v) (hv : v < 0) : HasDerivAt (S.m u) (S.massV u v) v := by
  obtain ⟨a, b, hua, hav, hvb, hb⟩ := exists_proper_outgoing_neighborhood huv hv
  apply intervalPrimitive_hasDerivAt ⟨hav, hvb⟩
    (h.massV_continuous_out hu hu0 hua (hav.le.trans hvb.le) hb.le)
  intro x hx
  exact h.regularCenter.localBV.mass_out u a x hx.1
    (outSeg_subset_triangle hu hu0 hua.le (hx.2.trans hb.le))

/-- The incoming expansion has its pointwise outgoing derivative off-axis.
Paper `e1a0fd5`, `eq:radius`, lines 594–601. -/
theorem nu_hasDerivAt_out {u v : ℝ} (hu : ui ≤ u) (hu0 : u < 0)
    (huv : u < v) (hv : v < 0) : HasDerivAt (S.nu u) (S.radiusCoeff u v) v := by
  obtain ⟨a, b, hua, hav, hvb, hb⟩ := exists_proper_outgoing_neighborhood huv hv
  have hc : ContinuousOn (S.radiusCoeff u) (Icc a b) := by
    have hh := ((h.regularCenter.continuous_lam.mono
      (properRectangle_subset_triangle (ui := ui) hu0 hua hb.le)).mul
      (h.incomingDatumCoeff_continuous_rectangle hu0 hua hb.le)).comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun x hx => ⟨⟨hu, le_rfl⟩, hx⟩)
    apply hh.congr
    intro x hx
    rw [S.radiusCoeff_eq_lam_gamma]
    simp only [incomingDatumCoeff, Function.comp_apply, Pi.mul_apply, id_eq]
    ring
  apply intervalPrimitive_hasDerivAt ⟨hav, hvb⟩ hc
  intro x hx
  exact h.regularCenter.localBV.nu_out u a x hx.1
    (outSeg_subset_offAxis hu hu0 hua (hx.2.trans hb.le))

/-- The transport coefficient has the outgoing derivative stated in the paper,
now derived from the integral solution class. Paper `e1a0fd5`,
`eq:transport-coefficient-derivative`, lines 596–599. -/
theorem incomingDatumCoeff_hasDerivAt_out {u v : ℝ} (hu : ui ≤ u) (hu0 : u < 0)
    (huv : u < v) (hv : v < 0) :
    HasDerivAt (incomingDatumCoeff S u) (outgoingDatumCoeffDerivative S u v) v := by
  have hp : (u, v) ∈ pastTriangle ui := ⟨hu, hu0, huv.le, hv.le⟩
  have hr0 := h.r_pos hp huv
  have hl0 := h.lam_pos hp
  have hmu := (h.mu_bounds hp).2
  have hnu := h.nu_hasDerivAt_out hu hu0 huv hv
  have hm := h.mass_hasDerivAt_out hu hu0 huv hv
  have hm' : HasDerivAt (S.m u)
      (S.r u v ^ 2 / (2 * kappaOf (S.lam u v) (S.mu u v)) * S.dvphi u v ^ 2) v := by
    convert hm using 1
    dsimp [SSFields.massV, SSFields.dvphi, kappaOf]
    field_simp [hr0.ne', hl0.ne', (sub_pos.mpr hmu).ne']
  have hn' : HasDerivAt (S.nu u)
      (kappaOf (S.lam u v) (S.mu u v) * varkappaOf (S.r u v) (S.mu u v) * S.nu u v) v := by
    simpa only [SSFields.kappa, SSFields.varkappa] using
      hnu.congr_deriv (S.radiusCoeff_eq u v)
  have hh := Renormalized.Outgoing.transport_coefficient_derivative
    (r := S.r u) (lam := S.lam u) (nu := S.nu u) (m := S.m u) (phiV := S.dvphi u)
    (h.acdatum_radius_hasDerivAt_out hu hu0 huv hv) hn' hm' hr0 hl0 hmu
  convert hh.neg using 1
  · funext x
    simp [incomingDatumCoeff, SSFields.gamma, SSFields.varkappa, SSFields.mu]
  · dsimp [outgoingDatumCoeffDerivative, SSFields.gamma, SSFields.dvphi,
      gammaOf, SSFields.mu]
    field_simp [hr0.ne', hl0.ne']

/-- Continuity of the scalar derivative on each proper rectangle.
Paper `e1a0fd5`, lines 594–601. -/
theorem dvphi_continuous_rectangle {U a b : ℝ}
    (hui : ui ≤ U) (hab : a ≤ b) (hU : U < 0) (hUa : U < a) (hb : b ≤ 0) :
    ContinuousOn (fun p : ℝ × ℝ => S.dvphi p.1 p.2) (Icc ui U ×ˢ Icc a b) := by
  have hs := properRectangle_subset_triangle (ui := ui) hU hUa hb
  have hd := h.dvpsi_continuous_rectangle hui hab hU hUa hb
  have hl := h.regularCenter.continuous_lam.mono hs
  have hf := h.regularCenter.continuous_phi.mono hs
  have hr := h.regularCenter.continuous_r.mono hs
  exact (hd.sub (hl.mul hf)).div hr
    (fun p hp => (h.r_pos (hs hp) (hp.1.2.trans_lt (hUa.trans_le hp.2.1))).ne')

/-- The coefficient derivative is jointly continuous on proper rectangles,
so differentiation under incoming integrals needs no extra source assumption.
Paper `e1a0fd5`, lines 596–601. -/
theorem outgoingDatumCoeffDerivative_continuous_rectangle {U a b : ℝ}
    (hui : ui ≤ U) (hab : a ≤ b) (hU : U < 0) (hUa : U < a) (hb : b ≤ 0) :
    ContinuousOn (fun p : ℝ × ℝ => outgoingDatumCoeffDerivative S p.1 p.2)
      (Icc ui U ×ˢ Icc a b) := by
  have hs := properRectangle_subset_triangle (ui := ui) hU hUa hb
  have hr := h.regularCenter.continuous_r.mono hs
  have hm := h.regularCenter.continuous_m.mono hs
  have hn := h.regularCenter.continuous_nu.mono hs
  have hl := h.regularCenter.continuous_lam.mono hs
  have hf := h.regularCenter.continuous_phi.mono hs
  have hd := h.dvpsi_continuous_rectangle hui hab hU hUa hb
  have hr0 : ∀ p ∈ Icc ui U ×ˢ Icc a b, S.r p.1 p.2 ≠ 0 :=
    fun p hp => (h.r_pos (hs hp) (hp.1.2.trans_lt (hUa.trans_le hp.2.1))).ne'
  have hl0 : ∀ p ∈ Icc ui U ×ˢ Icc a b, S.lam p.1 p.2 ≠ 0 :=
    fun p hp => (h.lam_pos (hs hp)).ne'
  have hmc : ContinuousOn (fun p : ℝ × ℝ => S.mu p.1 p.2) (Icc ui U ×ˢ Icc a b) :=
    (continuousOn_const.mul hm).div hr hr0
  have hgc : ContinuousOn (fun p : ℝ × ℝ => S.gamma p.1 p.2) (Icc ui U ×ˢ Icc a b) :=
    hn.div (continuousOn_const.sub hmc)
      (fun p hp => (sub_pos.mpr (h.mu_bounds (hs hp)).2).ne')
  have hA : ContinuousOn (fun p : ℝ × ℝ => S.theta p.1 p.2 / S.lam p.1 p.2)
      (Icc ui U ×ˢ Icc a b) := (hd.sub (hl.mul hf)).div hl hl0
  have h2mu : ContinuousOn (fun p : ℝ × ℝ => 2 * S.mu p.1 p.2)
      (Icc ui U ×ˢ Icc a b) := continuousOn_const.mul hmc
  exact (hl.mul (hgc.div (hr.pow 2) (fun p hp => pow_ne_zero 2 (hr0 p hp)))).mul
    ((hA.pow 2).sub h2mu)

end StandingFull

end AcExtensionPrinciple

end
