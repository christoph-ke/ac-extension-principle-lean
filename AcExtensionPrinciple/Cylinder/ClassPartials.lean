module

public import AcExtensionPrinciple.Cylinder.IncomingContinuity

/-!
# Characteristic scalar and mass partials from the solution class

This module discharges the derivative certificates in Lemma 2.4.
Paper `e1a0fd5`, `eq:cylinder-mass-balance`, `eq:cylinder-scalar-derivative`,
lines 709–737. No boundary derivative certificates are assumed.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- Continuous characteristic partials determine a strict total derivative.
Paper `e1a0fd5`, calculus used at lines 709–737. -/
theorem cylinder_strict_derivative_of_partials {ui : ℝ} {f fu fv : ℝ → ℝ → ℝ}
    (hu : ∀ p ∈ cylinderInterior ui, HasDerivAt (fun u => f u p.2) (fu p.1 p.2) p.1)
    (hv : ∀ p ∈ cylinderInterior ui, HasDerivAt (f p.1) (fv p.1 p.2) p.2)
    (hcu : ContinuousOn (fun p => fu p.1 p.2) (cylinderInterior ui))
    (hcv : ContinuousOn (fun p => fv p.1 p.2) (cylinderInterior ui))
    {p : ℝ × ℝ} (hp : p ∈ cylinderInterior ui) :
    HasStrictFDerivAt (fun p => f p.1 p.2)
      ((cylinderLinear (fu p.1 p.2)).coprod (cylinderLinear (fv p.1 p.2))) p := by
  have hn := (isOpen_cylinderInterior ui).mem_nhds hp
  apply hasStrictFDerivAt_uncurry_coprod (f := f)
    (f₁ := fun u v => cylinderLinear (fu u v))
    (f₂ := fun u v => cylinderLinear (fv u v))
  · filter_upwards [hn] with q hq
    exact (hu q hq).hasFDerivAt
  · filter_upwards [hn] with q hq
    exact (hv q hq).hasFDerivAt
  · exact ContinuousLinearMap.toSpanSingletonCLE.continuous.continuousAt.comp
      (hcu.continuousAt hn)
  · exact ContinuousLinearMap.toSpanSingletonCLE.continuous.continuousAt.comp
      (hcv.continuousAt hn)

/-- Interior points belong to the closed off-axis scalar domain.
Paper `e1a0fd5`, lines 709–737. -/
theorem cylinderInterior_subset_scalarRegion (ui : ℝ) :
    cylinderInterior ui ⊆ cylinderScalarRegion ui :=
  fun _ hp => ⟨hp.1.le, hp.2.1, hp.2.2.le⟩

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The incoming mass integrand is jointly continuous away from the axis.
Paper `e1a0fd5`, `eq:mass`, lines 709–737. -/
theorem cylinder_massU_continuous :
    ContinuousOn (fun p => S.massU p.1 p.2) (cylinderScalarRegion ui) := by
  have hs := cylinderScalarRegion_subset ui
  have hz := h.cylinder_dupsi_continuous.sub
    ((h.regularCenter.continuous_nu.mono hs).mul (h.regularCenter.continuous_phi.mono hs))
  exact ((continuousOn_const.sub h.cylinder_mu_continuous).mul (hz.pow 2)).div
    (continuousOn_const.mul (h.regularCenter.continuous_nu.mono hs))
    (fun p hp => mul_ne_zero (by norm_num) (h.nu_neg (hs hp)).ne)

/-- The outgoing mass integrand is jointly continuous away from the axis.
Paper `e1a0fd5`, `eq:mass`, lines 709–737. -/
theorem cylinder_massV_continuous :
    ContinuousOn (fun p => S.massV p.1 p.2) (cylinderScalarRegion ui) := by
  have hs := cylinderScalarRegion_subset ui
  have ht := h.cylinder_dvpsi_continuous.sub
    ((h.regularCenter.continuous_lam.mono hs).mul (h.regularCenter.continuous_phi.mono hs))
  exact ((continuousOn_const.sub h.cylinder_mu_continuous).mul (ht.pow 2)).div
    (continuousOn_const.mul (h.regularCenter.continuous_lam.mono hs))
    (fun p hp => mul_ne_zero (by norm_num) (h.lam_pos (hs hp)).ne')

/-- Incoming ψ partial recovered from the characteristic primitive.
Paper `e1a0fd5`, `eq:wave-psi`, lines 709–737. -/
theorem cylinder_psi_hasDerivAt_in {u v : ℝ} (hp : (u, v) ∈ cylinderInterior ui) :
    HasDerivAt (fun s => S.r s v * S.phi s v) (S.dupsi u v) u := by
  let d := (u + v) / 2
  have hud : u < d := by dsimp [d]; linarith [hp.2.1]
  have hdv : d < v := by dsimp [d]; linarith [hp.2.1]
  have hs : inSeg v ui d ⊆ cylinderScalarRegion ui := by
    intro p hps
    have hps' : p.1 ∈ Icc ui d ∧ p.2 = v := by simpa only [inSeg, mem_prod,
      mem_singleton_iff] using hps
    exact ⟨hps'.1.1, by rw [hps'.2]; exact hps'.1.2.trans_lt hdv, by simpa [hps'.2] using hp.2.2.le⟩
  apply intervalPrimitive_hasDerivAt ⟨hp.1, hud⟩
    (h.cylinder_dupsi_continuous.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs' => hs ⟨hs', by simp⟩))
  intro x hx
  exact h.regularCenter.localBV.psi_in v ui x hx.1
    (inSeg_subset_triangle le_rfl (hx.2.trans_lt (hdv.trans hp.2.2))
      (hx.2.trans hdv.le) hp.2.2.le)

/-- Outgoing ψ partial recovered from the characteristic primitive.
Paper `e1a0fd5`, `eq:wave-psi`, lines 709–737. -/
theorem cylinder_psi_hasDerivAt_out {u v : ℝ} (hp : (u, v) ∈ cylinderInterior ui) :
    HasDerivAt (fun s => S.r u s * S.phi u s) (S.dvpsi u v) v := by
  let a := (u + v) / 2
  have hua : u < a := by dsimp [a]; linarith [hp.2.1]
  have hav : a < v := by dsimp [a]; linarith [hp.2.1]
  have hc : ContinuousOn (S.dvpsi u) (Icc a 0) :=
    h.cylinder_dvpsi_continuous.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun s hs => ⟨hp.1.le, hua.trans_le hs.1, hs.2⟩)
  apply intervalPrimitive_hasDerivAt ⟨hav, hp.2.2⟩ hc
  intro x hx
  exact h.regularCenter.localBV.psi_out u a x hx.1
    (outSeg_subset_triangle hp.1.le (hp.2.1.trans hp.2.2) hua.le hx.2)

/-- Incoming φ partial is the shared scalar derivative field.
Paper `e1a0fd5`, `eq:cylinder-scalar-derivative`, lines 716–719. -/
theorem cylinder_phi_hasDerivAt_in {u v : ℝ} (hp : (u, v) ∈ cylinderInterior ui) :
    HasDerivAt (fun s => S.phi s v) (S.duphi u v) u := by
  have hr := h.radius_hasDerivAt_in hp
  have hr0 := (h.r_pos (cylinderInterior_subset ui hp) hp.2.1).ne'
  have hd := (h.cylinder_psi_hasDerivAt_in hp).div hr hr0
  have heq : (S.dupsi u v * S.r u v - (S.r u v * S.phi u v) * S.nu u v) /
      (S.r u v) ^ 2 = S.duphi u v := by
    unfold SSFields.duphi SSFields.zeta
    field_simp [hr0]
  apply (hd.congr_deriv heq).congr_of_eventuallyEq
  filter_upwards [hr.continuousAt.eventually (eventually_ne_nhds hr0)] with s hs
  exact (mul_div_cancel_left₀ (S.phi s v) hs).symm

/-- Outgoing φ partial is the shared scalar derivative field.
Paper `e1a0fd5`, `eq:cylinder-scalar-derivative`, lines 716–719. -/
theorem cylinder_phi_hasDerivAt_out {u v : ℝ} (hp : (u, v) ∈ cylinderInterior ui) :
    HasDerivAt (S.phi u) (S.dvphi u v) v := by
  have hr := h.radius_hasDerivAt_out hp
  have hr0 := (h.r_pos (cylinderInterior_subset ui hp) hp.2.1).ne'
  have hd := (h.cylinder_psi_hasDerivAt_out hp).div hr hr0
  have heq : (S.dvpsi u v * S.r u v - (S.r u v * S.phi u v) * S.lam u v) /
      (S.r u v) ^ 2 = S.dvphi u v := by
    unfold SSFields.dvphi SSFields.theta
    field_simp [hr0]
  apply (hd.congr_deriv heq).congr_of_eventuallyEq
  filter_upwards [hr.continuousAt.eventually (eventually_ne_nhds hr0)] with s hs
  exact (mul_div_cancel_left₀ (S.phi u s) hs).symm

/-- Incoming mass partial recovered from its continuous characteristic integrand.
Paper `e1a0fd5`, `eq:cylinder-mass-balance`, lines 709–716. -/
theorem cylinder_mass_hasDerivAt_in {u v : ℝ} (hp : (u, v) ∈ cylinderInterior ui) :
    HasDerivAt (fun s => S.m s v) (S.massU u v) u := by
  let d := (u + v) / 2
  have hud : u < d := by dsimp [d]; linarith [hp.2.1]
  have hdv : d < v := by dsimp [d]; linarith [hp.2.1]
  have hmap : MapsTo (fun s : ℝ => (s, v)) (Icc ui d) (cylinderScalarRegion ui) :=
    fun s hs => ⟨hs.1, hs.2.trans_lt hdv, hp.2.2.le⟩
  have hpair : ContinuousOn (fun s : ℝ => (s, v)) (Icc ui d) :=
    (continuous_id.prodMk continuous_const).continuousOn
  have hc := h.cylinder_massU_continuous.comp hpair hmap
  apply intervalPrimitive_hasDerivAt (f := fun s => S.m s v)
    (g := fun s => S.massU s v) ⟨hp.1, hud⟩ hc
  intro x hx
  exact h.regularCenter.localBV.mass_in v ui x hx.1
    (inSeg_subset_triangle le_rfl (hx.2.trans_lt (hdv.trans hp.2.2))
      (hx.2.trans hdv.le) hp.2.2.le)

/-- Outgoing mass partial recovered from its continuous characteristic integrand.
Paper `e1a0fd5`, `eq:cylinder-mass-balance`, lines 709–716. -/
theorem cylinder_mass_hasDerivAt_out {u v : ℝ} (hp : (u, v) ∈ cylinderInterior ui) :
    HasDerivAt (S.m u) (S.massV u v) v := by
  let a := (u + v) / 2
  have hua : u < a := by dsimp [a]; linarith [hp.2.1]
  have hav : a < v := by dsimp [a]; linarith [hp.2.1]
  have hmap : MapsTo (fun s : ℝ => (u, s)) (Icc a 0) (cylinderScalarRegion ui) :=
    fun s hs => ⟨hp.1.le, hua.trans_le hs.1, hs.2⟩
  have hpair : ContinuousOn (fun s : ℝ => (u, s)) (Icc a 0) :=
    (continuous_const.prodMk continuous_id).continuousOn
  have hc := h.cylinder_massV_continuous.comp hpair hmap
  apply intervalPrimitive_hasDerivAt (f := S.m u) (g := S.massV u) ⟨hav, hp.2.2⟩ hc
  intro x hx
  exact h.regularCenter.localBV.mass_out u a x hx.1
    (outSeg_subset_triangle hp.1.le (hp.2.1.trans hp.2.2) hua.le hx.2)

/-- Total scalar derivative certificate from the standing class alone.
Paper `e1a0fd5`, `eq:cylinder-scalar-derivative`, lines 716–719. -/
theorem cylinder_phi_hasFDerivAt {p : ℝ × ℝ} (hp : p ∈ cylinderInterior ui) :
    HasFDerivAt (fun p => S.phi p.1 p.2)
      ((cylinderLinear (S.duphi p.1 p.2)).coprod (cylinderLinear (S.dvphi p.1 p.2))) p :=
  (cylinder_strict_derivative_of_partials (f := S.phi) (fu := S.duphi) (fv := S.dvphi)
    (fun _ hq => h.cylinder_phi_hasDerivAt_in hq)
    (fun _ hq => h.cylinder_phi_hasDerivAt_out hq)
    (h.cylinder_duphi_continuous.mono (cylinderInterior_subset_scalarRegion ui))
    (h.cylinder_dvphi_continuous.mono (cylinderInterior_subset_scalarRegion ui)) hp).hasFDerivAt

/-- Total mass derivative certificate from the standing class alone.
Paper `e1a0fd5`, `eq:cylinder-mass-balance`, lines 709–716. -/
theorem cylinder_mass_hasFDerivAt {p : ℝ × ℝ} (hp : p ∈ cylinderInterior ui) :
    HasFDerivAt (fun p => S.m p.1 p.2)
      ((cylinderLinear (S.massU p.1 p.2)).coprod (cylinderLinear (S.massV p.1 p.2))) p :=
  (cylinder_strict_derivative_of_partials (f := S.m) (fu := S.massU) (fv := S.massV)
    (fun _ hq => h.cylinder_mass_hasDerivAt_in hq)
    (fun _ hq => h.cylinder_mass_hasDerivAt_out hq)
    (h.cylinder_massU_continuous.mono (cylinderInterior_subset_scalarRegion ui))
    (h.cylinder_massV_continuous.mono (cylinderInterior_subset_scalarRegion ui)) hp).hasFDerivAt

end StandingFull

end AcExtensionPrinciple

end
