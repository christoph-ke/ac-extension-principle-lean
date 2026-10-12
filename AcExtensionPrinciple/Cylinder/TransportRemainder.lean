module

public import AcExtensionPrinciple.Cylinder.LambdaRegularity
public import AcExtensionPrinciple.Cylinder.Energy

/-!
# Regular remainder in the incoming ψ transport

This module derives regularity of the transport remainder from the solution class.
Paper `e1a0fd5`, linear transport representation
at lines 422–428 and Lemma 2.4 regularity argument at lines 731–737.
The initial AC datum is kept separate; only the transport remainder is differentiated.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology NNReal

/-- Incoming integral of the continuous mixed ψ forcing.
Paper `e1a0fd5`, linear transport representation at lines 422–428. -/
@[expose] noncomputable def cylinderJ (S : SSFields) (ui u v : ℝ) : ℝ :=
  ∫ s in ui..u, S.radiusCoeff s v * S.phi s v

/-- Continuous outgoing differential coefficient of the mixed ψ forcing.
Paper `e1a0fd5`, `eq:transport-coefficient-derivative`, lines 731–737. -/
@[expose] noncomputable def cylinderForcingV (S : SSFields) (ui u v : ℝ) : ℝ :=
  (cylinderLambdaV S ui u v * cylinderKernel S u v + S.lam u v * cylinderKernelV S u v) *
    S.phi u v + S.radiusCoeff u v * S.dvphi u v

/-- Outgoing differential coefficient of the incoming forcing primitive.
Paper `e1a0fd5`, lines 422–428, 731–737. -/
@[expose] noncomputable def cylinderJV (S : SSFields) (ui u v : ℝ) : ℝ :=
  ∫ s in ui..u, cylinderForcingV S ui s v

/-- The remainder after separating the initial AC datum from ∂ᵥψ/λ.
Paper `e1a0fd5`, linear transport representation at lines 422–428, 731–737. -/
@[expose] noncomputable def cylinderRemainder (S : SSFields) (ui u v : ℝ) : ℝ :=
  cylinderJ S ui u v / S.lam u v

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The outgoing scalar derivative identity also holds on the initial characteristic.
Paper `e1a0fd5`, lines 422–428, 731–737. -/
theorem cylinder_phi_hasDerivAt_out_closed {u v : ℝ}
    (hp : (u, v) ∈ cylinderScalarRegion ui) (hv : v < 0) :
    HasDerivAt (S.phi u) (S.dvphi u v) v := by
  have hpsi : HasDerivAt (fun s => S.r u s * S.phi u s) (S.dvpsi u v) v := by
    apply cylinder_outgoing_derivative_of_primitive hp hv
      (h.cylinder_dvpsi_continuous.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun s hs => ⟨hp.1, hs.1, hs.2⟩))
    intro a b hua hab hb
    exact h.regularCenter.localBV.psi_out u a b hab
      (outSeg_subset_triangle hp.1 (hp.2.1.trans_le hp.2.2) hua.le hb)
  have hr := h.cylinder_radius_hasDerivAt_out_closed hp hv
  have hr0 := (h.r_pos (cylinderScalarRegion_subset ui hp) hp.2.1).ne'
  have heq : (S.dvpsi u v * S.r u v - (S.r u v * S.phi u v) * S.lam u v) /
      S.r u v ^ 2 = S.dvphi u v := by
    unfold SSFields.dvphi SSFields.theta
    field_simp [hr0]
  apply ((hpsi.div hr hr0).congr_deriv heq).congr_of_eventuallyEq
  filter_upwards [hr.continuousAt.eventually (eventually_ne_nhds hr0)] with s hs
  exact (mul_div_cancel_left₀ (S.phi u s) hs).symm

/-- Differentiate the mixed ψ forcing in v using the continuous kernel and expansion coefficients.
Paper `e1a0fd5`, lines 422–428, 731–737. -/
theorem cylinder_forcing_hasDerivAt_out {u v : ℝ}
    (hp : (u, v) ∈ cylinderScalarRegion ui) (hv : v < 0) :
    HasDerivAt (fun t => S.radiusCoeff u t * S.phi u t)
      (cylinderForcingV S ui u v) v := by
  have hd := ((h.cylinder_lambda_hasDerivAt_out hp hv).mul
    (h.cylinder_kernel_hasDerivAt_out hp hv)).mul
      (h.cylinder_phi_hasDerivAt_out_closed hp hv)
  convert hd using 1
  · funext t
    rw [cylinder_radiusCoeff_eq]
    rfl
  · simp only [cylinderForcingV, cylinder_radiusCoeff_eq, Pi.mul_apply]

/-- The differentiated forcing is jointly continuous on the closed regular off-axis region.
Paper `e1a0fd5`, lines 422–428, 731–737. -/
theorem cylinder_forcingV_continuous :
    ContinuousOn (fun p => cylinderForcingV S ui p.1 p.2) (cylinderScalarRegion ui) := by
  have hs := cylinderScalarRegion_subset ui
  have hl := h.regularCenter.continuous_lam.mono hs
  have hphi := h.regularCenter.continuous_phi.mono hs
  exact (((h.cylinder_lambdaV_continuous.mul h.cylinder_kernel_continuous).add
    (hl.mul h.cylinder_kernelV_continuous)).mul hphi).add
      (h.cylinder_radiusCoeff_continuous.mul h.cylinder_dvphi_continuous)

/-- The transport primitive J is jointly continuous off-axis.
Paper `e1a0fd5`, lines 422–428, 731–737. -/
theorem cylinder_J_continuous :
    ContinuousOn (fun p => cylinderJ S ui p.1 p.2) (cylinderScalarRegion ui) :=
  cylinder_primitive_continuous_region
    (F := fun u v => S.radiusCoeff u v * S.phi u v) h.cylinder_forcing_continuous

/-- Its outgoing differential coefficient is jointly continuous through the characteristic edges.
Paper `e1a0fd5`, lines 422–428, 731–737. -/
theorem cylinder_JV_continuous :
    ContinuousOn (fun p => cylinderJV S ui p.1 p.2) (cylinderScalarRegion ui) :=
  cylinder_primitive_continuous_region (F := cylinderForcingV S ui) h.cylinder_forcingV_continuous

/-- Outgoing derivative of J, including the initial characteristic.
Paper `e1a0fd5`, lines 422–428, 731–737. -/
theorem cylinder_J_hasDerivAt_out {u v : ℝ} (hp : (u, v) ∈ cylinderScalarRegion ui)
    (hv : v < 0) : HasDerivAt (cylinderJ S ui u) (cylinderJV S ui u v) v := by
  let U := (u + v) / 2
  let a := (U + v) / 2
  have huU : u < U := by dsimp [U]; linarith [hp.2.1]
  have hUa : U < a := by dsimp [a, U]; linarith [hp.2.1]
  have hav : a < v := by dsimp [a, U]; linarith [hp.2.1]
  have hUi := hp.1.trans huU.le
  have hs := cylinder_rectangle_subset_region (ui := ui) hUa (le_refl 0)
  exact cylinder_rectangle_integral_hasDerivAt
    (F := fun u v => S.radiusCoeff u v * S.phi u v) (Fv := cylinderForcingV S ui)
    hUi (hav.le.trans hv.le) ⟨hp.1, huU.le⟩ ⟨hav, hv⟩
    (h.cylinder_forcing_continuous.mono hs) (h.cylinder_forcingV_continuous.mono hs)
    (fun s hss t ht => h.cylinder_forcing_hasDerivAt_out
      ⟨hss.1, hss.2.trans_lt (hUa.trans ht.1), ht.2.le⟩ ht.2)

/-- Incoming derivative of J by the continuous-integrand fundamental theorem.
Paper `e1a0fd5`, lines 422–428, 731–737. -/
theorem cylinder_J_hasDerivAt_in {u v : ℝ} (hp : (u, v) ∈ cylinderInterior ui) :
    HasDerivAt (fun s => cylinderJ S ui s v) (S.radiusCoeff u v * S.phi u v) u := by
  let d := (u + v) / 2
  have hud : u < d := by dsimp [d]; linarith [hp.2.1]
  have hdv : d < v := by dsimp [d]; linarith [hp.2.1]
  have hmap : MapsTo (fun s : ℝ => (s, v)) (Icc ui d) (cylinderScalarRegion ui) :=
    fun s hs => ⟨hs.1, hs.2.trans_lt hdv, hp.2.2.le⟩
  have hpair : ContinuousOn (fun s : ℝ => (s, v)) (Icc ui d) :=
    (continuous_id.prodMk continuous_const).continuousOn
  have hc0 := h.cylinder_forcing_continuous.comp hpair hmap
  have hc : ContinuousOn (fun s => S.radiusCoeff s v * S.phi s v) (Icc ui d) :=
    by simpa only [Function.comp_def] using hc0
  apply intervalPrimitive_hasDerivAt (f := fun s => cylinderJ S ui s v)
    (g := fun s => S.radiusCoeff s v * S.phi s v) ⟨hp.1, hud⟩ hc
  intro x hx
  constructor
  · exact (hc.mono (Icc_subset_Icc le_rfl hx.2)).intervalIntegrable_of_Icc hx.1
  · simp only [cylinderJ, intervalIntegral.integral_same, sub_zero]

/-- J has the total derivative used by the cylinder chain rule.
Paper `e1a0fd5`, lines 422–428, 731–737. -/
theorem cylinder_J_hasFDerivAt {p : ℝ × ℝ} (hp : p ∈ cylinderInterior ui) :
    HasFDerivAt (fun p => cylinderJ S ui p.1 p.2)
      ((cylinderLinear (S.radiusCoeff p.1 p.2 * S.phi p.1 p.2)).coprod
        (cylinderLinear (cylinderJV S ui p.1 p.2))) p :=
  (cylinder_strict_derivative_of_partials (f := cylinderJ S ui)
    (fu := fun u v => S.radiusCoeff u v * S.phi u v) (fv := cylinderJV S ui)
    (fun _ hq => h.cylinder_J_hasDerivAt_in hq)
    (fun _ hq => h.cylinder_J_hasDerivAt_out (cylinderInterior_subset_scalarRegion ui hq) hq.2.2)
    (h.cylinder_forcing_continuous.mono (cylinderInterior_subset_scalarRegion ui))
    (h.cylinder_JV_continuous.mono (cylinderInterior_subset_scalarRegion ui)) hp).hasFDerivAt

/-- Discharge the exact representation premise, separating the initial datum
from a regular remainder.
Paper `e1a0fd5`, `eq:scalar-bound-linear-transport`, lines 422–428, 731–737. -/
theorem cylinder_P_representation {u v : ℝ} (hp : (u, v) ∈ cylinderScalarRegion ui) :
    S.dvpsi u v / S.lam u v = S.dvpsi ui v / S.lam u v + cylinderRemainder S ui u v := by
  rw [h.cylinder_dvpsi_representation hp, add_div]
  rfl

/-- Discharge hR: the transport remainder is Lipschitz on every nondegenerate regular cylinder
interval. Paper `e1a0fd5`, linear transport proof of trace AC at lines 731–737. -/
theorem cylinder_remainder_lipschitz_regular {b a0 a1 : ℝ} (hb : 0 < b)
    (hI : RegularCylinderInterval ui S b a0 a1) (ha : a0 < a1) :
    ∃ K : ℝ≥0, LipschitzOnWith K
      (fun u => cylinderRemainder S ui u (cylinderV h b u)) (Icc a0 a1) := by
  let v := cylinderV h b
  have hv := h.cylinderV_continuousOn_regular hb hI
  have hc := continuousOn_id.prodMk hv
  have hp : MapsTo (fun u => (u, v u)) (Icc a0 a1) (cylinderScalarRegion ui) :=
    fun _ hu => h.cylinderV_mem_regular hb hI hu
  have hpt (u : ℝ) (hu : u ∈ Icc a0 a1) := cylinderScalarRegion_subset ui (hp hu)
  have hcL := h.regularCenter.continuous_lam.comp hc hpt
  have hcJ := h.cylinder_J_continuous.comp hc hp
  have hcF := h.cylinder_forcing_continuous.comp hc hp
  have hcRC := h.cylinder_radiusCoeff_continuous.comp hc hp
  have hcLV := h.cylinder_lambdaV_continuous.comp hc hp
  have hcJV := h.cylinder_JV_continuous.comp hc hp
  have hcQ := h.cylinderV_tangent_continuousOn_regular hb hI
  let jd := fun u => S.radiusCoeff u (v u) * S.phi u (v u) +
    cylinderJV S ui u (v u) * (-S.nu u (v u) / S.lam u (v u))
  let ld := fun u => S.radiusCoeff u (v u) +
    cylinderLambdaV S ui u (v u) * (-S.nu u (v u) / S.lam u (v u))
  have hcjd : ContinuousOn jd (Icc a0 a1) := hcF.add (hcJV.mul hcQ)
  have hcld : ContinuousOn ld (Icc a0 a1) := hcRC.add (hcLV.mul hcQ)
  have hcR : ContinuousOn (fun u => cylinderRemainder S ui u (v u)) (Icc a0 a1) :=
    hcJ.div hcL (fun _ hu => (h.lam_pos (hpt _ hu)).ne')
  have hcRD : ContinuousOn (fun u => (jd u * S.lam u (v u) -
      cylinderJ S ui u (v u) * ld u) / S.lam u (v u) ^ 2) (Icc a0 a1) :=
    ((hcjd.mul hcL).sub (hcJ.mul hcld)).div (hcL.pow 2)
      (fun _ hu => pow_ne_zero _ (h.lam_pos (hpt _ hu)).ne')
  apply cylinder_interval_lipschitz
    (g := fun u => (jd u * S.lam u (v u) - cylinderJ S ui u (v u) * ld u) /
      S.lam u (v u) ^ 2) ha hcR hcRD
  intro u hu
  have hD := h.cylinder_regular_interior hI ⟨hu.1.le, hu.2⟩
  have hvs := (h.cylinderV_spec hb hD).1
  have hpi : (u, v u) ∈ cylinderInterior ui := ⟨hI.2.1.trans_lt hu.1, hvs⟩
  have hvd := (hasDerivAt_id u).prodMk (h.cylinderV_hasDerivAt_regular hb hI hu)
  have hjd : HasDerivAt (fun s => cylinderJ S ui s (v s)) (jd u) u := by
    convert (h.cylinder_J_hasFDerivAt hpi).comp_hasDerivAt u hvd using 1
    all_goals first | rfl | (simp only [ContinuousLinearMap.coprod_apply, cylinderLinear,
      jd, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, one_mul]; ring)
  have hld : HasDerivAt (fun s => S.lam s (v s)) (ld u) u := by
    convert (h.cylinder_lambda_hasFDerivAt hpi).comp_hasDerivAt u hvd using 1
    all_goals first | rfl | (simp only [ContinuousLinearMap.coprod_apply, cylinderLinear,
      ld, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, one_mul]; ring)
  exact hjd.div hld (h.lam_pos (hpt u (Ioo_subset_Icc_self hu))).ne'

end StandingFull

end AcExtensionPrinciple

end
