module

public import AcExtensionPrinciple.Cylinder.KernelDerivative
public import AcExtensionPrinciple.Cylinder.RegularInterval
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Expansion regularity from its integrating factor

This module derives λ regularity from the solution class.
Paper `e1a0fd5`, `eq:lambda-integrating-factor`,
`eq:scalar-bound-linear-transport`, lines 422–428 and 731–737.
The outgoing derivative follows by differentiating the continuous kernel integral.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology NNReal

/-- The continuous outgoing expansion coefficient obtained from the integrating factor.
Paper `e1a0fd5`, `eq:lambda-integrating-factor`, lines 422–428, 731–737. -/
@[expose] noncomputable def cylinderLambdaV (S : SSFields) (ui u v : ℝ) : ℝ :=
  S.lam u v * ∫ s in ui..u, cylinderKernelV S s v

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The outgoing expansion coefficient is continuous on the closed off-axis region.
Paper `e1a0fd5`, lines 422–428, 731–737. -/
theorem cylinder_lambdaV_continuous :
    ContinuousOn (fun p => cylinderLambdaV S ui p.1 p.2) (cylinderScalarRegion ui) :=
  (h.regularCenter.continuous_lam.mono (cylinderScalarRegion_subset ui)).mul
    (cylinder_primitive_continuous_region (F := cylinderKernelV S) h.cylinder_kernelV_continuous)

/-- Differentiate λ in v using only the radius integrating factor and its continuous kernel.
This holds also on the initial characteristic u=ui.
Paper `e1a0fd5`, `eq:lambda-integrating-factor`, lines 422–428, 731–737. -/
theorem cylinder_lambda_hasDerivAt_out {u v : ℝ} (hp : (u, v) ∈ cylinderScalarRegion ui)
    (hv : v < 0) : HasDerivAt (S.lam u) (cylinderLambdaV S ui u v) v := by
  let U := (u + v) / 2
  let a := (U + v) / 2
  have huU : u < U := by dsimp [U]; linarith [hp.2.1]
  have hUa : U < a := by dsimp [a, U]; linarith [hp.2.1]
  have hav : a < v := by dsimp [a, U]; linarith [hp.2.1]
  have hUi := hp.1.trans huU.le
  have hs := cylinder_rectangle_subset_region (ui := ui) hUa (le_refl 0)
  have hdJ := cylinder_rectangle_integral_hasDerivAt
    (F := cylinderKernel S) (Fv := cylinderKernelV S) hUi (hav.le.trans hv.le)
    ⟨hp.1, huU.le⟩ ⟨hav, hv⟩
    (h.cylinder_kernel_continuous.mono hs) (h.cylinder_kernelV_continuous.mono hs)
    (fun s hss t ht => h.cylinder_kernel_hasDerivAt_out
      ⟨hss.1, hss.2.trans_lt (hUa.trans ht.1), ht.2.le⟩ ht.2)
  have heq : Real.exp (∫ s in ui..u, cylinderKernel S s v) *
      (∫ s in ui..u, cylinderKernelV S s v) = cylinderLambdaV S ui u v := by
    rw [← h.cylinder_lambda_representation hp]
    rfl
  apply (hdJ.exp.congr_deriv heq).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hav hv] with t ht
  exact h.cylinder_lambda_representation ⟨hp.1, huU.trans (hUa.trans ht.1), ht.2.le⟩

/-- Incoming expansion derivative from the original radius transport primitive.
Paper `e1a0fd5`, `eq:radius`, lines 422–428, 731–737. -/
theorem cylinder_lambda_hasDerivAt_in {u v : ℝ} (hp : (u, v) ∈ cylinderInterior ui) :
    HasDerivAt (fun s => S.lam s v) (S.radiusCoeff u v) u := by
  let d := (u + v) / 2
  have hud : u < d := by dsimp [d]; linarith [hp.2.1]
  have hdv : d < v := by dsimp [d]; linarith [hp.2.1]
  have hmap : MapsTo (fun s : ℝ => (s, v)) (Icc ui d) (cylinderScalarRegion ui) :=
    fun s hs => ⟨hs.1, hs.2.trans_lt hdv, hp.2.2.le⟩
  have hpair : ContinuousOn (fun s : ℝ => (s, v)) (Icc ui d) :=
    (continuous_id.prodMk continuous_const).continuousOn
  have hc := h.cylinder_radiusCoeff_continuous.comp hpair hmap
  apply intervalPrimitive_hasDerivAt (f := fun s => S.lam s v)
    (g := fun s => S.radiusCoeff s v) ⟨hp.1, hud⟩ hc
  intro x hx
  exact h.regularCenter.localBV.lam_in v ui x hx.1
    (inSeg_subset_offAxis le_rfl (hx.2.trans_lt (hdv.trans hp.2.2))
      (hx.2.trans_lt hdv) hp.2.2.le)

/-- The expansion has its total derivative at every interior off-axis point.
Paper `e1a0fd5`, lines 422–428, 731–737. -/
theorem cylinder_lambda_hasFDerivAt {p : ℝ × ℝ} (hp : p ∈ cylinderInterior ui) :
    HasFDerivAt (fun p => S.lam p.1 p.2)
      ((cylinderLinear (S.radiusCoeff p.1 p.2)).coprod
        (cylinderLinear (cylinderLambdaV S ui p.1 p.2))) p :=
  (cylinder_strict_derivative_of_partials (f := S.lam) (fu := S.radiusCoeff)
    (fv := cylinderLambdaV S ui)
    (fun _ hq => h.cylinder_lambda_hasDerivAt_in hq)
    (fun _ hq => h.cylinder_lambda_hasDerivAt_out
      (cylinderInterior_subset_scalarRegion ui hq) hq.2.2)
    (h.cylinder_radiusCoeff_continuous.mono (cylinderInterior_subset_scalarRegion ui))
    (h.cylinder_lambdaV_continuous.mono (cylinderInterior_subset_scalarRegion ui)) hp).hasFDerivAt

/-- Discharge hL: λ_b is Lipschitz on every nondegenerate regular cylinder interval. Paper
`e1a0fd5`, linear transport argument at lines 731–737. -/
theorem cylinder_lambda_lipschitz_regular {b a0 a1 : ℝ} (hb : 0 < b)
    (hI : RegularCylinderInterval ui S b a0 a1) (ha : a0 < a1) :
    ∃ K : ℝ≥0, LipschitzOnWith K (fun u => S.lam u (cylinderV h b u)) (Icc a0 a1) := by
  have hv := h.cylinderV_continuousOn_regular hb hI
  have hc := continuousOn_id.prodMk hv
  have hp : MapsTo (fun u => (u, cylinderV h b u)) (Icc a0 a1) (cylinderScalarRegion ui) :=
    fun _ hu => h.cylinderV_mem_regular hb hI hu
  have hpt (u : ℝ) (hu : u ∈ Icc a0 a1) := cylinderScalarRegion_subset ui (hp hu)
  have hcL := h.regularCenter.continuous_lam.comp hc hpt
  have hcRC := h.cylinder_radiusCoeff_continuous.comp hc hp
  have hcLV := h.cylinder_lambdaV_continuous.comp hc hp
  have hcQ := h.cylinderV_tangent_continuousOn_regular hb hI
  apply cylinder_interval_lipschitz
    (g := fun u => S.radiusCoeff u (cylinderV h b u) +
      cylinderLambdaV S ui u (cylinderV h b u) *
        (-S.nu u (cylinderV h b u) / S.lam u (cylinderV h b u)))
    ha hcL (hcRC.add (hcLV.mul hcQ))
  intro u hu
  have hD := h.cylinder_regular_interior hI ⟨hu.1.le, hu.2⟩
  have hvs := (h.cylinderV_spec hb hD).1
  have hpi : (u, cylinderV h b u) ∈ cylinderInterior ui :=
    ⟨hI.2.1.trans_lt hu.1, hvs⟩
  convert (h.cylinder_lambda_hasFDerivAt hpi).comp_hasDerivAt u
    ((hasDerivAt_id u).prodMk (h.cylinderV_hasDerivAt_regular hb hI hu)) using 1
  simp only [ContinuousLinearMap.coprod_apply, cylinderLinear,
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, one_mul]
  ring

end StandingFull

end AcExtensionPrinciple

end
