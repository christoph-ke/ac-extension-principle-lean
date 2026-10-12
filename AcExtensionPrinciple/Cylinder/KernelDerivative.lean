module

public import AcExtensionPrinciple.Cylinder.ClassPartials

/-!
# Outgoing derivative of the linear transport coefficient

This module derives the transport kernel derivative from the solution class.
Paper `e1a0fd5`, `eq:transport-coefficient-derivative`
and the linear transport representation (lines 422–428, 731–737).
The derivative of γϰ uses r_v, m_v and ν_v, and never assumes λ_v.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- An outgoing continuous primitive has its derivative at every interior outgoing point.
Paper `e1a0fd5`, characteristic calculus used at lines 422–428, 731–737. -/
theorem cylinder_outgoing_derivative_of_primitive {ui u v : ℝ} {f g : ℝ → ℝ}
    (hp : (u, v) ∈ cylinderScalarRegion ui) (hv : v < 0)
    (hg : ContinuousOn g (Ioc u 0))
    (hprim : ∀ a b, u < a → a ≤ b → b ≤ 0 → IntervalPrimitive f g a b) :
    HasDerivAt f (g v) v := by
  let a := (u + v) / 2
  have hua : u < a := by dsimp [a]; linarith [hp.2.1]
  have hav : a < v := by dsimp [a]; linarith [hp.2.1]
  exact intervalPrimitive_hasDerivAt ⟨hav, hv⟩
    (hg.mono (fun s hs => ⟨hua.trans_le hs.1, hs.2⟩))
    (fun s hs => hprim a s hua hs.1 hs.2)

/-- Outgoing mass-ratio derivative, expressed in continuous solution fields.
Paper `e1a0fd5`, `eq:transport-coefficient-derivative`, lines 422–428, 731–737. -/
@[expose] noncomputable def cylinderMuV (S : SSFields) (u v : ℝ) : ℝ :=
  (2 * S.massV u v * S.r u v - (2 * S.m u v) * S.lam u v) / S.r u v ^ 2

/-- Outgoing derivative of γϰ, with no outgoing expansion derivative on the right.
Paper `e1a0fd5`, `eq:transport-coefficient-derivative`, lines 422–428, 731–737. -/
@[expose] noncomputable def cylinderKernelV (S : SSFields) (u v : ℝ) : ℝ :=
  ((S.radiusCoeff u v * S.mu u v + S.nu u v * cylinderMuV S u v) *
      ((1 - S.mu u v) * S.r u v) - (S.nu u v * S.mu u v) *
      ((-cylinderMuV S u v) * S.r u v + (1 - S.mu u v) * S.lam u v)) /
    ((1 - S.mu u v) * S.r u v) ^ 2

/-- The linear transport coefficient equals νμ/((1−μ)r).
Paper `e1a0fd5`, `eq:scalar-bound-linear-transport`, line 422. -/
theorem cylinderKernel_eq (S : SSFields) (u v : ℝ) :
    cylinderKernel S u v = S.nu u v * S.mu u v / ((1 - S.mu u v) * S.r u v) := by
  simp only [cylinderKernel, SSFields.gamma, SSFields.varkappa, gammaOf, varkappaOf,
    div_eq_mul_inv, mul_inv_rev]
  ring

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Radius outgoing derivative, also on the initial characteristic.
Paper `e1a0fd5`, `eq:radius`, lines 422–428. -/
theorem cylinder_radius_hasDerivAt_out_closed {u v : ℝ}
    (hp : (u, v) ∈ cylinderScalarRegion ui) (hv : v < 0) :
    HasDerivAt (S.r u) (S.lam u v) v := by
  apply cylinder_outgoing_derivative_of_primitive hp hv
    (h.regularCenter.continuous_lam.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun s hs => ⟨hp.1, hp.2.1.trans_le hp.2.2, hs.1.le, hs.2⟩))
  intro a b hua hab hb
  exact h.regularCenter.localBV.radius_out u a b hab
    (outSeg_subset_triangle hp.1 (hp.2.1.trans_le hp.2.2) hua.le hb)

/-- Mass outgoing derivative, also on the initial characteristic.
Paper `e1a0fd5`, `eq:mass`, lines 422–428. -/
theorem cylinder_mass_hasDerivAt_out_closed {u v : ℝ}
    (hp : (u, v) ∈ cylinderScalarRegion ui) (hv : v < 0) :
    HasDerivAt (S.m u) (S.massV u v) v := by
  have hmap : MapsTo (fun s : ℝ => (u, s)) (Ioc u 0) (cylinderScalarRegion ui) :=
    fun s hs => ⟨hp.1, hs.1, hs.2⟩
  have hpair : ContinuousOn (fun s : ℝ => (u, s)) (Ioc u 0) :=
    (continuous_const.prodMk continuous_id).continuousOn
  have hc := h.cylinder_massV_continuous.comp hpair hmap
  apply cylinder_outgoing_derivative_of_primitive (f := S.m u) (g := S.massV u) hp hv hc
  intro a b hua hab hb
  exact h.regularCenter.localBV.mass_out u a b hab
    (outSeg_subset_triangle hp.1 (hp.2.1.trans_le hp.2.2) hua.le hb)

/-- Incoming expansion outgoing derivative from the radius transport primitive.
Paper `e1a0fd5`, `eq:radius`, lines 422–428. -/
theorem cylinder_nu_hasDerivAt_out {u v : ℝ}
    (hp : (u, v) ∈ cylinderScalarRegion ui) (hv : v < 0) :
    HasDerivAt (S.nu u) (S.radiusCoeff u v) v := by
  have hmap : MapsTo (fun s : ℝ => (u, s)) (Ioc u 0) (cylinderScalarRegion ui) :=
    fun s hs => ⟨hp.1, hs.1, hs.2⟩
  have hpair : ContinuousOn (fun s : ℝ => (u, s)) (Ioc u 0) :=
    (continuous_const.prodMk continuous_id).continuousOn
  have hc := h.cylinder_radiusCoeff_continuous.comp hpair hmap
  apply cylinder_outgoing_derivative_of_primitive (f := S.nu u) (g := S.radiusCoeff u) hp hv hc
  intro a b hua hab hb
  exact h.regularCenter.localBV.nu_out u a b hab
    (outSeg_subset_offAxis hp.1 (hp.2.1.trans_le hp.2.2) hua hb)

/-- Mass-ratio outgoing derivative from the two primitive fields m and r.
Paper `e1a0fd5`, `eq:transport-coefficient-derivative`, lines 422–428. -/
theorem cylinder_mu_hasDerivAt_out {u v : ℝ}
    (hp : (u, v) ∈ cylinderScalarRegion ui) (hv : v < 0) :
    HasDerivAt (S.mu u) (cylinderMuV S u v) v := by
  exact ((h.cylinder_mass_hasDerivAt_out_closed hp hv).const_mul 2).div
    (h.cylinder_radius_hasDerivAt_out_closed hp hv)
    (h.r_pos (cylinderScalarRegion_subset ui hp) hp.2.1).ne'

/-- The outgoing mass-ratio coefficient is continuous through both characteristic edges.
Paper `e1a0fd5`, `eq:transport-coefficient-derivative`, lines 422–428, 731–737. -/
theorem cylinder_muV_continuous :
    ContinuousOn (fun p => cylinderMuV S p.1 p.2) (cylinderScalarRegion ui) := by
  have hs := cylinderScalarRegion_subset ui
  have hr := h.regularCenter.continuous_r.mono hs
  have hm := h.regularCenter.continuous_m.mono hs
  have hl := h.regularCenter.continuous_lam.mono hs
  exact (((continuousOn_const.mul h.cylinder_massV_continuous).mul hr).sub
    ((continuousOn_const.mul hm).mul hl)).div (hr.pow 2)
    (fun p hp => pow_ne_zero _ (h.r_pos (hs hp) hp.2.1).ne')

/-- γϰ has the stated continuous outgoing derivative at each regular outgoing point.
Paper `e1a0fd5`, `eq:transport-coefficient-derivative`, lines 422–428, 731–737. -/
theorem cylinder_kernel_hasDerivAt_out {u v : ℝ}
    (hp : (u, v) ∈ cylinderScalarRegion ui) (hv : v < 0) :
    HasDerivAt (cylinderKernel S u) (cylinderKernelV S u v) v := by
  have hn := h.cylinder_nu_hasDerivAt_out hp hv
  have hm := h.cylinder_mu_hasDerivAt_out hp hv
  have hr := h.cylinder_radius_hasDerivAt_out_closed hp hv
  have hg : (1 - S.mu u v) * S.r u v ≠ 0 :=
    mul_ne_zero (sub_pos.mpr (h.mu_bounds (cylinderScalarRegion_subset ui hp)).2).ne'
      (h.r_pos (cylinderScalarRegion_subset ui hp) hp.2.1).ne'
  convert (hn.mul hm).div (((hasDerivAt_const v (1 : ℝ)).sub hm).mul hr) hg using 1
  · funext t
    exact cylinderKernel_eq S u t
  · simp only [cylinderKernelV, zero_sub, Pi.mul_apply, Pi.sub_apply]

/-- The outgoing γϰ coefficient is continuous on the closed regular off-axis domain.
Paper `e1a0fd5`, `eq:transport-coefficient-derivative`, lines 422–428, 731–737. -/
theorem cylinder_kernelV_continuous :
    ContinuousOn (fun p => cylinderKernelV S p.1 p.2) (cylinderScalarRegion ui) := by
  have hs := cylinderScalarRegion_subset ui
  have hr := h.regularCenter.continuous_r.mono hs
  have hn := h.regularCenter.continuous_nu.mono hs
  have hl := h.regularCenter.continuous_lam.mono hs
  have hm := h.cylinder_mu_continuous
  have hmv := h.cylinder_muV_continuous
  have hg : ContinuousOn (fun p => 1 - S.mu p.1 p.2) (cylinderScalarRegion ui) :=
    continuousOn_const.sub hm
  have hden := hg.mul hr
  exact ((((h.cylinder_radiusCoeff_continuous.mul hm).add (hn.mul hmv)).mul hden).sub
    ((hn.mul hm).mul ((hmv.neg.mul hr).add (hg.mul hl)))).div (hden.pow 2)
      (fun p hp => pow_ne_zero _ (mul_ne_zero
        (sub_pos.mpr (h.mu_bounds (hs hp)).2).ne' (h.r_pos (hs hp) hp.2.1).ne'))

/-- The exact expansion integrating factor on every incoming off-axis segment.
Paper `e1a0fd5`, `eq:lambda-integrating-factor`, lines 422–428. -/
theorem cylinder_lambda_representation {u v : ℝ} (hp : (u, v) ∈ cylinderScalarRegion ui) :
    S.lam u v = Real.exp (∫ s in ui..u, cylinderKernel S s v) := by
  have hlog := h.log_lam_primitive hp.1 le_rfl (hp.2.1.trans_le hp.2.2) hp.2.1 hp.2.2
  have hinit := (h.initial_gauge v ⟨hp.1.trans hp.2.1.le, hp.2.2⟩).2
  have he := hlog.2
  dsimp only at he
  rw [hinit, Real.log_one, sub_zero] at he
  rw [← Real.exp_log (h.lam_pos (cylinderScalarRegion_subset ui hp)), he]
  rfl

end StandingFull

end AcExtensionPrinciple

end
