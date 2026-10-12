module

public import AcExtensionPrinciple.Cylinder.ClassEnergy

/-!
# Regularity of the logarithmic incoming-expansion coefficient

Paper `e1a0fd5`, `eq:logarithmic-expansions`, and lines 1460–1473.
The coefficient ν_v/ν contains only r, m, λ. Its incoming derivative
therefore needs no derivative of the original outgoing gauge ν.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory

/-- The outgoing logarithmic ν coefficient, after canceling ν. Paper
`e1a0fd5`, `eq:logarithmic-expansions`, lines 1460–1473. -/
@[expose] noncomputable def chartNuCoefficient (S : SSFields) (u v : ℝ) : ℝ :=
  S.mu u v * S.lam u v / ((1 - S.mu u v) * S.r u v)

/-- The incoming mass-ratio coefficient. Paper `e1a0fd5`,
`eq:mass`, lines 1460–1473 (coordinate regularity). -/
@[expose] noncomputable def chartMuU (S : SSFields) (u v : ℝ) : ℝ :=
  (2 * S.massU u v * S.r u v - 2 * S.m u v * S.nu u v) / S.r u v ^ 2

/-- Incoming derivative of the logarithmic ν coefficient. Paper
`e1a0fd5`, `eq:logarithmic-expansions`, lines 1460–1473. -/
@[expose] noncomputable def chartNuCoefficientU (S : SSFields) (u v : ℝ) : ℝ :=
  ((chartMuU S u v * S.lam u v + S.mu u v * S.radiusCoeff u v) *
      ((1 - S.mu u v) * S.r u v) - (S.mu u v * S.lam u v) *
      ((-chartMuU S u v) * S.r u v + (1 - S.mu u v) * S.nu u v)) /
    ((1 - S.mu u v) * S.r u v) ^ 2

/-- The coefficient is the one in the source logarithmic primitive.
Paper `e1a0fd5`, `eq:logarithmic-expansions`, lines 1460–1473. -/
theorem chartNuCoefficient_eq (S : SSFields) (u v : ℝ) :
    chartNuCoefficient S u v = S.kappa u v * S.varkappa u v := by
  simp only [chartNuCoefficient, SSFields.kappa, SSFields.varkappa, kappaOf, varkappaOf,
    div_eq_mul_inv, mul_inv_rev]
  ring

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Incoming radius, mass and expansion derivatives remain valid on the
terminal ray v=0. Paper `e1a0fd5`, `eq:radius`, `eq:mass`, lines 1460–1473. -/
theorem chart_incoming_closed_partials {u v : ℝ}
    (hp : (u, v) ∈ cylinderScalarRegion ui) (hu : ui < u) :
    HasDerivAt (fun x => S.r x v) (S.nu u v) u ∧
      HasDerivAt (fun x => S.m x v) (S.massU u v) u ∧
      HasDerivAt (fun x => S.lam x v) (S.radiusCoeff u v) u := by
  let d := (u + v) / 2
  have hud : u < d := by dsimp [d]; linarith [hp.2.1]
  have hdv : d < v := by dsimp [d]; linarith [hp.2.1]
  have hmap : MapsTo (fun x : ℝ => (x, v)) (Icc ui d) (cylinderScalarRegion ui) :=
    fun x hx => ⟨hx.1, hx.2.trans_lt hdv, hp.2.2⟩
  have hc : ContinuousOn (fun x : ℝ => (x, v)) (Icc ui d) :=
    (continuous_id.prodMk continuous_const).continuousOn
  have hseg {x : ℝ} (hx : x ∈ Icc ui d) :
      inSeg v ui x ⊆ offAxis (pastTriangle ui) :=
    inSeg_subset_offAxis le_rfl (hx.2.trans_lt (hdv.trans_le hp.2.2))
      (hx.2.trans_lt hdv) hp.2.2
  refine ⟨intervalPrimitive_hasDerivAt ⟨hu, hud⟩
    (h.regularCenter.continuous_nu.comp hc
      (fun _ hx => cylinderScalarRegion_subset ui (hmap hx)))
    (fun x hx => h.regularCenter.localBV.radius_in v ui x hx.1
      (fun p hp => (hseg hx hp).1)), ?_, ?_⟩
  · exact intervalPrimitive_hasDerivAt ⟨hu, hud⟩
      (h.cylinder_massU_continuous.comp hc hmap)
      (fun x hx => h.regularCenter.localBV.mass_in v ui x hx.1
        (fun p hp => (hseg hx hp).1))
  · exact intervalPrimitive_hasDerivAt ⟨hu, hud⟩
      (h.cylinder_radiusCoeff_continuous.comp hc hmap)
      (fun x hx => h.regularCenter.localBV.lam_in v ui x hx.1 (hseg hx))

/-- The incoming derivative of μ uses only continuous physical fields.
Paper `e1a0fd5`, `eq:mass`, lines 1460–1473. -/
theorem chart_mu_hasDerivAt_in {u v : ℝ}
    (hp : (u, v) ∈ cylinderScalarRegion ui) (hu : ui < u) :
    HasDerivAt (fun x => S.mu x v) (chartMuU S u v) u := by
  have hd := h.chart_incoming_closed_partials hp hu
  have hr := (h.r_pos (cylinderScalarRegion_subset ui hp) hp.2.1).ne'
  convert (hd.2.1.const_mul 2).div hd.1 hr using 1 <;> (try ext x) <;>
    simp only [SSFields.mu, massRatio, chartMuU, Pi.div_apply]

/-- Differentiability of ν_v/ν in the incoming parameter, also at v=0.
Paper `e1a0fd5`, `eq:logarithmic-expansions`, lines 1460–1473. -/
theorem chart_nuCoefficient_hasDerivAt_in {u v : ℝ}
    (hp : (u, v) ∈ cylinderScalarRegion ui) (hu : ui < u) :
    HasDerivAt (fun x => chartNuCoefficient S x v) (chartNuCoefficientU S u v) u := by
  have hd := h.chart_incoming_closed_partials hp hu
  have hm := h.chart_mu_hasDerivAt_in hp hu
  have hpt := cylinderScalarRegion_subset ui hp
  have hden : (1 - S.mu u v) * S.r u v ≠ 0 :=
    (mul_pos (sub_pos.mpr (h.mu_bounds hpt).2) (h.r_pos hpt hp.2.1)).ne'
  convert (hm.mul hd.2.2).div (((hasDerivAt_const u 1).sub hm).mul hd.1) hden using 1 <;>
    (try ext x) <;>
    simp only [chartNuCoefficient, chartNuCoefficientU, zero_sub, Pi.div_apply,
      Pi.mul_apply, Pi.sub_apply]

/-- The logarithmic coefficient is continuous on the closed off-axis
region. Paper `e1a0fd5`, `eq:logarithmic-expansions`, lines 1460–1473. -/
theorem chart_nuCoefficient_continuous :
    ContinuousOn (fun p => chartNuCoefficient S p.1 p.2) (cylinderScalarRegion ui) := by
  have hs := cylinderScalarRegion_subset ui
  have hm := h.cylinder_mu_continuous
  exact (hm.mul (h.regularCenter.continuous_lam.mono hs)).div
    ((continuousOn_const.sub hm).mul (h.regularCenter.continuous_r.mono hs))
    (fun p hp => (mul_pos (sub_pos.mpr (h.mu_bounds (hs hp)).2)
      (h.r_pos (hs hp) hp.2.1)).ne')

/-- The incoming coefficient derivative is continuous; no ν_u premise
is introduced. Paper `e1a0fd5`, `eq:logarithmic-expansions`, lines 1460–1473. -/
theorem chart_nuCoefficientU_continuous :
    ContinuousOn (fun p => chartNuCoefficientU S p.1 p.2) (cylinderScalarRegion ui) := by
  have hs := cylinderScalarRegion_subset ui
  have hr := h.regularCenter.continuous_r.mono hs
  have hn := h.regularCenter.continuous_nu.mono hs
  have hl := h.regularCenter.continuous_lam.mono hs
  have hmass := h.regularCenter.continuous_m.mono hs
  have hm := h.cylinder_mu_continuous
  have hmuU : ContinuousOn (fun p => chartMuU S p.1 p.2) (cylinderScalarRegion ui) :=
    (((continuousOn_const.mul h.cylinder_massU_continuous).mul hr).sub
      ((continuousOn_const.mul hmass).mul hn)).div (hr.pow 2)
        (fun p hp => pow_ne_zero 2 (h.r_pos (hs hp) hp.2.1).ne')
  have hden : ContinuousOn (fun p => (1 - S.mu p.1 p.2) * S.r p.1 p.2)
      (cylinderScalarRegion ui) := (continuousOn_const.sub hm).mul hr
  exact (((hmuU.mul hl).add (hm.mul h.cylinder_radiusCoeff_continuous)).mul hden |>.sub
    ((hm.mul hl).mul ((hmuU.neg.mul hr).add ((continuousOn_const.sub hm).mul hn)))).div
      (hden.pow 2) (fun p hp => pow_ne_zero 2
        (mul_pos (sub_pos.mpr (h.mu_bounds (hs hp)).2) (h.r_pos (hs hp) hp.2.1)).ne')

end StandingFull

end AcExtensionPrinciple

end
