module

public import AcExtensionPrinciple.Cylinder.RectangleIntegral

/-!
# Continuous coefficients and the outgoing scalar transport

This module derives scalar regularity from the solution class.
Paper `e1a0fd5`, `eq:scalar-bound-linear-transport`
(lines 422–428), `eq:regular-axis-scalar-traces`, and lines 731–737.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- The regular off-axis domain, including the initial and terminal characteristic edges.
Paper `e1a0fd5`, `eq:past-triangle`, lines 422–428, 731–737. -/
@[expose] def cylinderScalarRegion (ui : ℝ) : Set (ℝ × ℝ) :=
  {p | ui ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ 0}

/-- The off-axis scalar domain is contained in the solution triangle.
Paper `e1a0fd5`, `eq:past-triangle`, lines 422–428. -/
theorem cylinderScalarRegion_subset (ui : ℝ) : cylinderScalarRegion ui ⊆ pastTriangle ui :=
  fun _ hp => ⟨hp.1, hp.2.1.trans_le hp.2.2, hp.2.1.le, hp.2.2⟩

/-- The scalar region is exactly the domain used by the axis trace conditions.
Paper `e1a0fd5`, `eq:regular-axis-scalar-traces`, line 259. -/
theorem cylinderScalarRegion_eq_axisComplement (ui : ℝ) :
    cylinderScalarRegion ui = pastTriangle ui \ axis ui := by
  ext p
  constructor
  · intro hp
    refine ⟨cylinderScalarRegion_subset ui hp, ?_⟩
    intro ha
    have he : p.2 = p.1 := ha.2.2
    linarith [hp.2.1]
  · rintro ⟨hp, ha⟩
    refine ⟨hp.1, lt_of_le_of_ne hp.2.2.1 ?_, hp.2.2.2⟩
    intro he
    exact ha ⟨hp.1, hp.2.1, he.symm⟩

/-- Closed incoming transport rectangles stay away from the axis.
Paper `e1a0fd5`, lines 394–428, 731–737. -/
theorem cylinder_rectangle_subset_region {ui U a b : ℝ} (hUa : U < a) (hb : b ≤ 0) :
    Icc ui U ×ˢ Icc a b ⊆ cylinderScalarRegion ui := by
  intro p hp
  exact ⟨hp.1.1, hp.1.2.trans_lt (hUa.trans_le hp.2.1), hp.2.2.trans hb⟩

/-- Continuous off-axis forcing has a continuous incoming primitive on the whole region.
Paper `e1a0fd5`, calculus for lines 422–428 and 731–737. -/
theorem cylinder_primitive_continuous_region {ui : ℝ} {F : ℝ → ℝ → ℝ}
    (hf : ContinuousOn (fun p => F p.1 p.2) (cylinderScalarRegion ui)) :
    ContinuousOn (fun p => ∫ s in ui..p.1, F s p.2) (cylinderScalarRegion ui) := by
  intro p hp
  let U := (p.1 + p.2) / 2
  let a := (U + p.2) / 2
  have huU : p.1 < U := by dsimp [U]; linarith [hp.2.1]
  have hUa : U < a := by dsimp [a, U]; linarith [hp.2.1]
  have hav : a < p.2 := by dsimp [a, U]; linarith [hp.2.1]
  have hc := cylinder_rectangle_primitive_continuous (F := F) (hp.1.trans huU.le)
    (hav.le.trans hp.2.2) (hf.mono (cylinder_rectangle_subset_region hUa le_rfl))
  apply (hc p ⟨⟨hp.1, huU.le⟩, ⟨hav.le, hp.2.2⟩⟩).mono_of_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin,
    ((continuous_fst.tendsto p).eventually (Iio_mem_nhds huU)).filter_mono nhdsWithin_le_nhds,
    ((continuous_snd.tendsto p).eventually (Ioi_mem_nhds hav)).filter_mono nhdsWithin_le_nhds]
    with q hq hqU hqa
  exact ⟨⟨hq.1, hqU.le⟩, ⟨hqa.le, hq.2.2⟩⟩

/-- Incoming logarithmic expansion coefficient γϰ, used by the linear transport formula.
Paper `e1a0fd5`, `eq:scalar-bound-linear-transport`, line 422. -/
@[expose] noncomputable def cylinderKernel (S : SSFields) (u v : ℝ) : ℝ :=
  S.gamma u v * S.varkappa u v

/-- The radius transport coefficient equals λγϰ with the shared field definitions.
Paper `e1a0fd5`, `eq:radius`, `eq:scalar-bound-linear-transport`, lines 422–428. -/
theorem cylinder_radiusCoeff_eq (S : SSFields) (u v : ℝ) :
    S.radiusCoeff u v = S.lam u v * cylinderKernel S u v := by
  simp only [SSFields.radiusCoeff, cylinderKernel, SSFields.gamma, SSFields.varkappa,
    gammaOf, varkappaOf, div_eq_mul_inv, mul_inv_rev]
  ring

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- μ is jointly continuous off-axis, including both characteristic edges.
Paper `e1a0fd5`, lines 422–428, 731–737. -/
theorem cylinder_mu_continuous :
    ContinuousOn (fun p => S.mu p.1 p.2) (cylinderScalarRegion ui) := by
  have hs := cylinderScalarRegion_subset ui
  exact (continuousOn_const.mul (h.regularCenter.continuous_m.mono hs)).div
    (h.regularCenter.continuous_r.mono hs)
    (fun p hp => (h.r_pos (hs hp) hp.2.1).ne')

/-- γϰ is jointly continuous off-axis. Paper `e1a0fd5`,
`eq:scalar-bound-linear-transport`, lines 422–428, 731–737. -/
theorem cylinder_kernel_continuous :
    ContinuousOn (fun p => cylinderKernel S p.1 p.2) (cylinderScalarRegion ui) := by
  have hs := cylinderScalarRegion_subset ui
  have hm := h.cylinder_mu_continuous
  exact ((h.regularCenter.continuous_nu.mono hs).div (continuousOn_const.sub hm)
    (fun p hp => (sub_pos.mpr (h.mu_bounds (hs hp)).2).ne')).mul
    (hm.div (h.regularCenter.continuous_r.mono hs)
      (fun p hp => (h.r_pos (hs hp) hp.2.1).ne'))

/-- The radius mixed-equation coefficient is jointly continuous off-axis.
Paper `e1a0fd5`, `eq:radius`, lines 422–428 and 731–737. -/
theorem cylinder_radiusCoeff_continuous :
    ContinuousOn (fun p => S.radiusCoeff p.1 p.2) (cylinderScalarRegion ui) := by
  have hc := (h.regularCenter.continuous_lam.mono (cylinderScalarRegion_subset ui)).mul
    h.cylinder_kernel_continuous
  convert hc using 1
  ext p
  simp only [cylinder_radiusCoeff_eq, Pi.mul_apply]

/-- The ψ mixed-equation forcing λγϰφ is jointly continuous off-axis.
Paper `e1a0fd5`, `eq:scalar-bound-linear-transport`, lines 422–428, 731–737. -/
theorem cylinder_forcing_continuous :
    ContinuousOn (fun p => S.radiusCoeff p.1 p.2 * S.phi p.1 p.2)
      (cylinderScalarRegion ui) := by
  have hs := cylinderScalarRegion_subset ui
  have hc := ((h.regularCenter.continuous_lam.mono hs).mul h.cylinder_kernel_continuous).mul
    (h.regularCenter.continuous_phi.mono hs)
  convert hc using 1
  ext p
  simp only [cylinder_radiusCoeff_eq, Pi.mul_apply]

/-- The exact incoming linear transport representation, recovered from the ψ primitive.
Paper `e1a0fd5`, `eq:scalar-bound-linear-transport`, lines 422–428. -/
theorem cylinder_dvpsi_representation {u v : ℝ} (hp : (u, v) ∈ cylinderScalarRegion ui) :
    S.dvpsi u v = S.dvpsi ui v +
      ∫ s in ui..u, S.radiusCoeff s v * S.phi s v := by
  have ht := h.regularCenter.localBV.dvpsi_in v ui u hp.1
    (inSeg_subset_offAxis le_rfl (hp.2.1.trans_le hp.2.2) hp.2.1 hp.2.2)
  linarith [ht.2]

/-- Joint continuity of ∂ᵥψ on each closed incoming transport rectangle.
Paper `e1a0fd5`, linear representation at lines 422–428. -/
theorem cylinder_dvpsi_continuous_rectangle {U a b : ℝ} (hU : ui ≤ U)
    (hUa : U < a) (hab : a ≤ b) (hb : b ≤ 0) :
    ContinuousOn (fun p => S.dvpsi p.1 p.2) (Icc ui U ×ˢ Icc a b) := by
  have hs := cylinder_rectangle_subset_region (ui := ui) hUa hb
  have hcJ := cylinder_rectangle_primitive_continuous
    (F := fun u v => S.radiusCoeff u v * S.phi u v) hU hab
    (h.cylinder_forcing_continuous.mono hs)
  have hcD : ContinuousOn (fun p : ℝ × ℝ => S.dvpsi ui p.2) (Icc ui U ×ˢ Icc a b) :=
    h.initial_ac_data.continuousOn.comp continuous_snd.continuousOn
    (fun p hp => by
      rw [uIcc_of_le h.initial_negative.le]
      exact ⟨hU.trans (hUa.le.trans hp.2.1), hp.2.2.trans hb⟩)
  apply (hcD.add hcJ).congr
  intro p hp
  exact h.cylinder_dvpsi_representation (hs hp)

/-- ∂ᵥψ is jointly continuous on the whole regular off-axis domain.
Paper `e1a0fd5`, lines 422–428 and 731–737. -/
theorem cylinder_dvpsi_continuous :
    ContinuousOn (fun p => S.dvpsi p.1 p.2) (cylinderScalarRegion ui) := by
  intro p hp
  let U := (p.1 + p.2) / 2
  let a := (U + p.2) / 2
  have huU : p.1 < U := by dsimp [U]; linarith [hp.2.1]
  have hUa : U < a := by dsimp [a, U]; linarith [hp.2.1]
  have hav : a < p.2 := by dsimp [a, U]; linarith [hp.2.1]
  have hc := h.cylinder_dvpsi_continuous_rectangle (hp.1.trans huU.le) hUa
    (hav.le.trans hp.2.2) le_rfl
  apply (hc p ⟨⟨hp.1, huU.le⟩, ⟨hav.le, hp.2.2⟩⟩).mono_of_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin,
    ((continuous_fst.tendsto p).eventually (Iio_mem_nhds huU)).filter_mono nhdsWithin_le_nhds,
    ((continuous_snd.tendsto p).eventually (Ioi_mem_nhds hav)).filter_mono nhdsWithin_le_nhds]
      with q hq hqU hqa
  exact ⟨⟨hq.1, hqU.le⟩, ⟨hqa.le, hq.2.2⟩⟩

/-- The outgoing scalar derivative is jointly continuous off-axis.
Paper `e1a0fd5`, lines 422–428 and 731–737. -/
theorem cylinder_dvphi_continuous :
    ContinuousOn (fun p => S.dvphi p.1 p.2) (cylinderScalarRegion ui) := by
  have hs := cylinderScalarRegion_subset ui
  exact (h.cylinder_dvpsi_continuous.sub
    ((h.regularCenter.continuous_lam.mono hs).mul (h.regularCenter.continuous_phi.mono hs))).div
    (h.regularCenter.continuous_r.mono hs)
    (fun p hp => (h.r_pos (hs hp) hp.2.1).ne')

/-- The unnormalized incoming ψ derivative has the continuous regular-axis trace νφ.
Paper `e1a0fd5`, `eq:regular-axis-scalar-traces`, line 259. -/
theorem cylinder_dupsi_axis_tendsto {a : ℝ} (ha : (a, a) ∈ axis ui) :
    Tendsto (fun p => S.dupsi p.1 p.2) (𝓝[cylinderScalarRegion ui] (a, a))
      (𝓝 (S.nu a a * S.phi a a)) := by
  have hq := h.regularCenter.axis_dupsi_trace a ha
  rw [← cylinderScalarRegion_eq_axisComplement] at hq
  have hn := (h.regularCenter.continuous_nu (a, a) (axis_subset_pastTriangle ui ha)).mono
    (cylinderScalarRegion_subset ui)
  have ht := hq.mul hn
  rw [mul_comm (S.phi a a) (S.nu a a)] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with p hp
  exact div_mul_cancel₀ _ (h.nu_neg (cylinderScalarRegion_subset ui hp)).ne

end StandingFull

end AcExtensionPrinciple

end
