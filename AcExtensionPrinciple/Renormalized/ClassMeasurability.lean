module

public import AcExtensionPrinciple.Renormalized.ClassDatumInputs
public import AcExtensionPrinciple.Renormalized.ClassEnergy

/-!
# Measurability of all Section 3 cone integrands

Paper `e1a0fd5`, `equations.tex` lines 1069–1124.
Measurability is recovered from continuous class fields, characteristic
primitives, and the a.e. radial derivative specified by Lemma 2.2.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The incoming scalar-product derivative is continuous off the axis on
an outgoing cone, including its terminal endpoint. Paper `e1a0fd5`,
lines 222 and 1069. -/
theorem dupsi_continuousOn_cone {u : ℝ} (hu : ui ≤ u) (hu0 : u < 0) :
    ContinuousOn (S.dupsi u) (Ioc u 0) := by
  intro v hv
  let a := (u + v) / 2
  have hua : u < a := by dsimp [a]; linarith [hv.1]
  have hav : a < v := by dsimp [a]; linarith [hv.1]
  have ha0 : a ≤ 0 := hav.le.trans hv.2
  have hac := intervalPrimitive_ac ha0 (fun x hx =>
    h.regularCenter.localBV.dupsi_out u a x hx.1
      (outSeg_subset_offAxis hu hu0 hua hx.2))
  have hc : ContinuousOn (S.dupsi u) (Icc a 0) := by
    simpa only [uIcc_of_le ha0] using hac.continuousOn
  apply (hc v ⟨hav.le, hv.2⟩).mono_of_mem_nhdsWithin
  filter_upwards [eventually_mem_nhdsWithin,
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (Ioi_mem_nhds hav)] with x hx hax
  exact ⟨hax.le, hx.2⟩

/-- All primitive fields needed in cone integrands are a.e. strongly
measurable. Paper `e1a0fd5`, lines 1069–1124. -/
theorem cone_primitive_fields_measurable {u : ℝ} (hu : ui ≤ u) (hu0 : u < 0) :
    AEStronglyMeasurable (S.r u) (volume.restrict (Ioc u 0)) ∧
    AEStronglyMeasurable (S.lam u) (volume.restrict (Ioc u 0)) ∧
    AEStronglyMeasurable (S.nu u) (volume.restrict (Ioc u 0)) ∧
    AEStronglyMeasurable (S.m u) (volume.restrict (Ioc u 0)) ∧
    AEStronglyMeasurable (S.phi u) (volume.restrict (Ioc u 0)) ∧
    AEStronglyMeasurable (S.dupsi u) (volume.restrict (Ioc u 0)) := by
  have hm {f : ℝ → ℝ → ℝ}
      (hf : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) (pastTriangle ui)) :
      AEStronglyMeasurable (f u) (volume.restrict (Ioc u 0)) :=
    ((continuous_out hf (outSeg_subset_triangle hu hu0 le_rfl le_rfl)).mono
      Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  exact ⟨hm h.regularCenter.continuous_r, hm h.regularCenter.continuous_lam,
    hm h.regularCenter.continuous_nu, hm h.regularCenter.continuous_m,
    hm h.regularCenter.continuous_phi,
    (h.dupsi_continuousOn_cone hu hu0).aestronglyMeasurable measurableSet_Ioc⟩

/-- The geometric mass ratio and κ are measurable on every proper cone.
Paper `e1a0fd5`, lines 1069–1124. -/
theorem cone_geometric_fields_measurable {u : ℝ} (hu : ui ≤ u) (hu0 : u < 0) :
    AEStronglyMeasurable (S.mu u) (volume.restrict (Ioc u 0)) ∧
    AEStronglyMeasurable (S.kappa u) (volume.restrict (Ioc u 0)) := by
  obtain ⟨hr, hl, _, hm, _, _⟩ := h.cone_primitive_fields_measurable hu hu0
  have hmu : AEStronglyMeasurable (S.mu u) (volume.restrict (Ioc u 0)) :=
    (hm.const_mul 2).div₀ hr
  exact ⟨hmu, hl.div₀ (aestronglyMeasurable_const.sub hmu)⟩

end StandingFull

namespace SectionThreeDatumInputs

variable {ui : ℝ} {S : SSFields} {q : ℝ → ℝ → ℝ}
    (D : SectionThreeDatumInputs ui S q) (h : StandingFull ui S)
include D h

/-- The prescribed a.e. radial derivative is measurable on every cone.
Paper `e1a0fd5`, `eq:radial-datum-derivative`, lines 555–558 and 1069. -/
theorem q_measurable {u : ℝ} (hu : ui ≤ u) (hu0 : u < 0) :
    AEStronglyMeasurable (q u) (volume.restrict (Ioc u 0)) := by
  have hl := (h.cone_primitive_fields_measurable hu hu0).2.1
  have hd : AEStronglyMeasurable (deriv (S.outgoingDatum u)) (volume.restrict (Ioc u 0)) :=
    (measurable_deriv _).aestronglyMeasurable
  exact (hd.div₀ hl).congr (D.radial_eq u hu hu0).symm

/-- Both scalar derivative fields are measurable from class fields and
the outgoing AC datum. Paper `e1a0fd5`, lines 1069–1124. -/
theorem scalar_derivatives_measurable {u : ℝ} (hu : ui ≤ u) (hu0 : u < 0) :
    AEStronglyMeasurable (S.dvphi u) (volume.restrict (Ioc u 0)) ∧
    AEStronglyMeasurable (S.duphi u) (volume.restrict (Ioc u 0)) := by
  obtain ⟨hr, hl, hn, _, hphi, hdupsi⟩ := h.cone_primitive_fields_measurable hu hu0
  have hPc : ContinuousOn (S.outgoingDatum u) (Ioc u 0) :=
    (D.outgoing_ac u hu hu0).continuousOn.mono
      (by rw [uIcc_of_le hu0.le]; exact Ioc_subset_Icc_self)
  have hP : AEStronglyMeasurable (S.outgoingDatum u) (volume.restrict (Ioc u 0)) :=
    hPc.aestronglyMeasurable measurableSet_Ioc
  have hdvpsi : AEStronglyMeasurable (S.dvpsi u) (volume.restrict (Ioc u 0)) := by
    apply (hl.mul hP).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    dsimp [SSFields.outgoingDatum]
    exact mul_div_cancel₀ _ (ne_of_gt (h.lam_pos (p := (u, v)) ⟨hu, hu0, hv.1.le, hv.2⟩))
  exact ⟨(hdvpsi.sub (hl.mul hphi)).div₀ hr, (hdupsi.sub (hn.mul hphi)).div₀ hr⟩

/-- The renormalized derivative and interaction are measurable on every
proper cone. Paper `e1a0fd5`, lines 1069–1078. -/
theorem renormalized_fields_measurable {u : ℝ} (hu : ui ≤ u) (hu0 : u < 0) :
    AEStronglyMeasurable (S.renormalizedDerivative q u) (volume.restrict (Ioc u 0)) ∧
    AEStronglyMeasurable (S.renormalizedInteraction u) (volume.restrict (Ioc u 0)) := by
  obtain ⟨hr, hl, hn, _, _, _⟩ := h.cone_primitive_fields_measurable hu hu0
  have hmu := (h.cone_geometric_fields_measurable hu hu0).1
  obtain ⟨hv, hu'⟩ := D.scalar_derivatives_measurable h hu hu0
  have hA := (hr.div₀ hl).mul hv
  have hB := (hr.div₀ hn).mul hu'
  have hgap : AEStronglyMeasurable (fun v => 1 - S.mu u v) (volume.restrict (Ioc u 0)) :=
    aestronglyMeasurable_const.sub hmu
  exact ⟨(hgap.mul hl).mul ((D.q_measurable h hu hu0).sub ((hA.pow 3).div₀ hr)),
    hmu.add ((hgap.mul hA).mul hB)⟩

/-- Measurability of the transported initial datum, remainder, and weighted
energy is discharged from the explicit splitting. Paper `e1a0fd5`,
`eq:renormalized-splitting`, `eq:renormalized-initial-energy`, lines 1088–1124. -/
theorem splitting_fields_measurable {u : ℝ} (hu : ui ≤ u) (hu0 : u < 0) :
    AEStronglyMeasurable (S.renormalizedInitial q ui u) (volume.restrict (Ioc u 0)) ∧
    AEStronglyMeasurable (S.renormalizedRemainder q ui u) (volume.restrict (Ioc u 0)) ∧
    AEStronglyMeasurable (S.renormalizedRemainderEnergy q ui u) (volume.restrict (Ioc u 0)) := by
  have hsub : Ioc u 0 ⊆ Ioc ui 0 := Ioc_subset_Ioc_left hu
  have hki := AEStronglyMeasurable.mono_set hsub
    (h.cone_geometric_fields_measurable le_rfl h.initial_negative).2
  have hji := AEStronglyMeasurable.mono_set hsub
    (D.renormalized_fields_measurable h le_rfl h.initial_negative).1
  have hk := (h.cone_geometric_fields_measurable hu hu0).2
  have hinit : AEStronglyMeasurable (S.renormalizedInitial q ui u) (volume.restrict (Ioc u 0)) :=
    (hki.div₀ hk).mul hji
  have hrem : AEStronglyMeasurable (S.renormalizedRemainder q ui u) (volume.restrict (Ioc u 0)) :=
    (D.renormalized_fields_measurable h hu hu0).1.sub hinit
  have hr := (h.cone_primitive_fields_measurable hu hu0).1
  have hl := (h.cone_primitive_fields_measurable hu hu0).2.1
  have hmu := (h.cone_geometric_fields_measurable hu hu0).1
  exact ⟨hinit, hrem, (hr.mul (hrem.pow 2)).div₀
    ((aestronglyMeasurable_const.sub hmu).pow 2 |>.mul hl)⟩

end SectionThreeDatumInputs

end AcExtensionPrinciple

end
