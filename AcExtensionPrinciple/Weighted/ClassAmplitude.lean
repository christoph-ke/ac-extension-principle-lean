module

public import AcExtensionPrinciple.Weighted.ClassChart

/-!
# Measurable cone coefficients

Paper `e1a0fd5`, `eq:weighted-radial-operator`,
`equations.tex` lines 1155–1158 and 1204–1215. The scalar coefficient
is the actual incoming amplitude, not an externally supplied function.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory Filter
open scoped Topology

/-- Extend a continuous function on an open interval measurably, keeping
the prescribed terminal value. Paper `e1a0fd5`, lines 1204–1215. -/
theorem exists_measurable_Ioc_extension {f : ℝ → ℝ} {u : ℝ}
    (hf : ContinuousOn f (Ioo u 0)) :
    ∃ F : ℝ → ℝ, Measurable F ∧ EqOn f F (Ioc u 0) := by
  classical
  let F₀ := (Ioo u 0).piecewise f (fun _ => 0)
  have hm : Measurable F₀ := hf.measurable_piecewise continuousOn_const measurableSet_Ioo
  let F := fun v => if v = 0 then f 0 else F₀ v
  refine ⟨F, Measurable.ite (measurableSet_singleton 0) measurable_const hm, ?_⟩
  intro v hv
  by_cases hv0 : v = 0
  · simp [F, hv0]
  · have hv' : v ∈ Ioo u 0 := ⟨hv.1, lt_of_le_of_ne hv.2 hv0⟩
    simp [F, F₀, hv0, hv']

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The incoming amplitude is continuous at each strictly interior point of
an outgoing cone. Paper `e1a0fd5`, `eq:weighted-radial-operator`, line 1158. -/
theorem weightedIncomingAmplitude_continuousOn {u : ℝ} (hu : ui ≤ u) (hu0 : u < 0) :
    ContinuousOn (weightedIncomingAmplitude S u) (Ioo u 0) := by
  intro v hv
  let a := (u + v) / 2
  have hua : u < a := by dsimp [a]; linarith [hv.1]
  have hav : a < v := by dsimp [a]; linarith [hv.1]
  have hdu : AbsolutelyContinuousOnInterval (S.dupsi u) a 0 := by
    apply intervalPrimitive_ac (g := fun s => S.radiusCoeff u s * S.phi u s)
      (hav.le.trans hv.2.le)
    intro x hx
    exact h.regularCenter.localBV.dupsi_out u a x hx.1
      (outSeg_subset_offAxis hu hu0 hua hx.2)
  have hdc : ContinuousOn (S.dupsi u) (Icc a 0) := by
    simpa only [uIcc_of_le (hav.le.trans hv.2.le)] using hdu.continuousOn
  have hd := hdc.continuousAt (Icc_mem_nhds hav hv.2)
  have hs := outSeg_subset_triangle hu hu0 hua.le le_rfl
  have hn := (continuous_out h.regularCenter.continuous_nu hs).continuousAt
    (Icc_mem_nhds hav hv.2)
  have hphi := (continuous_out h.regularCenter.continuous_phi hs).continuousAt
    (Icc_mem_nhds hav hv.2)
  have heq : (fun s => S.dupsi u s / S.nu u s - S.phi u s) =ᶠ[𝓝 v]
      weightedIncomingAmplitude S u := by
    filter_upwards [Ioo_mem_nhds hv.1 hv.2] with s hs'
    have hr := (h.r_pos ⟨hu, hu0, hs'.1.le, hs'.2.le⟩ hs'.1).ne'
    have hn0 := (h.nu_neg (p := (u, s)) ⟨hu, hu0, hs'.1.le, hs'.2.le⟩).ne
    unfold weightedIncomingAmplitude SSFields.duphi SSFields.zeta
    field_simp [hr, hn0]
  exact ((hd.div hn (h.nu_neg (p := (u, v))
    ⟨hu, hu0, hv.1.le, hv.2.le⟩).ne).sub hphi).congr heq |>.continuousWithinAt

/-- A measurable representative of the actual incoming amplitude on a cone.
Paper `e1a0fd5`, `eq:weighted-radial-operator`, lines 1155–1158. -/
theorem weighted_exists_measurable_amplitude {u : ℝ} (hu : ui ≤ u) (hu0 : u < 0) :
    ∃ A : ℝ → ℝ, Measurable A ∧ EqOn (weightedIncomingAmplitude S u) A (Ioc u 0) :=
  exists_measurable_Ioc_extension (h.weightedIncomingAmplitude_continuousOn hu hu0)

end StandingFull

end AcExtensionPrinciple

end
