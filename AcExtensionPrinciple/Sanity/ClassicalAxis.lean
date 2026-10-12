module

public import AcExtensionPrinciple.Sanity.ClassicalPrimitives
public import AcExtensionPrinciple.Gauge.Primitive
public import AcExtensionPrinciple.GeometricBounds.RayBounds

/-!
# Classical scalar values at the regular axis
Paper `e1a0fd5`, `eq:regular-axis`, `eq:regular-axis-scalar-traces`, lines 220–275;
Christodoulou CPAM p. 1157. Endpoint FTC and the product rule determine the stored values.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

namespace ClassicalTriangleSolution

variable {ui : ℝ} {S : SSFields} (h : ClassicalTriangleSolution ui S)
include h

/-- Outgoing scalar derivatives have the prescribed axis values.
Paper `e1a0fd5`, `eq:regular-axis-scalar-traces`, line 259. -/
theorem dvpsi_axis {a : ℝ} (ha : (a, a) ∈ AcExtensionPrinciple.axis ui) :
    S.dvpsi a a = S.lam a a * S.phi a a := by
  have hs := outSeg_subset_triangle ha.1 ha.2.1 le_rfl le_rfl
  have hsc := hs.trans (classical_past_subset_closed ui)
  have hc := fun y (hy : y ∈ Icc a 0) =>
    outSeg_subset_triangle ha.1 ha.2.1 le_rfl hy.2
  have hr := hasDerivWithinAt_of_intervalPrimitives
    (fun y hy => h.radius_out hy.1 (hc y hy))
    (StandingFull.continuous_out
      (h.c1_lam.continuousOn.mono (classical_past_subset_closed ui)) hs)
    (left_mem_Icc.mpr ha.2.1.le)
  have hp := hasDerivWithinAt_of_intervalPrimitives
    (fun y hy => h.psi_out hy.1 (hc y hy))
    (StandingFull.continuous_out
      (h.c1_dvpsi.continuousOn.mono (classical_past_subset_closed ui)) hs)
    (left_mem_Icc.mpr ha.2.1.le)
  have hf : ContDiffOn ℝ 1 (fun v => S.phi a v) (Icc a 0) :=
    h.c1_phi.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun v hv => hsc ⟨mem_singleton a, hv⟩)
  have hφ := (hf.differentiableOn (by decide) a
    (left_mem_Icc.mpr ha.2.1.le)).hasDerivWithinAt
  have he := UniqueDiffWithinAt.eq_deriv (Icc a 0)
    (uniqueDiffOn_Icc ha.2.1 a (left_mem_Icc.mpr ha.2.1.le)) hp (hr.mul hφ)
  simpa [(h.axis a ha.1 ha.2.1.le).1] using he

/-- Incoming scalar derivative values at every axis point above the initial corner.
Paper `e1a0fd5`, `eq:regular-axis-scalar-traces`, line 259. -/
theorem dupsi_axis_interior {a : ℝ} (ha : (a, a) ∈ AcExtensionPrinciple.axis ui) (hia : ui < a) :
    S.dupsi a a = S.nu a a * S.phi a a := by
  have hs := inSeg_subset_triangle (ui := ui) le_rfl ha.2.1 le_rfl ha.2.1.le
  have hsc := hs.trans (classical_past_subset_closed ui)
  have hc := fun y (hy : y ∈ Icc ui a) =>
    inSeg_subset_triangle (ui := ui) le_rfl (hy.2.trans_lt ha.2.1) hy.2 ha.2.1.le
  have hr := hasDerivWithinAt_of_intervalPrimitives
    (fun y hy => h.radius_in hy.1 (hc y hy))
    (StandingFull.continuous_in
      (h.c1_nu.continuousOn.mono (classical_past_subset_closed ui)) hs)
    (right_mem_Icc.mpr ha.1)
  have hp := hasDerivWithinAt_of_intervalPrimitives
    (fun y hy => h.psi_in hy.1 (hc y hy))
    (StandingFull.continuous_in
      (h.c1_dupsi.continuousOn.mono (classical_past_subset_closed ui)) hs)
    (right_mem_Icc.mpr ha.1)
  have hf : ContDiffOn ℝ 1 (fun u => S.phi u a) (Icc ui a) :=
    h.c1_phi.comp (contDiff_id.prodMk contDiff_const).contDiffOn
      (fun u hu => hsc ⟨hu, mem_singleton a⟩)
  have hφ := (hf.differentiableOn (by decide) a (right_mem_Icc.mpr ha.1)).hasDerivWithinAt
  have he := UniqueDiffWithinAt.eq_deriv (Icc ui a)
    (uniqueDiffOn_Icc hia a (right_mem_Icc.mpr ha.1)) hp (hr.mul hφ)
  simpa [(h.axis a ha.1 ha.2.1.le).1] using he

/-- Continuity supplies the incoming scalar value also at the initial axis corner.
Paper `e1a0fd5`, `eq:regular-axis-scalar-traces`, line 259. -/
theorem dupsi_axis {a : ℝ} (ha : (a, a) ∈ AcExtensionPrinciple.axis ui) :
    S.dupsi a a = S.nu a a * S.phi a a := by
  rcases ha.1.eq_or_lt with he | he
  · change ui = a at he
    subst a
    have hm : ∀ x ∈ Icc ui 0, (x, x) ∈ closedTriangle ui :=
      fun x hx => ⟨hx.1, le_rfl, hx.2⟩
    have hp := h.c1_dupsi.continuousOn.comp
      (continuous_id.prodMk continuous_id).continuousOn hm
    have hn := h.c1_nu.continuousOn.comp
      (continuous_id.prodMk continuous_id).continuousOn hm
    have hφ := h.c1_phi.continuousOn.comp
      (continuous_id.prodMk continuous_id).continuousOn hm
    have hh : EqOn (fun x => S.dupsi x x) (fun x => S.nu x x * S.phi x x) (Ioo ui 0) :=
      fun x hx => h.dupsi_axis_interior ⟨hx.1.le, hx.2, rfl⟩ hx.1
    exact hh.of_subset_closure hp (hn.mul hφ) Ioo_subset_Icc_self
      (by rw [closure_Ioo h.initial_negative.ne])
      (left_mem_Icc.mpr h.initial_negative.le)
  · exact h.dupsi_axis_interior ha he

omit h in
/-- A continuous field on the triangle has the ordinary outgoing axis limit.
Paper `e1a0fd5`, `eq:regular-axis`, lines 222–259. -/
theorem axis_outgoing_limit {f : ℝ × ℝ → ℝ}
    (hf : ContinuousOn f (closedTriangle ui)) {a : ℝ} (ha : (a, a) ∈ AcExtensionPrinciple.axis ui) :
    Tendsto (fun ε => f (a, a + ε)) (𝓝[>] 0) (𝓝 (f (a, a))) := by
  have hc : Tendsto f (𝓝[closedTriangle ui] (a, a)) (𝓝 (f (a, a))) :=
    hf (a, a) ⟨ha.1, le_rfl, ha.2.1.le⟩
  apply hc.comp
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_, ?_⟩
  · have ht : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 (0 : ℝ)) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [add_zero] using (tendsto_const_nhds (x := a)).prodMk_nhds
      ((tendsto_const_nhds (x := a)).add ht)
  · filter_upwards [self_mem_nhdsWithin,
      (tendsto_id.mono_left nhdsWithin_le_nhds).eventually
        (Iio_mem_nhds (neg_pos.mpr ha.2.1))] with ε hε hεa
    change ui ≤ a ∧ a ≤ a + ε ∧ a + ε ≤ 0
    change 0 < ε at hε
    change ε < -a at hεa
    exact ⟨ha.1, by linarith, by linarith⟩

end ClassicalTriangleSolution

end AcExtensionPrinciple

end
