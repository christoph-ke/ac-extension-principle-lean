module

public import AcExtensionPrinciple.Renormalized.ClassL1

/-!
# Extending the weighted interaction primitive to the regular axis

Paper `e1a0fd5`, `equations.tex` lines 1038–1078.
The endpoint passage requires a genuine integrable majorant, rather than
using the default value of an undefined Bochner integral.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- Local primitives with an integrable derivative extend from a zero axis
trace. Paper `e1a0fd5`, `eq:renormalized-radial-primitive`, line 1078. -/
theorem primitive_from_zero_axis_trace {F g : ℝ → ℝ} {u v : ℝ}
    (huv : u < v) (hg : IntervalIntegrable g volume u v)
    (hF : Tendsto F (𝓝[Ioo u v] u) (𝓝 0))
    (hlocal : ∀ a ∈ Ioo u v, IntervalPrimitive F g a v) :
    F v = ∫ s in u..v, g s := by
  have hn : (𝓝[Ioo u v] u).NeBot := mem_closure_iff_nhdsWithin_neBot.mp
    (by rw [closure_Ioo huv.ne]; exact left_mem_Icc.mpr huv.le)
  let G (a : ℝ) := ∫ s in u..a, g s
  have hG := hg.absolutelyContinuousOnInterval_intervalIntegral (c := u) (by simp)
  have hc : ContinuousOn G (Icc u v) := by simpa only [uIcc_of_le huv.le] using hG.continuousOn
  have ht := (hc u ⟨le_rfl, huv.le⟩).mono Ioo_subset_Icc_self
  have he : (fun a => F v - F a) =ᶠ[𝓝[Ioo u v] u] (fun a => G v - G a) := by
    filter_upwards [eventually_mem_nhdsWithin] with a ha
    have hsub : uIcc u a ⊆ uIcc u v := by
      rw [uIcc_of_le ha.1.le, uIcc_of_le huv.le]
      exact Icc_subset_Icc_right ha.2.le
    have hsum := intervalIntegral.integral_add_adjacent_intervals
      (hg.mono_set hsub) (hlocal a ha).1
    rw [(hlocal a ha).2]
    dsimp [G]
    linarith
  have hlim := tendsto_nhds_unique (tendsto_const_nhds.sub hF)
    ((tendsto_const_nhds.sub ht).congr' he.symm)
  simpa [G] using hlim

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The weighted interaction is an off-axis primitive of `r B j`.
Paper `e1a0fd5`, `eq:renormalized-radial-primitive`, line 1078. -/
theorem radius_interaction_primitive_of_ac_datum {q : ℝ → ℝ → ℝ} {u a b : ℝ}
    (hab : a ≤ b) (hu : ui ≤ u) (hu0 : u < 0) (hua : u < a) (hb0 : b ≤ 0)
    (hP : AbsolutelyContinuousOnInterval (S.outgoingDatum u) a b)
    (hq : ∀ᵐ x, x ∈ Ioo a b → HasDerivAt (S.outgoingDatum u) (S.lam u x * q u x) x) :
    IntervalPrimitive (fun v => S.r u v * S.renormalizedInteraction u v)
      (fun v => S.r u v * (S.r u v / S.nu u v * S.duphi u v) *
        S.renormalizedDerivative q u v) a b := by
  have hr := intervalPrimitive_ac hab
    (fun x hx => h.regularCenter.localBV.radius_out u a x hx.1
      (outSeg_subset_triangle hu hu0 hua.le (hx.2.trans hb0)))
  apply ac_integral_eq_sub hab
    (hr.fun_mul (h.renormalizedInteraction_ac_out_of_ac_datum hab hu hu0 hua hb0 hP))
  filter_upwards [h.outgoing_reduced_ae hab hu hu0 hua hb0,
    h.renormalized_radial_ae_of_datum_derivative hab hu hu0 hua hb0 hq] with x hx hcx hxI
  convert (hx hxI).1.mul (hcx hxI) using 1
  field_simp [ne_of_gt (h.r_pos (u := u) (v := x)
    ⟨hu, hu0, (hua.trans hxI.1).le, hxI.2.le.trans hb0⟩ (hua.trans hxI.1))]
  ring

/-- Bounded interaction and vanishing radius give the zero weighted axis trace.
Paper `e1a0fd5`, `eq:renormalized-radial-primitive`, line 1078. -/
theorem radius_interaction_axis_trace_of_bound {u v M : ℝ}
    (hu : ui ≤ u) (hu0 : u < 0) (huv : u < v) (hv0 : v ≤ 0)
    (hC : ∀ s ∈ Ioo u v, |S.renormalizedInteraction u s| ≤ M) :
    Tendsto (fun s => S.r u s * S.renormalizedInteraction u s) (𝓝[Ioo u v] u) (𝓝 0) := by
  have hc := continuous_out h.regularCenter.continuous_r
    (outSeg_subset_triangle hu hu0 le_rfl hv0)
  have hr := (hc u ⟨le_rfl, huv.le⟩).mono Ioo_subset_Icc_self
  change Tendsto (S.r u) (𝓝[Ioo u v] u) (𝓝 (S.r u u)) at hr
  have haxis := (h.regularCenter.localBV.axis_values u ⟨hu, hu0, le_rfl, hu0.le⟩).1
  rw [haxis] at hr
  apply squeeze_zero_norm' ?_ (by simpa using hr.abs.mul_const M)
  filter_upwards [eventually_mem_nhdsWithin] with s hs
  simpa only [Real.norm_eq_abs, abs_mul] using
    mul_le_mul_of_nonneg_left (hC s hs) (abs_nonneg (S.r u s))

/-- The interaction primitive integrated from the regular axis.
Paper `e1a0fd5`, `eq:renormalized-radial-primitive`, lines 1038–1043 and 1078.
Local AC is supplied by Lemma 2.2, bounded interaction by the amplitude
bounds, and integrability by the cone L¹ bound with bounded `r B`. -/
theorem renormalized_axis_primitive_of_local_transport {q : ℝ → ℝ → ℝ} {u v M : ℝ}
    (hu : ui ≤ u) (hu0 : u < 0) (huv : u < v) (hv0 : v ≤ 0)
    (hC : ∀ s ∈ Ioo u v, |S.renormalizedInteraction u s| ≤ M)
    (hlocal : ∀ a ∈ Ioo u v, IntervalPrimitive
      (fun s => S.r u s * S.renormalizedInteraction u s)
      (fun s => S.r u s * (S.r u s / S.nu u s * S.duphi u s) *
        S.renormalizedDerivative q u s) a v)
    (hg : IntervalIntegrable
      (fun s => S.r u s * (S.r u s / S.nu u s * S.duphi u s) *
        S.renormalizedDerivative q u s) volume u v) :
    S.renormalizedInteraction u v / S.r u v =
      (1 / S.r u v ^ 2) * ∫ s in u..v,
        S.r u s * (S.r u s / S.nu u s * S.duphi u s) * S.renormalizedDerivative q u s := by
  have he := primitive_from_zero_axis_trace huv hg
    (h.radius_interaction_axis_trace_of_bound hu hu0 huv hv0 hC) hlocal
  have hr0 := ne_of_gt (h.r_pos ⟨hu, hu0, huv.le, hv0⟩ huv)
  calc
    _ = (S.r u v * S.renormalizedInteraction u v) / S.r u v ^ 2 := by
      field_simp [hr0]
    _ = _ := by rw [he]; ring

end StandingFull

end AcExtensionPrinciple

end
