module

public import AcExtensionPrinciple.Gauge.Variation
public import Mathlib.Topology.Order.LeftRightNhds

/-!
# One-sided filters for an increasing chart

Components for paper `e1a0fd5`, `equations.tex` lines 1390–1422.
A continuous strictly increasing map on a nontrivial right interval carries
the right neighborhood filter onto the corresponding right neighborhood filter.
-/

public section

namespace AcExtensionPrinciple

open Set Filter
open scoped Topology

/-- Increasing continuous charts preserve the entire right neighborhood filter.
Paper `e1a0fd5`, `eq:continuation-null-gauge`, lines 1390–1395. -/
theorem map_nhdsGT_of_continuous_strictMonoOn {T : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hc : ContinuousOn T (Icc a b)) (hm : StrictMonoOn T (Icc a b)) :
    Filter.map T (𝓝[>] a) = 𝓝[>] T a := by
  apply le_antisymm
  · change Tendsto T (𝓝[>] a) (𝓝[>] T a)
    have hsource : 𝓝[>] a ≤ 𝓝[Icc a b] a := by
      apply le_inf nhdsWithin_le_nhds
      exact le_principal_iff.mpr (mem_of_superset (Ioo_mem_nhdsGT hab) Ioo_subset_Icc_self)
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨(hc a ⟨le_rfl, hab.le⟩).tendsto.mono_left hsource, ?_⟩
    filter_upwards [Ioo_mem_nhdsGT hab] with x hx
    exact hm ⟨le_rfl, hab.le⟩ ⟨hx.1.le, hx.2.le⟩ hx.1
  · rw [Filter.le_def]
    intro s hs
    change T ⁻¹' s ∈ 𝓝[>] a at hs
    obtain ⟨d, hd, hs⟩ := (mem_nhdsGT_iff_exists_mem_Ioc_Ioo_subset hab).mp hs
    have had : T a < T d := hm ⟨le_rfl, hab.le⟩ ⟨hd.1.le, hd.2⟩ hd.1
    apply mem_of_superset (Ioo_mem_nhdsGT had)
    intro y hy
    have hsub : Icc a d ⊆ Icc a b := Icc_subset_Icc le_rfl hd.2
    have hi := (hc.mono hsub).image_Ioo_of_strictMonoOn hd.1.le (hm.mono hsub)
    have hym : y ∈ T '' Ioo a d := by rwa [hi]
    obtain ⟨x, hx, rfl⟩ := hym
    exact hs hx

/-- The displacement form of a right chart, as used in the axis limit conditions.
Paper `e1a0fd5`, `eq:continuation-null-gauge`, lines 1390–1395. -/
theorem map_axis_displacement {T : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hc : ContinuousOn T (Icc a b)) (hm : StrictMonoOn T (Icc a b)) :
    Filter.map (fun ε : ℝ => T (a + ε) - T a) (𝓝[>] 0) = 𝓝[>] 0 := by
  have hsub : MapsTo (fun ε : ℝ => a + ε) (Icc 0 (b - a)) (Icc a b) := by
    intro ε hε
    constructor <;> linarith [hε.1, hε.2]
  have hcont : ContinuousOn (fun ε : ℝ => T (a + ε) - T a) (Icc 0 (b - a)) :=
    (hc.comp (continuous_const.add continuous_id).continuousOn hsub).sub continuousOn_const
  have hmono : StrictMonoOn (fun ε : ℝ => T (a + ε) - T a) (Icc 0 (b - a)) := by
    intro x hx y hy hxy
    exact sub_lt_sub_right (hm (hsub hx) (hsub hy) (by linarith)) _
  simpa using map_nhdsGT_of_continuous_strictMonoOn (by linarith : 0 < b - a) hcont hmono

end AcExtensionPrinciple

end
