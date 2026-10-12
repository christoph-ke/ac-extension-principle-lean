module

public import AcExtensionPrinciple.Continuation.AxisRanges
public import AcExtensionPrinciple.Continuation.ProperBounds

/-!
# The original solution in the Christodoulou class on proper triangles

Original class-membership components, paper `e1a0fd5`, `equations.tex` lines 220–275 and 1390–1411.
This module assembles the untransformed class, including the corrected δ-ranges and the outgoing
limits at the regular axis.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- Restrict a jointly continuous field to the outgoing axis-limit filter.
Paper `e1a0fd5`, `eq:regular-axis`, lines 220–275 and 1411. -/
theorem outgoing_axis_limit_of_continuous {D E : Set (ℝ × ℝ)}
    {f : ℝ × ℝ → ℝ} {a : ℝ} (hDE : D ⊆ E) (ha : (a, a) ∈ E)
    (hf : ContinuousOn f E) :
    Tendsto (fun v => f (a, v)) (𝓝[>] a ⊓ 𝓟 {v | (a, v) ∈ D}) (𝓝 (f (a, a))) := by
  apply (hf (a, a) ha).tendsto.comp
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · exact (tendsto_const_nhds.prodMk_nhds
      (tendsto_id.mono_left (inf_le_left.trans nhdsWithin_le_nhds)))
  · have hm : ∀ᶠ v in 𝓝[>] a ⊓ 𝓟 {v | (a, v) ∈ D}, (a, v) ∈ D :=
      Filter.Eventually.filter_mono inf_le_right (by simp)
    exact hm.mono (fun _ hv => hDE hv)

/-- Changing from the axis displacement ε to the outgoing parameter v
preserves a right limit. Paper `e1a0fd5`, lines 220–275 and 1411. -/
theorem axis_displacement_limit {f : ℝ → ℝ} {a z : ℝ}
    (h : Tendsto (fun ε => f (a + ε)) (𝓝[>] 0) (𝓝 z)) :
    Tendsto f (𝓝[>] a) (𝓝 z) := by
  have ht : Tendsto (fun v : ℝ => v - a) (𝓝[>] a) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa using ((tendsto_id : Tendsto (id : ℝ → ℝ) (𝓝 a) (𝓝 a)).mono_left
        (nhdsWithin_le_nhds : 𝓝[>] a ≤ 𝓝 a)).sub_const a
    · filter_upwards [self_mem_nhdsWithin] with v hv
      exact sub_pos.mpr hv
  simpa only [Function.comp_def, add_sub_cancel] using h.comp ht

/-- All original integral identities, scalar AC, and axis conditions supply
the Christodoulou core on an off-axis subdomain. Paper `e1a0fd5`,
lines 220–275 and 1411, Q5/Q8. -/
theorem RegularCenterFull.chr_core {ui : ℝ} {S : SSFields}
    {D : Set (ℝ × ℝ)} {A : Set ℝ} (h : RegularCenterFull ui S)
    (hD : D ⊆ offAxis (pastTriangle ui)) (hA : ∀ a ∈ A, (a, a) ∈ axis ui) :
    ChrBVCore D A S := by
  have htri : D ⊆ pastTriangle ui := hD.trans sdiff_subset
  have hout (p : ℝ × ℝ) (hp : p ∈ D) :
      ContinuousWithinAt (S.phi p.1) {w | p.2 ≤ w ∧ (p.1, w) ∈ D} p.2 :=
    (h.continuous_phi p (htri hp)).comp_of_eq
      (continuousWithinAt_const.prodMk continuousWithinAt_id)
      (fun _ hw => htri hw.2) rfl
  have hin (p : ℝ × ℝ) (hp : p ∈ D) :
      ContinuousWithinAt (fun s => S.phi s p.2)
        {s | p.1 ≤ s ∧ (s, p.2) ∈ D} p.1 :=
    (h.continuous_phi p (htri hp)).comp_of_eq
      (continuousWithinAt_id.prodMk continuousWithinAt_const)
      (fun _ hw => htri hw.2) rfl
  have hlam (p : ℝ × ℝ) (hp : p ∈ D) :
      ContinuousWithinAt (S.lam p.1) {w | p.2 ≤ w ∧ (p.1, w) ∈ D} p.2 :=
    (h.localBV.lam_right_cont p (htri hp)).mono (fun _ hw => ⟨hw.1, htri hw.2⟩)
  have hnu (p : ℝ × ℝ) (hp : p ∈ D) :
      ContinuousWithinAt (fun s => S.nu s p.2)
        {s | p.1 ≤ s ∧ (s, p.2) ∈ D} p.1 :=
    (h.localBV.nu_right_cont p (htri hp)).mono (fun _ hw => ⟨hw.1, htri hw.2⟩)
  refine {
    off_axis := ?_
    radius_out := fun u a b hab hs => h.localBV.radius_out u a b hab (hs.trans htri)
    radius_in := fun v a b hab hs => h.localBV.radius_in v a b hab (hs.trans htri)
    psi_out := fun u a b hab hs => h.localBV.psi_out u a b hab (hs.trans htri)
    psi_in := fun v a b hab hs => h.localBV.psi_in v a b hab (hs.trans htri)
    mass_out := fun u a b hab hs => h.localBV.mass_out u a b hab (hs.trans htri)
    mass_in := fun v a b hab hs => h.localBV.mass_in v a b hab (hs.trans htri)
    lam_in := fun v a b hab hs => h.localBV.lam_in v a b hab (hs.trans hD)
    nu_out := fun u a b hab hs => h.localBV.nu_out u a b hab (hs.trans hD)
    dvpsi_in := fun v a b hab hs => h.localBV.dvpsi_in v a b hab (hs.trans hD)
    dupsi_out := fun u a b hab hs => h.localBV.dupsi_out u a b hab (hs.trans hD)
    scalar_ac_out := ?_
    scalar_ac_in := ?_
    radius_axis_limit := ?_
    mass_axis_limit := ?_
    expansion_axis_limit := ?_
    scalar_axis_variation := fun a ha => (h.chr_axis_variation (hA a ha)).restrict htri
    psi_axis_limit := ?_
    lam_right_cont := hlam
    theta_right_cont := fun p hp =>
      ((h.localBV.dvpsi_right_cont p (htri hp)).mono
        (fun _ hw => ⟨hw.1, htri hw.2⟩)).sub ((hlam p hp).mul (hout p hp))
    nu_right_cont := hnu
    zeta_right_cont := fun p hp =>
      ((h.localBV.dupsi_right_cont p (htri hp)).mono
        (fun _ hw => ⟨hw.1, htri hw.2⟩)).sub ((hnu p hp).mul (hin p hp)) }
  · intro p hp
    exact lt_of_le_of_ne (htri hp).2.2.1 (hD hp).2
  · intro u a b hab hs
    rcases h.localBV.scalar_ac_variation (outSeg u a b)
      (isCompact_singleton.prod isCompact_Icc) (hs.trans htri) with ⟨C, hout, _⟩
    exact (hout u a b hab Subset.rfl).1
  · intro v a b hab hs
    rcases h.localBV.scalar_ac_variation (inSeg v a b)
      (isCompact_Icc.prod isCompact_singleton) (hs.trans htri) with ⟨C, _, hin⟩
    exact (hin v a b hab Subset.rfl).1
  · intro a ha
    have ha' := axis_subset_pastTriangle ui (hA a ha)
    simpa only [(h.localBV.axis_values a ha').1] using
      outgoing_axis_limit_of_continuous htri ha' h.continuous_r
  · intro a ha
    have ha' := axis_subset_pastTriangle ui (hA a ha)
    simpa only [(h.localBV.axis_values a ha').2] using
      outgoing_axis_limit_of_continuous htri ha' h.continuous_m
  · intro a ha
    have hz : S.nu a a + S.lam a a = 0 := by rw [h.axis_expansions a (hA a ha)]; ring
    simpa only [Pi.add_apply, Prod.fst, Prod.snd, hz] using outgoing_axis_limit_of_continuous htri
      (axis_subset_pastTriangle ui (hA a ha)) (h.continuous_nu.add h.continuous_lam)
  · intro a ha
    exact (axis_displacement_limit (h.localBV.psi_axis_limit a
      (axis_subset_pastTriangle ui (hA a ha)))).mono_left inf_le_left

/-- Before reparametrization: the original solution belongs to the global Christodoulou class on
every proper triangle, excluding its axis. Paper `e1a0fd5`, lines 1390–1411. -/
theorem StandingFull.chr_on_proper_triangle {ui ū c : ℝ} {S : SSFields}
    (h : StandingFull ui S) (hū : ui ≤ ū) (hc : c < 0) :
    ChristodoulouBV (offAxis (properOriginalTriangle ū c)) (Icc ū c) S := by
  have hD : offAxis (properOriginalTriangle ū c) ⊆ offAxis (pastTriangle ui) :=
    sdiff_subset_sdiff_left (properOriginalTriangle_subset hū hc)
  exact ⟨h.regularCenter.chr_core hD
    (fun a ha => ⟨hū.trans ha.1, ha.2.trans_lt hc, rfl⟩),
    (h.proper_triangle_bounds hū hc).restrict sdiff_subset⟩

end AcExtensionPrinciple

end
