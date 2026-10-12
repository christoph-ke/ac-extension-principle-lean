module

public import AcExtensionPrinciple.External.SmallBVExistence

/-!
# Restricting the development for uniqueness

This module proves domain restriction for paper `e1a0fd5`, `equations.tex` line 1411. Restriction
keeps Christodoulou's original four δ-ranges unchanged.
-/

public section

namespace AcExtensionPrinciple

open Set Filter
open scoped Topology ENNReal

/-- All four axis variation conditions decrease under domain restriction.
Paper `e1a0fd5`, line 1411, Christodoulou pp. 1146–1147, item 4. -/
theorem ChrAxisVanishingVariation.restrict {D E : Set (ℝ × ℝ)} {S : SSFields}
    {a : ℝ} (h : ChrAxisVanishingVariation D S a) (hED : E ⊆ D) :
    ChrAxisVanishingVariation E S a := by
  have hp (f : ℝ → ℝ) (s : Set ℝ) (p : ℝ → ℝ × ℝ) :
      eVariationOn f {x | x ∈ s ∧ p x ∈ E} ≤
        eVariationOn f {x | x ∈ s ∧ p x ∈ D} :=
    eVariationOn.mono _ (fun _ hx => ⟨hx.1, hED hx.2⟩)
  constructor
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      h.past_outgoing (fun _ => zero_le) (fun _ => iSup_mono fun _ =>
        iSup_mono fun _ => hp _ _ _)
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      h.past_incoming (fun _ => zero_le) (fun _ => iSup_mono fun _ =>
        iSup_mono fun _ => hp _ _ _)
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      h.future_incoming (fun _ => zero_le) (fun _ => iSup_mono fun _ =>
        iSup_mono fun _ => hp _ _ _)
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      h.future_outgoing (fun _ => zero_le) (fun _ => iSup_mono fun _ =>
        iSup_mono fun _ => hp _ _ _)

/-- Integral equations, AC and outgoing axis limits survive restriction. Paper `e1a0fd5`, line 1411,
restriction to the uniqueness domain. -/
theorem ChrBVCore.restrict {D E : Set (ℝ × ℝ)} {A B : Set ℝ} {S : SSFields}
    (h : ChrBVCore D A S) (hED : E ⊆ D) (hBA : B ⊆ A) : ChrBVCore E B S where
  off_axis := hED.trans h.off_axis
  radius_out u a b hab hs := h.radius_out u a b hab (hs.trans hED)
  radius_in v a b hab hs := h.radius_in v a b hab (hs.trans hED)
  psi_out u a b hab hs := h.psi_out u a b hab (hs.trans hED)
  psi_in v a b hab hs := h.psi_in v a b hab (hs.trans hED)
  mass_out u a b hab hs := h.mass_out u a b hab (hs.trans hED)
  mass_in v a b hab hs := h.mass_in v a b hab (hs.trans hED)
  lam_in v a b hab hs := h.lam_in v a b hab (hs.trans hED)
  nu_out u a b hab hs := h.nu_out u a b hab (hs.trans hED)
  dvpsi_in v a b hab hs := h.dvpsi_in v a b hab (hs.trans hED)
  dupsi_out u a b hab hs := h.dupsi_out u a b hab (hs.trans hED)
  scalar_ac_out u a b hab hs := h.scalar_ac_out u a b hab (hs.trans hED)
  scalar_ac_in v a b hab hs := h.scalar_ac_in v a b hab (hs.trans hED)
  radius_axis_limit a ha := (h.radius_axis_limit a (hBA ha)).mono_left
    (inf_le_inf_left _ (principal_mono.mpr (fun _ hv => hED hv)))
  mass_axis_limit a ha := (h.mass_axis_limit a (hBA ha)).mono_left
    (inf_le_inf_left _ (principal_mono.mpr (fun _ hv => hED hv)))
  expansion_axis_limit a ha := (h.expansion_axis_limit a (hBA ha)).mono_left
    (inf_le_inf_left _ (principal_mono.mpr (fun _ hv => hED hv)))
  scalar_axis_variation a ha := (h.scalar_axis_variation a (hBA ha)).restrict hED
  psi_axis_limit a ha := (h.psi_axis_limit a (hBA ha)).mono_left
    (inf_le_inf_left _ (principal_mono.mpr (fun _ hv => hED hv)))
  lam_right_cont p hp := (h.lam_right_cont p (hED hp)).mono
    (fun _ hw => ⟨hw.1, hED hw.2⟩)
  theta_right_cont p hp := (h.theta_right_cont p (hED hp)).mono
    (fun _ hw => ⟨hw.1, hED hw.2⟩)
  nu_right_cont p hp := (h.nu_right_cont p (hED hp)).mono
    (fun _ hw => ⟨hw.1, hED hw.2⟩)
  zeta_right_cont p hp := (h.zeta_right_cont p (hED hp)).mono
    (fun _ hw => ⟨hw.1, hED hw.2⟩)

/-- Uniform BV bounds survive restriction of the domain. Paper `e1a0fd5`,
line 1411, Christodoulou pp. 1146–1147, items 1, 3, 5. -/
theorem ChrBVBoundsOn.restrict {K D E : Set (ℝ × ℝ)} {S : SSFields}
    (h : ChrBVBoundsOn K D S) (hED : E ⊆ D) : ChrBVBoundsOn K E S := by
  rcases h with ⟨⟨c, N, hc, hb⟩, ⟨C, hout, hin⟩⟩
  refine ⟨⟨c, N, hc, fun p hp => hb p ⟨hp.1, hED hp.2⟩⟩, C, ?_, ?_⟩
  · intro u
    have hs : {v | (u, v) ∈ K ∩ E} ⊆ {v | (u, v) ∈ K ∩ D} :=
      fun _ hv => ⟨hv.1, hED hv.2⟩
    exact ⟨(eVariationOn.mono _ hs).trans (hout u).1,
      (eVariationOn.mono _ hs).trans (hout u).2.1,
      (eVariationOn.mono _ hs).trans (hout u).2.2⟩
  · intro v
    have hs : {u | (u, v) ∈ K ∩ E} ⊆ {u | (u, v) ∈ K ∩ D} :=
      fun _ hu => ⟨hu.1, hED hu.2⟩
    exact ⟨(eVariationOn.mono _ hs).trans (hin v).1,
      (eVariationOn.mono _ hs).trans (hin v).2.1,
      (eVariationOn.mono _ hs).trans (hin v).2.2⟩

/-- The global class restricts to smaller domains and axis parameter sets. Paper `e1a0fd5`, line
1411, restriction to the uniqueness domain. -/
theorem ChristodoulouBV.restrict {D E : Set (ℝ × ℝ)} {A B : Set ℝ} {S : SSFields}
    (h : ChristodoulouBV D A S) (hED : E ⊆ D) (hBA : B ⊆ A) :
    ChristodoulouBV E B S := ⟨h.1.restrict hED hBA, h.2.restrict hED⟩

/-- Every causal past lies in the complete development. Paper `e1a0fd5`,
line 1411. -/
theorem pastSet_subset_smallBVDomain (a b : ℝ) : pastSet a b ⊆ smallBVDomain :=
  fun _ hp => ⟨hp.1.1, hp.2.1⟩

/-- All adjacent axis parameters of a causal past are nonnegative.
Paper `e1a0fd5`, line 1411. -/
theorem pastSet_adjacentAxis_nonneg (a b : ℝ) : adjacentAxis (pastSet a b) ⊆ Ici 0 := by
  intro t ht
  exact (closure_minimal (fun p hp => hp.1.1)
    (isClosed_le continuous_const continuous_fst)) ht

/-- The global development restricts to precisely the class needed by E2, including the terminal
incoming ray. Paper `e1a0fd5`, line 1411. -/
theorem ChristodoulouBV.on_pastSet {S : SSFields}
    (h : ChristodoulouBV smallBVDomain (Ici 0) S) (a b : ℝ) :
    ChristodoulouBV (pastSet a b) (adjacentAxis (pastSet a b)) S :=
  h.restrict (pastSet_subset_smallBVDomain a b) (pastSet_adjacentAxis_nonneg a b)

end AcExtensionPrinciple

end
