module

public import AcExtensionPrinciple.Continuation.AxisRanges
public import AcExtensionPrinciple.Gauge.Variation

/-!
# Transport of all four axis variation families

Paper `e1a0fd5`, `equations.tex` lines 1390–1411.
An increasing continuous inverse chart compares each family with the
original family at the image interval's actual width. No linear estimate
for the chart is necessary here.
-/

public section

namespace AcExtensionPrinciple

open Set Filter
open scoped Topology ENNReal

/-- Variation of a scalar pullback is bounded by the original variation on
any set containing its image. Paper `e1a0fd5`, line 1411. -/
theorem variation_pullback_le {f U : ℝ → ℝ} {s t : Set ℝ}
    (hU : Monotone U) (hs : MapsTo U s t) :
    eVariationOn (fun x => f (U x)) s ≤ eVariationOn f t :=
  eVariationOn.comp_le_of_monotoneOn f U (hU.monotoneOn _) hs

/-- Both image widths tend to zero from above. Paper `e1a0fd5`,
`eq:continuation-null-gauge`, lines 1390–1395. -/
theorem axis_widths_tendsto {U : ℝ → ℝ} (hU : StrictMono U) (hc : Continuous U) (a : ℝ) :
    Tendsto (fun ε => U a - U (a - ε)) (𝓝[>] 0) (𝓝[>] 0) ∧
    Tendsto (fun ε => U (a + ε) - U a) (𝓝[>] 0) (𝓝[>] 0) := by
  constructor
  · apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · have hf : Continuous (fun ε : ℝ => U a - U (a - ε)) := by fun_prop
      simpa using (hf.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      change 0 < ε at hε
      exact sub_pos.mpr (hU (by linarith))
  · apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · have hf : Continuous (fun ε : ℝ => U (a + ε) - U a) := by fun_prop
      simpa using (hf.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      change 0 < ε at hε
      exact sub_pos.mpr (hU (by linarith))

/-- Transport of the past outgoing axis family.
Paper `e1a0fd5`, lines 1390–1411, Christodoulou item 4. -/
theorem chr_past_outgoing_pullback {D E : Set (ℝ × ℝ)} {S : SSFields}
    {U dU : ℝ → ℝ} {a : ℝ} (hU : StrictMono U) (hc : Continuous U)
    (hmap : ∀ p ∈ E, (U p.1, U p.2) ∈ D)
    (h : Tendsto (fun ε : ℝ => ⨆ δ ∈ Ioc 0 ε, eVariationOn (S.phi (U a - δ))
      {v | v ∈ Ioo (U a - δ) (U a) ∧ (U a - δ, v) ∈ D}) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun ε : ℝ => ⨆ δ ∈ Ioc 0 ε, eVariationOn ((S.pullback U dU).phi (a - δ))
      {v | v ∈ Ioo (a - δ) a ∧ (a - δ, v) ∈ E}) (𝓝[>] 0) (𝓝 0) := by
  have hw := axis_widths_tendsto hU hc a
  have hm := hU.monotone
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (h.comp hw.1)
  · exact Eventually.of_forall (fun _ => zero_le)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    apply iSup_le
    intro δ
    apply iSup_le
    intro hδ
    let d := U a - U (a - δ)
    have hd : d ∈ Ioc 0 (U a - U (a - ε)) :=
      ⟨sub_pos.mpr (hU (by linarith [hδ.1])), sub_le_sub_left (hm (by linarith [hδ.2])) _⟩
    refine le_iSup_of_le d (le_iSup_of_le hd ?_)
    have hcenter : U a - d = U (a - δ) := by dsimp [d]; ring
    simp only [SSFields.pullback, hcenter]
    apply variation_pullback_le hm
    intro v hv
    refine ⟨⟨hU hv.1.1, hU hv.1.2⟩, hmap (a - δ, v) hv.2⟩

/-- Transport of the past incoming axis family.
Paper `e1a0fd5`, lines 1390–1411, Christodoulou item 4. -/
theorem chr_past_incoming_pullback {D E : Set (ℝ × ℝ)} {S : SSFields}
    {U dU : ℝ → ℝ} {a : ℝ} (hU : StrictMono U) (hc : Continuous U)
    (hmap : ∀ p ∈ E, (U p.1, U p.2) ∈ D)
    (h : Tendsto (fun ε : ℝ => ⨆ δ ∈ Ico 0 ε, eVariationOn (fun u => S.phi u (U a - δ))
      {u | u ∈ Ioo (U a - ε) (U a - δ) ∧ (u, U a - δ) ∈ D}) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun ε : ℝ => ⨆ δ ∈ Ico 0 ε, eVariationOn (fun u => (S.pullback U dU).phi u (a - δ))
      {u | u ∈ Ioo (a - ε) (a - δ) ∧ (u, a - δ) ∈ E}) (𝓝[>] 0) (𝓝 0) := by
  have hw := axis_widths_tendsto hU hc a
  have hm := hU.monotone
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (h.comp hw.1)
  · exact Eventually.of_forall (fun _ => zero_le)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    apply iSup_le
    intro δ
    apply iSup_le
    intro hδ
    let d := U a - U (a - δ)
    have hd : d ∈ Ico 0 (U a - U (a - ε)) :=
      ⟨sub_nonneg.mpr (hm (by linarith [hδ.1])),
        sub_lt_sub_left (hU (by linarith [hδ.2])) _⟩
    refine le_iSup_of_le d (le_iSup_of_le hd ?_)
    have hcenter : U a - d = U (a - δ) := by dsimp [d]; ring
    have hwidth : U a - (U a - U (a - ε)) = U (a - ε) := by ring
    simp only [SSFields.pullback, hcenter, hwidth]
    apply variation_pullback_le (f := fun u => S.phi u (U (a - δ))) hm
    intro u hu
    exact ⟨⟨hU hu.1.1, hU hu.1.2⟩, hmap (u, a - δ) hu.2⟩

/-- Transport of the future incoming axis family.
Paper `e1a0fd5`, lines 1390–1411, Christodoulou item 4. -/
theorem chr_future_incoming_pullback {D E : Set (ℝ × ℝ)} {S : SSFields}
    {U dU : ℝ → ℝ} {a : ℝ} (hU : StrictMono U) (hc : Continuous U)
    (hmap : ∀ p ∈ E, (U p.1, U p.2) ∈ D)
    (h : Tendsto (fun ε : ℝ => ⨆ δ ∈ Ioc 0 ε, eVariationOn (fun u => S.phi u (U a + δ))
      {u | u ∈ Ioo (U a) (U a + δ) ∧ (u, U a + δ) ∈ D}) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun ε : ℝ => ⨆ δ ∈ Ioc 0 ε, eVariationOn (fun u => (S.pullback U dU).phi u (a + δ))
      {u | u ∈ Ioo a (a + δ) ∧ (u, a + δ) ∈ E}) (𝓝[>] 0) (𝓝 0) := by
  have hw := axis_widths_tendsto hU hc a
  have hm := hU.monotone
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (h.comp hw.2)
  · exact Eventually.of_forall (fun _ => zero_le)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    apply iSup_le
    intro δ
    apply iSup_le
    intro hδ
    let d := U (a + δ) - U a
    have hd : d ∈ Ioc 0 (U (a + ε) - U a) :=
      ⟨sub_pos.mpr (hU (by linarith [hδ.1])),
        sub_le_sub_right (hm (by linarith [hδ.2])) _⟩
    refine le_iSup_of_le d (le_iSup_of_le hd ?_)
    have hcenter : U a + d = U (a + δ) := by dsimp [d]; ring
    simp only [SSFields.pullback, hcenter]
    apply variation_pullback_le (f := fun u => S.phi u (U (a + δ))) hm
    intro u hu
    exact ⟨⟨hU hu.1.1, hU hu.1.2⟩, hmap (u, a + δ) hu.2⟩

/-- Transport of the future outgoing axis family.
Paper `e1a0fd5`, lines 1390–1411, Christodoulou item 4. -/
theorem chr_future_outgoing_pullback {D E : Set (ℝ × ℝ)} {S : SSFields}
    {U dU : ℝ → ℝ} {a : ℝ} (hU : StrictMono U) (hc : Continuous U)
    (hmap : ∀ p ∈ E, (U p.1, U p.2) ∈ D)
    (h : Tendsto (fun ε : ℝ => ⨆ δ ∈ Ico 0 ε, eVariationOn (S.phi (U a + δ))
      {v | v ∈ Ioo (U a + δ) (U a + ε) ∧ (U a + δ, v) ∈ D}) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun ε : ℝ => ⨆ δ ∈ Ico 0 ε, eVariationOn ((S.pullback U dU).phi (a + δ))
      {v | v ∈ Ioo (a + δ) (a + ε) ∧ (a + δ, v) ∈ E}) (𝓝[>] 0) (𝓝 0) := by
  have hw := axis_widths_tendsto hU hc a
  have hm := hU.monotone
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (h.comp hw.2)
  · exact Eventually.of_forall (fun _ => zero_le)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    apply iSup_le
    intro δ
    apply iSup_le
    intro hδ
    let d := U (a + δ) - U a
    have hd : d ∈ Ico 0 (U (a + ε) - U a) :=
      ⟨sub_nonneg.mpr (hm (by linarith [hδ.1])),
        sub_lt_sub_right (hU (by linarith [hδ.2])) _⟩
    refine le_iSup_of_le d (le_iSup_of_le hd ?_)
    have hcenter : U a + d = U (a + δ) := by dsimp [d]; ring
    have hwidth : U a + (U (a + ε) - U a) = U (a + ε) := by ring
    simp only [SSFields.pullback, hcenter, hwidth]
    apply variation_pullback_le hm
    intro v hv
    exact ⟨⟨hU hv.1.1, hU hv.1.2⟩, hmap (a + δ, v) hv.2⟩

/-- Increasing common charts transport Christodoulou's exact four δ-ranges. Paper `e1a0fd5`, lines
1390–1411, original class membership in the continuation chart. -/
theorem ChrAxisVanishingVariation.pullback {D E : Set (ℝ × ℝ)} {S : SSFields}
    {U dU : ℝ → ℝ} {a : ℝ} (hU : StrictMono U) (hc : Continuous U)
    (hmap : ∀ p ∈ E, (U p.1, U p.2) ∈ D)
    (h : ChrAxisVanishingVariation D S (U a)) :
    ChrAxisVanishingVariation E (S.pullback U dU) a :=
  ⟨chr_past_outgoing_pullback hU hc hmap h.past_outgoing,
    chr_past_incoming_pullback hU hc hmap h.past_incoming,
    chr_future_incoming_pullback hU hc hmap h.future_incoming,
    chr_future_outgoing_pullback hU hc hmap h.future_outgoing⟩

end AcExtensionPrinciple

end
