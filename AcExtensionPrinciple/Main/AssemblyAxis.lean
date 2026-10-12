module

public import AcExtensionPrinciple.Main.AssemblyClassGeometry

/-!
# Local transport of regular-axis conditions

Paper `e1a0fd5`, `equations.tex` lines 222 and 1411–1422. Axis limits and
all four vanishing-variation families transfer when the continuation
matches a source class in a coordinate neighborhood of the axis point.
-/

public section

namespace AcExtensionPrinciple

open Set Filter
open scoped Topology ENNReal

/-- Sums of pointwise quantities are pointwise. Paper `e1a0fd5`, lines 1411–1422. -/
theorem LocalQuantity.add {q q' : SSFields → ℝ → ℝ → ℝ}
    (hq : LocalQuantity q) (hq' : LocalQuantity q') :
    LocalQuantity (fun S u v => q S u v + q' S u v) := by
  intro S₁ S₂ u v he
  dsimp only
  rw [hq S₁ S₂ u v he, hq' S₁ S₂ u v he]

/-- θ is a pointwise quantity. Paper `e1a0fd5`, lines 222 and 1411–1422. -/
theorem local_theta : LocalQuantity SSFields.theta := by
  intro S₁ S₂ u v he
  dsimp [SSFields.theta]
  rw [local_dvpsi S₁ S₂ u v he, local_lam S₁ S₂ u v he, local_phi S₁ S₂ u v he]

/-- ζ is a pointwise quantity. Paper `e1a0fd5`, lines 222 and 1411–1422. -/
theorem local_zeta : LocalQuantity SSFields.zeta := by
  intro S₁ S₂ u v he
  dsimp [SSFields.zeta]
  rw [local_dupsi S₁ S₂ u v he, local_nu S₁ S₂ u v he, local_phi S₁ S₂ u v he]

/-- Variation decreases under simultaneous domain restriction and field
identification. Paper `e1a0fd5`, lines 222 and 1411–1422. -/
theorem variation_transfer {f g : ℝ → ℝ} {s t : Set ℝ}
    (hm : ∀ x ∈ s, x ∈ t ∧ f x = g x) : eVariationOn f s ≤ eVariationOn g t := by
  rw [eVariationOn.congr (fun x hx => (hm x hx).2)]
  exact eVariationOn.mono _ (fun x hx => (hm x hx).1)

/-- A source axis limit transfers through a matching coordinate neighborhood.
Paper `e1a0fd5`, lines 222 and 1411–1422. -/
theorem axis_limit_local_transfer {D E : Set (ℝ × ℝ)} {S P : SSFields}
    {q : SSFields → ℝ → ℝ → ℝ} {a η L : ℝ} (hη : 0 < η) (hq : LocalQuantity q)
    (hm : ∀ p ∈ D, |p.1 - a| < η → |p.2 - a| < η →
      p ∈ E ∧ P.values p.1 p.2 = S.values p.1 p.2)
    (ht : Tendsto (q S a) (𝓝[>] a ⊓ 𝓟 {v | (a, v) ∈ E}) (𝓝 L)) :
    Tendsto (q P a) (𝓝[>] a ⊓ 𝓟 {v | (a, v) ∈ D}) (𝓝 L) := by
  have hnear : ∀ᶠ v in 𝓝[>] a ⊓ 𝓟 {v | (a, v) ∈ D},
      (a, v) ∈ E ∧ q P a v = q S a v := by
    have hmem : ∀ᶠ v in 𝓝[>] a ⊓ 𝓟 {v | (a, v) ∈ D}, (a, v) ∈ D :=
      Filter.Eventually.filter_mono inf_le_right (by simp)
    filter_upwards [Filter.Eventually.filter_mono inf_le_left
      (Ioo_mem_nhdsGT (show a < a + η by linarith)), hmem]
      with v hv hp
    obtain ⟨hE, he⟩ := hm (a, v) hp (by simpa using hη)
      (abs_lt.mpr ⟨by linarith [hv.1], by linarith [hv.2]⟩)
    exact ⟨hE, hq P S a v he⟩
  have hfilter : 𝓝[>] a ⊓ 𝓟 {v | (a, v) ∈ D} ≤
      𝓝[>] a ⊓ 𝓟 {v | (a, v) ∈ E} :=
    le_inf inf_le_left (le_principal_iff.mpr (hnear.mono (fun _ hv => hv.1)))
  exact (ht.mono_left hfilter).congr' (hnear.mono (fun _ hv => hv.2.symm))

/-- All four Christodoulou axis-variation families transfer locally,
including their δ = 0 members. Paper `e1a0fd5`, lines 222 and 1411–1422. -/
theorem axis_variation_local_transfer {D E : Set (ℝ × ℝ)} {S P : SSFields}
    {a η : ℝ} (hη : 0 < η)
    (hm : ∀ p ∈ D, |p.1 - a| < η → |p.2 - a| < η →
      p ∈ E ∧ P.values p.1 p.2 = S.values p.1 p.2)
    (h : ChrAxisVanishingVariation E S a) : ChrAxisVanishingVariation D P a := by
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < η :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds hη)
  constructor
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h.past_outgoing
      (Eventually.of_forall (fun _ => bot_le))
    filter_upwards [hsmall] with ε hε
    apply iSup_le
    intro δ
    apply iSup_le
    intro hδ
    apply le_iSup_of_le δ
    apply le_iSup_of_le hδ
    apply variation_transfer
    intro x hx
    have hδ0 := hδ.1
    have hδε := hδ.2
    obtain ⟨hE, he⟩ := hm (a - δ, x) hx.2
      (abs_lt.mpr ⟨by linarith [hx.1.1, hx.1.2], by linarith [hx.1.1, hx.1.2]⟩)
      (abs_lt.mpr ⟨by linarith [hx.1.1, hx.1.2], by linarith [hx.1.1, hx.1.2]⟩)
    exact ⟨⟨hx.1, hE⟩, local_phi P S _ _ he⟩
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h.past_incoming
      (Eventually.of_forall (fun _ => bot_le))
    filter_upwards [hsmall] with ε hε
    apply iSup_le
    intro δ
    apply iSup_le
    intro hδ
    apply le_iSup_of_le δ
    apply le_iSup_of_le hδ
    apply variation_transfer
    intro x hx
    have hδ0 := hδ.1
    have hδε := hδ.2
    obtain ⟨hE, he⟩ := hm (x, a - δ) hx.2
      (abs_lt.mpr ⟨by linarith [hx.1.1, hx.1.2], by linarith [hx.1.1, hx.1.2]⟩)
      (abs_lt.mpr ⟨by linarith [hx.1.1, hx.1.2], by linarith [hx.1.1, hx.1.2]⟩)
    exact ⟨⟨hx.1, hE⟩, local_phi P S _ _ he⟩
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h.future_incoming
      (Eventually.of_forall (fun _ => bot_le))
    filter_upwards [hsmall] with ε hε
    apply iSup_le
    intro δ
    apply iSup_le
    intro hδ
    apply le_iSup_of_le δ
    apply le_iSup_of_le hδ
    apply variation_transfer
    intro x hx
    have hδ0 := hδ.1
    have hδε := hδ.2
    obtain ⟨hE, he⟩ := hm (x, a + δ) hx.2
      (abs_lt.mpr ⟨by linarith [hx.1.1, hx.1.2], by linarith [hx.1.1, hx.1.2]⟩)
      (abs_lt.mpr ⟨by linarith [hx.1.1, hx.1.2], by linarith [hx.1.1, hx.1.2]⟩)
    exact ⟨⟨hx.1, hE⟩, local_phi P S _ _ he⟩
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h.future_outgoing
      (Eventually.of_forall (fun _ => bot_le))
    filter_upwards [hsmall] with ε hε
    apply iSup_le
    intro δ
    apply iSup_le
    intro hδ
    apply le_iSup_of_le δ
    apply le_iSup_of_le hδ
    apply variation_transfer
    intro x hx
    have hδ0 := hδ.1
    have hδε := hδ.2
    obtain ⟨hE, he⟩ := hm (a + δ, x) hx.2
      (abs_lt.mpr ⟨by linarith [hx.1.1, hx.1.2], by linarith [hx.1.1, hx.1.2]⟩)
      (abs_lt.mpr ⟨by linarith [hx.1.1, hx.1.2], by linarith [hx.1.1, hx.1.2]⟩)
    exact ⟨⟨hx.1, hE⟩, local_phi P S _ _ he⟩

end AcExtensionPrinciple

end
