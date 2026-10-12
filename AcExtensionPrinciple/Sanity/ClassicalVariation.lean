module

public import AcExtensionPrinciple.Sanity.ClassicalCalculus

/-!
# Uniform classical variation bounds
Paper `e1a0fd5`, lines 220–275, Luk–Oh Definition 2.1; Christodoulou CPAM p. 1157.
The Lipschitz constant is uniform on the closed triangle, including the apex.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- Lipschitz variation on an arbitrary subset of an interval.
Paper `e1a0fd5`, line 222, Luk–Oh Definition 2.1(5). -/
theorem classical_variation_le {f : ℝ → ℝ} {s : Set ℝ} {a b : ℝ} {L : NNReal}
    (hf : LipschitzOnWith L f s) (hs : s ⊆ Icc a b) :
    eVariationOn f s ≤ ENNReal.ofReal ((L : ℝ) * (b - a)) := by
  have ht := hf.comp_eVariationOn_le (mapsTo_id s)
  change eVariationOn f s ≤ _ at ht
  calc
    _ ≤ (L : ℝ≥0∞) * eVariationOn id s := ht
    _ ≤ (L : ℝ≥0∞) * eVariationOn id (Icc a b) :=
      mul_le_mul (le_refl _) (eVariationOn.mono id hs) bot_le bot_le
    _ = _ := by rw [eVariationOn_id_Icc, ENNReal.ofReal_mul L.coe_nonneg]; simp

/-- Outgoing variation on any clipped characteristic portion.
Paper `e1a0fd5`, line 222, Luk–Oh Definition 2.1(5). -/
theorem classical_variation_out {ui u a b : ℝ} {f : ℝ × ℝ → ℝ} {L : NNReal}
    (hf : LipschitzOnWith L f (closedTriangle ui)) {s : Set ℝ}
    (hs : ∀ x ∈ s, (u, x) ∈ closedTriangle ui) (hi : s ⊆ Icc a b) :
    eVariationOn (fun v => f (u, v)) s ≤ ENNReal.ofReal ((L : ℝ) * (b - a)) := by
  apply classical_variation_le (L := L) _ hi
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  simpa using hf.dist_le_mul (u, x) (hs x hx) (u, y) (hs y hy)

/-- Incoming variation on any clipped characteristic portion.
Paper `e1a0fd5`, line 222, Luk–Oh Definition 2.1(5). -/
theorem classical_variation_in {ui v a b : ℝ} {f : ℝ × ℝ → ℝ} {L : NNReal}
    (hf : LipschitzOnWith L f (closedTriangle ui)) {s : Set ℝ}
    (hs : ∀ x ∈ s, (x, v) ∈ closedTriangle ui) (hi : s ⊆ Icc a b) :
    eVariationOn (fun u => f (u, v)) s ≤ ENNReal.ofReal ((L : ℝ) * (b - a)) := by
  apply classical_variation_le (L := L) _ hi
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  simpa using hf.dist_le_mul (x, v) (hs x hx) (y, v) (hs y hy)

/-- A single finite constant bounds both characteristic variations of a classical field.
Paper `e1a0fd5`, line 222, Luk–Oh Definition 2.1(2)–(4). -/
theorem classical_uniform_variation {ui : ℝ} {f : ℝ × ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (closedTriangle ui)) : ∃ C : ℝ,
    (∀ u a b, a ≤ b → outSeg u a b ⊆ pastTriangle ui →
      eVariationOn (fun v => f (u, v)) (Icc a b) ≤ ENNReal.ofReal C) ∧
    (∀ v a b, a ≤ b → inSeg v a b ⊆ pastTriangle ui →
      eVariationOn (fun u => f (u, v)) (Icc a b) ≤ ENNReal.ofReal C) := by
  obtain ⟨L, hL⟩ := classical_lipschitz hf
  refine ⟨(L : ℝ) * (-ui), ?_, ?_⟩
  · intro u a b hab hs
    have ha := hs (a := (u, a)) ⟨mem_singleton u, le_rfl, hab⟩
    have hb := hs (a := (u, b)) ⟨mem_singleton u, hab, le_rfl⟩
    exact (classical_variation_out hL
      (fun x hx => classical_past_subset_closed ui (hs ⟨mem_singleton u, hx⟩))
      Subset.rfl).trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left (by linarith [ha.1, ha.2.2.1, hb.2.2.2]) L.coe_nonneg))
  · intro v a b hab hs
    have ha := hs (a := (a, v)) ⟨⟨le_rfl, hab⟩, mem_singleton v⟩
    have hb := hs (a := (b, v)) ⟨⟨hab, le_rfl⟩, mem_singleton v⟩
    exact (classical_variation_in hL
      (fun x hx => classical_past_subset_closed ui (hs ⟨hx, mem_singleton v⟩))
      Subset.rfl).trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left (by linarith [ha.1, hb.2.1]) L.coe_nonneg))

/-- Uniform variation bounded by `Lε` vanishes as the characteristic length shrinks.
The four axis families discharge this bound below. Paper `e1a0fd5`, line 222, Def. 2.1(5). -/
theorem classical_shrinking_variation {F : ℝ → ℝ → ℝ≥0∞} {L : NNReal}
    (hF : ∀ ε > 0, ∀ δ ∈ Ioc 0 ε, F ε δ ≤ ENNReal.ofReal ((L : ℝ) * ε)) :
    Tendsto (fun ε => ⨆ δ ∈ Ioc 0 ε, F ε δ) (𝓝[>] 0) (𝓝 0) := by
  have ht : Tendsto (fun ε : ℝ => ENNReal.ofReal ((L : ℝ) * ε)) (𝓝[>] 0) (𝓝 0) := by
    have ht : Tendsto (fun ε : ℝ => (L : ℝ) * ε) (𝓝[>] 0) (𝓝 0) := by
      simpa using tendsto_const_nhds.mul
        (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun ε : ℝ => ε)
          (𝓝[>] 0) (𝓝 0))
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
    (Eventually.of_forall (fun _ => bot_le))
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact iSup_le (fun δ => iSup_le (fun hδ => hF ε hε δ hδ))

/-- The four clipped axis families have vanishing variation for a classical scalar.
Paper `e1a0fd5`, line 222, Luk–Oh Definition 2.1(5). -/
theorem classical_axis_variation {ui : ℝ} {S : SSFields}
    (hf : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.phi p.1 p.2) (closedTriangle ui))
    (a : ℝ) : AxisVanishingVariation (pastTriangle ui) S a := by
  obtain ⟨L, hL⟩ := classical_lipschitz hf
  constructor
  · apply classical_shrinking_variation (L := L)
    intro ε hε δ hδ
    exact (classical_variation_out hL
      (fun x hx => classical_past_subset_closed ui hx.2)
      (fun x hx => Ioo_subset_Icc_self hx.1)).trans
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (by linarith [hδ.2])
          L.coe_nonneg))
  · apply classical_shrinking_variation (L := L)
    intro ε hε δ hδ
    exact (classical_variation_in hL
      (fun x hx => classical_past_subset_closed ui hx.2)
      (fun x hx => Ioo_subset_Icc_self hx.1)).trans
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (by linarith [hδ.1])
          L.coe_nonneg))
  · apply classical_shrinking_variation (L := L)
    intro ε hε δ hδ
    exact (classical_variation_in hL
      (fun x hx => classical_past_subset_closed ui hx.2)
      (fun x hx => Ioo_subset_Icc_self hx.1)).trans
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (by linarith [hδ.2])
          L.coe_nonneg))
  · apply classical_shrinking_variation (L := L)
    intro ε hε δ hδ
    exact (classical_variation_out hL
      (fun x hx => classical_past_subset_closed ui hx.2)
      (fun x hx => Ioo_subset_Icc_self hx.1)).trans
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (by linarith [hδ.1])
          L.coe_nonneg))

end AcExtensionPrinciple

end
