module

public import AcExtensionPrinciple.Solution.Geometry

/-!
# Characteristic paths for the one-sided regular-axis reading

Paper `e1a0fd5`, `equations.tex` lines 247–261,
`eq:regular-axis-scalar-traces`. These filter calculations do not assert
that characteristic limits imply a joint limit.
-/

public section

namespace AcExtensionPrinciple

open Set Filter
open scoped Topology

/-- The outgoing characteristic approaches the axis within the off-axis triangle.
Paper `e1a0fd5`, lines 247–262, `eq:regular-axis-one-sided-traces`, `eq:regular-axis-scalar-traces`. -/
theorem oneSided_outgoing_path {ui a : ℝ} (ha : (a, a) ∈ axis ui) :
    Tendsto (fun ε : ℝ => (a, a + ε)) (𝓝[>] 0)
      (𝓝[pastTriangle ui \ axis ui] (a, a)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_, ?_⟩
  · simpa using tendsto_const_nhds.prodMk_nhds
      ((tendsto_const_nhds (x := a)).add
        (tendsto_id.mono_left nhdsWithin_le_nhds :
          Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0)))
  · filter_upwards [Ioo_mem_nhdsGT (neg_pos.mpr ha.2.1)] with ε hε
    refine ⟨⟨ha.1, ha.2.1, by linarith [hε.1], by linarith [hε.2]⟩, ?_⟩
    intro haxis
    have he : a + ε = a := haxis.2.2
    linarith [hε.1]

/-- Restricting the incoming characteristic to the triangle handles the initial vertex.
Paper `e1a0fd5`, lines 247–262, `eq:regular-axis-one-sided-traces`, `eq:regular-axis-scalar-traces`. -/
theorem oneSided_incoming_path {ui a : ℝ} (ha : (a, a) ∈ axis ui) :
    Tendsto (fun ε : ℝ => (a - ε, a))
      (𝓝[>] 0 ⊓ 𝓟 {ε | ui ≤ a - ε})
      (𝓝[pastTriangle ui \ axis ui] (a, a)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_, ?_⟩
  · have ht : Tendsto (fun ε : ℝ => ε)
        (𝓝[>] 0 ⊓ 𝓟 {ε | ui ≤ a - ε}) (𝓝 0) :=
      tendsto_id.mono_left (inf_le_left.trans nhdsWithin_le_nhds)
    simpa using ((tendsto_const_nhds (x := a)).sub ht).prodMk_nhds
      (tendsto_const_nhds (x := a))
  · have hpos : ∀ᶠ ε : ℝ in 𝓝[>] 0 ⊓ 𝓟 {ε | ui ≤ a - ε}, 0 < ε :=
      Filter.Eventually.filter_mono inf_le_left
        (self_mem_nhdsWithin : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε)
    have hbound : ∀ᶠ ε : ℝ in 𝓝[>] 0 ⊓ 𝓟 {ε | ui ≤ a - ε}, ui ≤ a - ε :=
      (show ∀ᶠ ε : ℝ in 𝓟 {ε | ui ≤ a - ε}, ui ≤ a - ε from
        Filter.mem_principal_self _).filter_mono inf_le_right
    filter_upwards [hpos, hbound] with ε hε hb
    refine ⟨⟨hb, by linarith [ha.2.1], by linarith, ha.2.1.le⟩, ?_⟩
    intro haxis
    have he : a = a - ε := haxis.2.2
    linarith

/-- A joint trace gives the outgoing one-sided trace. Paper `e1a0fd5`,
lines 247–261, `eq:regular-axis-scalar-traces`. -/
theorem oneSided_outgoing_of_joint {ui a L : ℝ} {f : ℝ → ℝ → ℝ}
    (ha : (a, a) ∈ axis ui)
    (ht : Tendsto (fun p : ℝ × ℝ => f p.1 p.2)
      (𝓝[pastTriangle ui \ axis ui] (a, a)) (𝓝 L)) :
    Tendsto (fun ε => f a (a + ε)) (𝓝[>] 0) (𝓝 L) :=
  ht.comp (oneSided_outgoing_path ha)

/-- A joint trace gives the restricted incoming one-sided trace. Paper `e1a0fd5`,
lines 247–261, `eq:regular-axis-scalar-traces`. -/
theorem oneSided_incoming_of_joint {ui a L : ℝ} {f : ℝ → ℝ → ℝ}
    (ha : (a, a) ∈ axis ui)
    (ht : Tendsto (fun p : ℝ × ℝ => f p.1 p.2)
      (𝓝[pastTriangle ui \ axis ui] (a, a)) (𝓝 L)) :
    Tendsto (fun ε => f (a - ε) a)
      (𝓝[>] 0 ⊓ 𝓟 {ε | ui ≤ a - ε}) (𝓝 L) :=
  ht.comp (oneSided_incoming_path ha)

/-- Reparametrize an outgoing ε trace by v decreasing to a. Paper `e1a0fd5`,
lines 247–261, `eq:regular-axis-scalar-traces`. -/
theorem oneSided_outgoing_reparam {a L : ℝ} {f : ℝ → ℝ}
    (ht : Tendsto (fun ε => f (a + ε)) (𝓝[>] 0) (𝓝 L)) :
    Tendsto f (𝓝[>] a) (𝓝 L) := by
  have hs : Tendsto (fun v : ℝ => v - a) (𝓝[>] a) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa using (tendsto_id.mono_left nhdsWithin_le_nhds :
        Tendsto (fun v : ℝ => v) (𝓝[>] a) (𝓝 a)).sub_const a
    · filter_upwards [self_mem_nhdsWithin] with v hv
      exact sub_pos.mpr hv
  simpa only [Function.comp_def, add_sub_cancel] using ht.comp hs

/-- Reparametrize an incoming ε trace at an interior axis point by u increasing to a.
Paper `e1a0fd5`, lines 247–262, `eq:regular-axis-one-sided-traces`, `eq:regular-axis-scalar-traces`. -/
theorem oneSided_incoming_reparam {ui a L : ℝ} {f : ℝ → ℝ} (ha : ui < a)
    (ht : Tendsto (fun ε => f (a - ε))
      (𝓝[>] 0 ⊓ 𝓟 {ε | ui ≤ a - ε}) (𝓝 L)) :
    Tendsto f (𝓝[<] a) (𝓝 L) := by
  have hs : Tendsto (fun u : ℝ => a - u) (𝓝[<] a) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa using (tendsto_const_nhds (x := a)).sub
        (tendsto_id.mono_left nhdsWithin_le_nhds :
          Tendsto (fun u : ℝ => u) (𝓝[<] a) (𝓝 a))
    · filter_upwards [self_mem_nhdsWithin] with u hu
      exact sub_pos.mpr hu
  have hb : Tendsto (fun u : ℝ => a - u) (𝓝[<] a)
      (𝓟 {ε | ui ≤ a - ε}) := by
    apply tendsto_principal.mpr
    filter_upwards [Ioo_mem_nhdsLT ha] with u hu
    simpa only [sub_sub_cancel] using hu.1.le
  simpa only [Function.comp_def, sub_sub_cancel, inf_idem] using ht.comp (hs.inf hb)

/-- At the initial vertex the restricted incoming filter is bottom, hence imposes
no exterior condition. Paper `e1a0fd5`, lines 247–262, `eq:regular-axis-one-sided-traces`, `eq:regular-axis-scalar-traces`. -/
theorem oneSided_incoming_initial_filter (ui : ℝ) :
    (𝓝[>] 0 ⊓ 𝓟 {ε : ℝ | ui ≤ ui - ε}) = ⊥ := by
  apply Filter.empty_mem_iff_bot.mp
  have hpos : ∀ᶠ ε : ℝ in 𝓝[>] 0 ⊓ 𝓟 {ε | ui ≤ ui - ε}, 0 < ε :=
    Filter.Eventually.filter_mono inf_le_left
      (self_mem_nhdsWithin : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε)
  have hbound : ∀ᶠ ε : ℝ in 𝓝[>] 0 ⊓ 𝓟 {ε | ui ≤ ui - ε}, ui ≤ ui - ε :=
    (show ∀ᶠ ε : ℝ in 𝓟 {ε | ui ≤ ui - ε}, ui ≤ ui - ε from
      Filter.mem_principal_self _).filter_mono inf_le_right
  filter_upwards [hpos, hbound] with ε hε hb
  exact (by linarith : False)

end AcExtensionPrinciple

end
