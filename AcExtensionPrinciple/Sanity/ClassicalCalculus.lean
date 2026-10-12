module

public import AcExtensionPrinciple.Sanity.Classical
public import AcExtensionPrinciple.Solution.PositiveAC
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Calculus on the classical closed triangle
Helpers for paper `e1a0fd5`, `eq:past-triangle`, lines 66–84 and 220–275;
Christodoulou CPAM p. 1157. All regularity premises come from the classical structure.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- The past domain lies in its closed triangle. Paper `e1a0fd5`, `eq:past-triangle`. -/
theorem classical_past_subset_closed (ui : ℝ) : pastTriangle ui ⊆ closedTriangle ui :=
  fun _ hp => ⟨hp.1, hp.2.2⟩

/-- The closed triangle is compact. Paper `e1a0fd5`, `eq:past-triangle`. -/
theorem classical_triangle_compact (ui : ℝ) : IsCompact (closedTriangle ui) := by
  have hc : IsClosed (closedTriangle ui) :=
    (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_fst continuous_snd).inter
        (isClosed_le continuous_snd continuous_const))
  apply ((isCompact_Icc : IsCompact (Icc ui 0)).prod
    (isCompact_Icc : IsCompact (Icc ui 0))).of_isClosed_subset hc
  intro p hp
  exact ⟨⟨hp.1, hp.2.1.trans hp.2.2⟩, ⟨hp.1.trans hp.2.1, hp.2.2⟩⟩

/-- The closed triangle is convex. Paper `e1a0fd5`, `eq:past-triangle`. -/
theorem classical_triangle_convex (ui : ℝ) : Convex ℝ (closedTriangle ui) := by
  intro x hx y hy a b ha hb hab
  change ui ≤ a * x.1 + b * y.1 ∧
    a * x.1 + b * y.1 ≤ a * x.2 + b * y.2 ∧ a * x.2 + b * y.2 ≤ 0
  have hlo : ui ≤ a * x.1 + b * y.1 := by
    calc
      ui = a * ui + b * ui := by rw [← add_mul, hab, one_mul]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hx.1 ha)
        (mul_le_mul_of_nonneg_left hy.1 hb)
  exact ⟨hlo,
    by nlinarith [mul_nonneg ha (sub_nonneg.mpr hx.2.1),
      mul_nonneg hb (sub_nonneg.mpr hy.2.1)],
    add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha hx.2.2)
      (mul_nonpos_of_nonneg_of_nonpos hb hy.2.2)⟩

/-- A classical field has one Lipschitz constant on the whole triangle.
Paper `e1a0fd5`, lines 220–275; Christodoulou CPAM p. 1157. -/
theorem classical_lipschitz {ui : ℝ} {f : ℝ × ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (closedTriangle ui)) :
    ∃ L, LipschitzOnWith L f (closedTriangle ui) :=
  hf.exists_lipschitzOnWith (by decide) (classical_triangle_convex ui)
    (classical_triangle_compact ui)

/-- Restriction of a Lipschitz field to an outgoing segment.
Paper `e1a0fd5`, lines 220–275. -/
theorem classical_lipschitz_out {ui u a b : ℝ} {f : ℝ × ℝ → ℝ} {L : NNReal}
    (hf : LipschitzOnWith L f (closedTriangle ui))
    (hs : outSeg u a b ⊆ closedTriangle ui) :
    LipschitzOnWith L (fun v => f (u, v)) (Icc a b) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  simpa using hf.dist_le_mul (u, x) (hs (a := (u, x)) ⟨mem_singleton u, hx⟩)
    (u, y) (hs (a := (u, y)) ⟨mem_singleton u, hy⟩)

/-- Restriction of a Lipschitz field to an incoming segment.
Paper `e1a0fd5`, lines 220–275. -/
theorem classical_lipschitz_in {ui v a b : ℝ} {f : ℝ × ℝ → ℝ} {L : NNReal}
    (hf : LipschitzOnWith L f (closedTriangle ui))
    (hs : inSeg v a b ⊆ closedTriangle ui) :
    LipschitzOnWith L (fun u => f (u, v)) (Icc a b) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  simpa using hf.dist_le_mul (x, v) (hs (a := (x, v)) ⟨hx, mem_singleton v⟩)
    (y, v) (hs (a := (y, v)) ⟨hy, mem_singleton v⟩)

/-- Outgoing traces of classical fields are AC, including axis endpoints.
Paper `e1a0fd5`, lines 220–275; Christodoulou CPAM p. 1157. -/
theorem classical_ac_out {ui u a b : ℝ} {f : ℝ × ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (closedTriangle ui)) (hab : a ≤ b)
    (hs : outSeg u a b ⊆ closedTriangle ui) :
    AbsolutelyContinuousOnInterval (fun v => f (u, v)) a b := by
  obtain ⟨L, hL⟩ := classical_lipschitz hf
  have hl := classical_lipschitz_out hL hs
  rw [← uIcc_of_le hab] at hl
  exact hl.absolutelyContinuousOnInterval

/-- Incoming traces of classical fields are AC, including axis endpoints.
Paper `e1a0fd5`, lines 220–275; Christodoulou CPAM p. 1157. -/
theorem classical_ac_in {ui v a b : ℝ} {f : ℝ × ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (closedTriangle ui)) (hab : a ≤ b)
    (hs : inSeg v a b ⊆ closedTriangle ui) :
    AbsolutelyContinuousOnInterval (fun u => f (u, v)) a b := by
  obtain ⟨L, hL⟩ := classical_lipschitz hf
  have hl := classical_lipschitz_in hL hs
  rw [← uIcc_of_le hab] at hl
  exact hl.absolutelyContinuousOnInterval

/-- FTC uses only AC and the interior pointwise derivative; no endpoint source continuity
is needed. Paper `e1a0fd5`, lines 66–84 and 222. -/
theorem classical_primitive {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (g x) x) : IntervalPrimitive f g a b :=
  ac_integral_eq_sub hab hf (Eventually.of_forall hd)

end AcExtensionPrinciple

end
