module

public import AcExtensionPrinciple.Weighted.ClassWeights
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

/-!
# Joint measurability from the local BV solution class

Paper `e1a0fd5`, `lem:weighted-radial-estimates`,
`equations.tex` lines 1196–1202. Characteristic BV and transverse
continuity justify Tonelli without a new solution-class hypothesis.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory

/-- Patch measurable extensions on a countable measurable cover.
Paper `e1a0fd5`, lines 1196–1202, measurability for Tonelli. -/
theorem measurable_piecewise_of_countable_extensions {ι : Type*} [Countable ι]
    {s : ι → Set (ℝ × ℝ)} {f : ℝ × ℝ → ℝ}
    (hs : ∀ i, MeasurableSet (s i))
    (hf : ∀ i, ∃ F : ℝ × ℝ → ℝ, Measurable F ∧ EqOn f F (s i)) :
    ∃ F : ℝ × ℝ → ℝ, Measurable F ∧ EqOn f F (⋃ i, s i) := by
  classical
  choose F hF heF using hf
  let D := ⋃ i, s i
  let G := D.piecewise f (fun _ => 0)
  have hD : MeasurableSet D := MeasurableSet.iUnion hs
  refine ⟨G, ?_, ?_⟩
  · intro t ht
    rw [show G = D.piecewise f (fun _ => 0) from rfl, piecewise_preimage, Set.ite]
    have he : D ∩ f ⁻¹' t = ⋃ i, s i ∩ F i ⁻¹' t := by
      ext p
      simp only [D, mem_inter_iff, mem_iUnion, mem_preimage]
      constructor
      · rintro ⟨⟨i, hi⟩, hp⟩
        exact ⟨i, hi, by rwa [← heF i hi]⟩
      · rintro ⟨i, hi, hp⟩
        exact ⟨⟨i, hi⟩, by rwa [heF i hi]⟩
    rw [inter_comm (f ⁻¹' t) D, he]
    exact (MeasurableSet.iUnion (fun i => (hs i).inter (hF i ht))).union
      ((measurable_const ht).diff hD)
  · intro p hp
    simp [G, D, hp]

/-- Clamp a real coordinate to a closed interval. Paper `e1a0fd5`,
lines 1196–1202, local BV measurability on rectangles. -/
@[expose] noncomputable def weightedClamp (a b x : ℝ) : ℝ := min (max x a) b

/-- The clamped coordinate belongs to its interval. Paper `e1a0fd5`,
lines 1196–1202, local BV measurability on rectangles. -/
theorem weightedClamp_mem {a b : ℝ} (hab : a ≤ b) (x : ℝ) :
    weightedClamp a b x ∈ Icc a b :=
  ⟨le_min (le_max_right _ _) hab, min_le_right _ _⟩

/-- Clamping preserves coordinates already in the interval. Paper `e1a0fd5`,
lines 1196–1202, local BV measurability on rectangles. -/
theorem weightedClamp_eq {a b x : ℝ} (hx : x ∈ Icc a b) : weightedClamp a b x = x := by
  simp [weightedClamp, max_eq_left hx.1, min_eq_left hx.2]

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- On every off-axis rectangle, ∂ᵤψ has a jointly measurable extension:
BV in u and the outgoing primitive in v give the Carathéodory argument.
Paper `e1a0fd5`, lines 1196–1202, Luk–Oh Definition 2.1(4). -/
theorem weighted_exists_measurable_dupsi_rectangle {a b c : ℝ}
    (hia : ui ≤ a) (hab : a ≤ b) (hbc : b < c) (hc0 : c ≤ 0) :
    ∃ F : ℝ × ℝ → ℝ, Measurable F ∧
      EqOn (fun p => S.dupsi p.1 p.2) F (Icc a b ×ˢ Icc c 0) := by
  have hb0 : b < 0 := hbc.trans_le hc0
  let K := Icc a b ×ˢ Icc c 0
  have hK : K ⊆ pastTriangle ui := fun p hp =>
    ⟨hia.trans hp.1.1, hp.1.2.trans_lt hb0, (hp.1.2.trans_lt (hbc.trans_le hp.2.1)).le, hp.2.2⟩
  obtain ⟨C, _, hvar⟩ := h.regularCenter.localBV.psi_variation K
    (isCompact_Icc.prod isCompact_Icc) hK
  let A := weightedClamp a b
  let V := weightedClamp c 0
  have hA (x : ℝ) : A x ∈ Icc a b := weightedClamp_mem hab x
  have hV (y : ℝ) : V y ∈ Icc c 0 := weightedClamp_mem hc0 y
  have hVm : Continuous V := (continuous_id.max continuous_const).min continuous_const
  have hAm : Monotone A := fun x y hxy => min_le_min_right b (max_le_max_right a hxy)
  have hcont (x : ℝ) : Continuous (fun y => S.dupsi (A x) (V y)) := by
    have hp := hA x
    have hac : AbsolutelyContinuousOnInterval (S.dupsi (A x)) c 0 := by
      apply intervalPrimitive_ac (g := fun y => S.radiusCoeff (A x) y * S.phi (A x) y) hc0
      intro z hz
      exact h.regularCenter.localBV.dupsi_out (A x) c z hz.1
        (outSeg_subset_offAxis (hia.trans hp.1) (hp.2.trans_lt hb0)
          (hp.2.trans_lt hbc) hz.2)
    have hc : ContinuousOn (S.dupsi (A x)) (Icc c 0) := by
      simpa only [uIcc_of_le hc0] using hac.continuousOn
    exact hc.comp_continuous hVm hV
  have hmeas (y : ℝ) : Measurable (fun x => S.dupsi (A x) (V y)) := by
    have hv := hV y
    have hb : eVariationOn (fun x => S.dupsi x (V y)) (Icc a b) ≤ ENNReal.ofReal C :=
      hvar (V y) a b hab (fun p hp => by
        change p.1 ∈ Icc a b ∧ p.2 = V y at hp
        exact ⟨hp.1, by rw [hp.2]; exact hv⟩)
    have hvcomp := eVariationOn.comp_le_of_monotoneOn (fun x => S.dupsi x (V y)) A
      (hAm.monotoneOn univ) (fun x _ => hA x)
    have hBV : BoundedVariationOn (fun x => S.dupsi (A x) (V y)) univ :=
      ((hvcomp.trans hb).trans_lt ENNReal.ofReal_lt_top).ne
    exact hBV.measurable
  let F := fun p : ℝ × ℝ => S.dupsi (A p.1) (V p.2)
  have hm := measurable_uncurry_of_continuous_of_measurable hcont hmeas
  refine ⟨F, hm.comp measurable_swap, ?_⟩
  intro p hp
  dsimp only [F, A, V]
  rw [weightedClamp_eq hp.1, weightedClamp_eq hp.2]

end StandingFull

end AcExtensionPrinciple

end
