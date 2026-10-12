module

public import AcExtensionPrinciple.Main.AssemblyClassGeometry

/-!
# Characteristic integral identities for the continuation patch

Paper `e1a0fd5`, `equations.tex` lines 1411–1422. Incoming segments
concatenate at the selected cone; outgoing segments use a single chart.
-/

public section

namespace AcExtensionPrinciple

open Set

section

variable {ui ū : ℝ} {S N P : SSFields} (hū : ū ∈ Ioo ui 0)
  (hold : FieldsAgreeOn (pastTriangle ui \ axis ui) P S)
  (hnew : FieldsAgreeOn (lateContinuationDomain ū) P N)

include hū hold hnew

/-- Outgoing primitive transport through the two-chart cover.
Paper `e1a0fd5`, lines 1411–1422. -/
theorem continuation_primitive_out {qf qg : SSFields → ℝ → ℝ → ℝ}
    (hf : LocalQuantity qf) (hg : LocalQuantity qg)
    (h₁ : ∀ u a b, a ≤ b → outSeg u a b ⊆ pastTriangle ui \ axis ui →
      IntervalPrimitive (qf S u) (qg S u) a b)
    (h₂ : ∀ u a b, a ≤ b → outSeg u a b ⊆ lateContinuationDomain ū →
      IntervalPrimitive (qf N u) (qg N u) a b)
    {u a b : ℝ} (hab : a ≤ b) (hs : outSeg u a b ⊆ continuationDomain ui ū) :
    IntervalPrimitive (qf P u) (qg P u) a b := by
  rcases continuation_out_cover hū hs with hleft | hright
  · apply (h₁ u a b hab hleft).congr
    · intro v hv
      rw [uIcc_of_le hab] at hv
      exact (hf P S u v (hold (u, v) (hleft ⟨by simp, hv⟩))).symm
    · intro v hv
      rw [uIcc_of_le hab] at hv
      exact (hg P S u v (hold (u, v) (hleft ⟨by simp, hv⟩))).symm
  · apply (h₂ u a b hab hright).congr
    · intro v hv
      rw [uIcc_of_le hab] at hv
      exact (hf P N u v (hnew (u, v) (hright ⟨by simp, hv⟩))).symm
    · intro v hv
      rw [uIcc_of_le hab] at hv
      exact (hg P N u v (hnew (u, v) (hright ⟨by simp, hv⟩))).symm

/-- Incoming primitive transport, including segments crossing the cut.
Paper `e1a0fd5`, lines 1411–1422. -/
theorem continuation_primitive_in {qf qg : SSFields → ℝ → ℝ → ℝ}
    (hf : LocalQuantity qf) (hg : LocalQuantity qg)
    (h₁ : ∀ v a b, a ≤ b → inSeg v a b ⊆ pastTriangle ui \ axis ui →
      IntervalPrimitive (fun u => qf S u v) (fun u => qg S u v) a b)
    (h₂ : ∀ v a b, a ≤ b → inSeg v a b ⊆ lateContinuationDomain ū →
      IntervalPrimitive (fun u => qf N u v) (fun u => qg N u v) a b)
    {v a b : ℝ} (hab : a ≤ b) (hs : inSeg v a b ⊆ continuationDomain ui ū) :
    IntervalPrimitive (fun u => qf P u v) (fun u => qg P u v) a b := by
  have hleft {a b : ℝ} (hab : a ≤ b) (hs : inSeg v a b ⊆ pastTriangle ui \ axis ui) :
      IntervalPrimitive (fun u => qf P u v) (fun u => qg P u v) a b := by
    apply (h₁ v a b hab hs).congr
    · intro u hu
      rw [uIcc_of_le hab] at hu
      exact (hf P S u v (hold (u, v) (hs ⟨hu, by simp⟩))).symm
    · intro u hu
      rw [uIcc_of_le hab] at hu
      exact (hg P S u v (hold (u, v) (hs ⟨hu, by simp⟩))).symm
  have hright {a b : ℝ} (hab : a ≤ b) (hs : inSeg v a b ⊆ lateContinuationDomain ū) :
      IntervalPrimitive (fun u => qf P u v) (fun u => qg P u v) a b := by
    apply (h₂ v a b hab hs).congr
    · intro u hu
      rw [uIcc_of_le hab] at hu
      exact (hf P N u v (hnew (u, v) (hs ⟨hu, by simp⟩))).symm
    · intro u hu
      rw [uIcc_of_le hab] at hu
      exact (hg P N u v (hnew (u, v) (hs ⟨hu, by simp⟩))).symm
  by_cases ha : ū ≤ a
  · exact hright hab (continuation_in_late hū ha hs)
  · have ha' : a < ū := not_le.mp ha
    by_cases hb : b ≤ ū
    · exact hleft hab (continuation_in_old hū hab ha' hb hs)
    · obtain ⟨hseg₁, hseg₂⟩ := continuation_in_split hū ha' (not_le.mp hb).le hs
      exact (hleft ha'.le hseg₁).trans (hright (not_le.mp hb).le hseg₂)

/-- Outgoing scalar AC is preserved by the chart cover.
Paper `e1a0fd5`, lines 222 and 1411–1422. -/
theorem continuation_scalar_ac_out
    (h₁ : ∀ u a b, a ≤ b → outSeg u a b ⊆ pastTriangle ui \ axis ui →
      AbsolutelyContinuousOnInterval (S.phi u) a b)
    (h₂ : ∀ u a b, a ≤ b → outSeg u a b ⊆ lateContinuationDomain ū →
      AbsolutelyContinuousOnInterval (N.phi u) a b)
    {u a b : ℝ} (hab : a ≤ b) (hs : outSeg u a b ⊆ continuationDomain ui ū) :
    AbsolutelyContinuousOnInterval (P.phi u) a b := by
  rcases continuation_out_cover hū hs with hl | hr
  · apply (h₁ u a b hab hl).congr
    intro v hv
    rw [uIcc_of_le hab] at hv
    exact (local_phi P S u v (hold (u, v) (hl ⟨by simp, hv⟩))).symm
  · apply (h₂ u a b hab hr).congr
    intro v hv
    rw [uIcc_of_le hab] at hv
    exact (local_phi P N u v (hnew (u, v) (hr ⟨by simp, hv⟩))).symm

/-- Incoming scalar AC concatenates at the identified scalar trace.
Paper `e1a0fd5`, lines 222 and 1411–1422. -/
theorem continuation_scalar_ac_in
    (h₁ : ∀ v a b, a ≤ b → inSeg v a b ⊆ pastTriangle ui \ axis ui →
      AbsolutelyContinuousOnInterval (fun u => S.phi u v) a b)
    (h₂ : ∀ v a b, a ≤ b → inSeg v a b ⊆ lateContinuationDomain ū →
      AbsolutelyContinuousOnInterval (fun u => N.phi u v) a b)
    {v a b : ℝ} (hab : a ≤ b) (hs : inSeg v a b ⊆ continuationDomain ui ū) :
    AbsolutelyContinuousOnInterval (fun u => P.phi u v) a b := by
  have hleft {a b : ℝ} (hab : a ≤ b) (hs : inSeg v a b ⊆ pastTriangle ui \ axis ui) :
      AbsolutelyContinuousOnInterval (fun u => P.phi u v) a b := by
    apply (h₁ v a b hab hs).congr
    intro u hu
    rw [uIcc_of_le hab] at hu
    exact (local_phi P S u v (hold (u, v) (hs ⟨hu, by simp⟩))).symm
  have hright {a b : ℝ} (hab : a ≤ b) (hs : inSeg v a b ⊆ lateContinuationDomain ū) :
      AbsolutelyContinuousOnInterval (fun u => P.phi u v) a b := by
    apply (h₂ v a b hab hs).congr
    intro u hu
    rw [uIcc_of_le hab] at hu
    exact (local_phi P N u v (hnew (u, v) (hs ⟨hu, by simp⟩))).symm
  by_cases ha : ū ≤ a
  · exact hright hab (continuation_in_late hū ha hs)
  · have ha' : a < ū := not_le.mp ha
    by_cases hb : b ≤ ū
    · exact hleft hab (continuation_in_old hū hab ha' hb hs)
    · obtain ⟨hseg₁, hseg₂⟩ := continuation_in_split hū ha' (not_le.mp hb).le hs
      exact ac_concat ha'.le (not_le.mp hb).le (hleft ha'.le hseg₁) (hright (not_le.mp hb).le hseg₂)

end

end AcExtensionPrinciple

end
