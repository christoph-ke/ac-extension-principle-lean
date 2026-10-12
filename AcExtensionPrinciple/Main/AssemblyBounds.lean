module

public import AcExtensionPrinciple.Main.AssemblyCore

/-!
# Compactly localized continuation bounds

Paper `e1a0fd5`, `equations.tex` lines 222 and 1411–1422. The early proper
triangle and a finite new triangle control each compact set. Incoming
variation adds at their common selected-cone endpoint.
-/

public section

namespace AcExtensionPrinciple

open Set
open scoped ENNReal

/-- The early off-axis region is a proper compact triangle with its axis
removed. Paper `e1a0fd5`, lines 1411–1422. -/
@[expose] def earlyContinuationDomain (ui ū : ℝ) : Set (ℝ × ℝ) :=
  {p | ui ≤ p.1 ∧ p.1 ≤ ū ∧ p.1 < p.2 ∧ p.2 ≤ 0}

section

variable {ui ū B : ℝ} {S N P : SSFields} (hū : ū ∈ Ioo ui 0) (hB : 0 ≤ B)
  (hold : FieldsAgreeOn (pastTriangle ui \ axis ui) P S)
  (hnew : FieldsAgreeOn (lateContinuationDomain ū) P N)

include hū hB hold hnew

/-- Uniform outgoing variation is controlled by one side of the patch.
Paper `e1a0fd5`, lines 222 and 1411–1422. -/
theorem continuation_variation_out {q : SSFields → ℝ → ℝ → ℝ} (hq : LocalQuantity q)
    {L R : ℝ≥0∞}
    (hl : ∀ u, eVariationOn (q S u) {v | (u, v) ∈ earlyContinuationDomain ui ū} ≤ L)
    (hr : ∀ u, eVariationOn (q N u)
      {v | (u, v) ∈ lateContinuationDomain ū ∧ v ≤ B} ≤ R) (u : ℝ) :
    eVariationOn (q P u) {v | (u, v) ∈ earlyContinuationDomain ui ū ∪
      {p | p ∈ lateContinuationDomain ū ∧ p.2 ≤ B}} ≤ L + R := by
  by_cases hu : ū ≤ u
  · apply le_trans ?_ ((hr u).trans le_add_self)
    apply variation_transfer
    intro v hv
    have hn : (u, v) ∈ lateContinuationDomain ū ∧ v ≤ B := by
      rcases hv with ho | hn
      · exact ⟨⟨hu, ho.2.2.1⟩, ho.2.2.2.trans hB⟩
      · exact hn
    exact ⟨hn, hq P N u v (hnew (u, v) hn.1)⟩
  · apply le_trans ?_ ((hl u).trans le_self_add)
    apply variation_transfer
    intro v hv
    have ho : (u, v) ∈ earlyContinuationDomain ui ū := by
      rcases hv with ho | hn
      · exact ho
      · exact (hu hn.1.1).elim
    have hpoint : (u, v) ∈ pastTriangle ui \ axis ui :=
      past_offaxis_iff.mpr ⟨ho.1, ho.2.1.trans_lt hū.2, ho.2.2.1, ho.2.2.2⟩
    exact ⟨ho, hq P S u v (hold (u, v) hpoint)⟩

/-- Uniform incoming variation adds across the selected cone, whose shared
value prevents a jump contribution. Paper `e1a0fd5`, lines 222 and 1411–1422. -/
theorem continuation_variation_in {q : SSFields → ℝ → ℝ → ℝ} (hq : LocalQuantity q)
    {L R : ℝ≥0∞}
    (hl : ∀ v, eVariationOn (fun u => q S u v) {u | (u, v) ∈ earlyContinuationDomain ui ū} ≤ L)
    (hr : ∀ v, eVariationOn (fun u => q N u v)
      {u | (u, v) ∈ lateContinuationDomain ū ∧ v ≤ B} ≤ R) (v : ℝ) :
    eVariationOn (fun u => q P u v) {u | (u, v) ∈ earlyContinuationDomain ui ū ∪
      {p | p ∈ lateContinuationDomain ū ∧ p.2 ≤ B}} ≤ L + R := by
  have hleft : eVariationOn (fun u => q P u v) {u | (u, v) ∈ earlyContinuationDomain ui ū} ≤ L := by
    apply le_trans ?_ (hl v)
    apply variation_transfer
    intro u hu
    exact ⟨hu, hq P S u v (hold (u, v) (past_offaxis_iff.mpr
      ⟨hu.1, hu.2.1.trans_lt hū.2, hu.2.2.1, hu.2.2.2⟩))⟩
  have hright : eVariationOn (fun u => q P u v)
      {u | (u, v) ∈ lateContinuationDomain ū ∧ v ≤ B} ≤ R := by
    apply le_trans ?_ (hr v)
    exact variation_transfer (fun u hu => ⟨hu, hq P N u v (hnew (u, v) hu.1)⟩)
  by_cases hv : v ≤ ū
  · apply le_trans ?_ (hleft.trans le_self_add)
    apply eVariationOn.mono
    intro u hu
    rcases hu with ho | hn
    · exact ho
    · exact (not_lt_of_ge (hv.trans hn.1.1) hn.1.2).elim
  · by_cases hv0 : 0 < v
    · apply le_trans ?_ (hright.trans le_add_self)
      apply eVariationOn.mono
      intro u hu
      rcases hu with ho | hn
      · exact (not_le_of_gt hv0 ho.2.2.2).elim
      · exact hn
    · have hv' : ū < v := not_le.mp hv
      have hv0' : v ≤ 0 := not_lt.mp hv0
      have he : {u | (u, v) ∈ earlyContinuationDomain ui ū ∪
          {p | p ∈ lateContinuationDomain ū ∧ p.2 ≤ B}} =
          {u | (u, v) ∈ earlyContinuationDomain ui ū} ∪
            {u | (u, v) ∈ lateContinuationDomain ū ∧ v ≤ B} := by ext u; rfl
      rw [he, eVariationOn.union _
        (show IsGreatest {u | (u, v) ∈ earlyContinuationDomain ui ū} ū from
          ⟨⟨hū.1.le, le_rfl, hv', hv0'⟩, fun u hu => hu.2.1⟩)
        (show IsLeast {u | (u, v) ∈ lateContinuationDomain ū ∧ v ≤ B} ū from
          ⟨⟨⟨le_rfl, hv'⟩, hv0'.trans hB⟩, fun u hu => hu.1.1⟩)]
      exact add_le_add hleft hright

/-- Early and late bounds give globally uniform bounds on their finite
union. Paper `e1a0fd5`, lines 222 and 1411–1422. -/
theorem continuation_bounds_union
    (h₁ : ChrBVBoundsOn univ (earlyContinuationDomain ui ū) S)
    (h₂ : ChrBVBoundsOn univ {p | p ∈ lateContinuationDomain ū ∧ p.2 ≤ B} N) :
    ChrBVBoundsOn univ (earlyContinuationDomain ui ū ∪
      {p | p ∈ lateContinuationDomain ū ∧ p.2 ≤ B}) P := by
  obtain ⟨c₁, N₁, hc₁, hb₁⟩ := h₁.expansion_bounds
  obtain ⟨c₂, N₂, hc₂, hb₂⟩ := h₂.expansion_bounds
  obtain ⟨C₁, ho₁, hi₁⟩ := h₁.variation_bounds
  obtain ⟨C₂, ho₂, hi₂⟩ := h₂.variation_bounds
  simp only [univ_inter] at ho₁ ho₂ hi₁ hi₂
  let E := ENNReal.ofReal C₁ + ENNReal.ofReal C₂
  have hE : E ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
  have he : ENNReal.ofReal E.toReal = E := ENNReal.ofReal_toReal hE
  refine ⟨⟨min c₁ c₂, max N₁ N₂, lt_min hc₁ hc₂, ?_⟩, E.toReal, ?_, ?_⟩
  · intro p hp
    rcases hp.2 with ho | hn
    · have hpoint : p ∈ pastTriangle ui \ axis ui :=
        past_offaxis_iff.mpr ⟨ho.1, ho.2.1.trans_lt hū.2, ho.2.2.1, ho.2.2.2⟩
      have hh := hb₁ p ⟨mem_univ _, ho⟩
      rw [local_lam P S _ _ (hold p hpoint), local_nu P S _ _ (hold p hpoint)]
      exact ⟨(min_le_left _ _).trans hh.1, hh.2.trans (le_max_left _ _)⟩
    · have hh := hb₂ p ⟨mem_univ _, hn⟩
      rw [local_lam P N _ _ (hnew p hn.1), local_nu P N _ _ (hnew p hn.1)]
      exact ⟨(min_le_right _ _).trans hh.1, hh.2.trans (le_max_right _ _)⟩
  · intro u
    simp only [univ_inter, he]
    exact ⟨continuation_variation_out hū hB hold hnew local_lam
        (fun u => (ho₁ u).1) (fun u => (ho₂ u).1) u,
      continuation_variation_out hū hB hold hnew local_phi
        (fun u => (ho₁ u).2.1) (fun u => (ho₂ u).2.1) u,
      continuation_variation_out hū hB hold hnew local_theta
        (fun u => (ho₁ u).2.2) (fun u => (ho₂ u).2.2) u⟩
  · intro v
    simp only [univ_inter, he]
    exact ⟨continuation_variation_in hū hB hold hnew local_nu
        (fun v => (hi₁ v).1) (fun v => (hi₂ v).1) v,
      continuation_variation_in hū hB hold hnew local_phi
        (fun v => (hi₁ v).2.1) (fun v => (hi₂ v).2.1) v,
      continuation_variation_in hū hB hold hnew local_zeta
        (fun v => (hi₁ v).2.2) (fun v => (hi₂ v).2.2) v⟩

end

/-- Bounds decrease under restriction of the full characteristic portions
K ∩ D, even when both K and D change. Paper `e1a0fd5`, lines 222 and 1411–1422. -/
theorem ChrBVBoundsOn.mono_portions {K L D E : Set (ℝ × ℝ)} {S : SSFields}
    (h : ChrBVBoundsOn L E S) (hsub : K ∩ D ⊆ L ∩ E) : ChrBVBoundsOn K D S := by
  obtain ⟨⟨c, N, hc, hb⟩, C, hout, hin⟩ := h
  refine ⟨⟨c, N, hc, fun p hp => hb p (hsub hp)⟩, C, ?_, ?_⟩
  · intro u
    have hs : {v | (u, v) ∈ K ∩ D} ⊆ {v | (u, v) ∈ L ∩ E} := fun v hv => hsub hv
    exact ⟨(eVariationOn.mono _ hs).trans (hout u).1,
      (eVariationOn.mono _ hs).trans (hout u).2.1,
      (eVariationOn.mono _ hs).trans (hout u).2.2⟩
  · intro v
    have hs : {u | (u, v) ∈ K ∩ D} ⊆ {u | (u, v) ∈ L ∩ E} := fun u hu => hsub hu
    exact ⟨(eVariationOn.mono _ hs).trans (hin v).1,
      (eVariationOn.mono _ hs).trans (hin v).2.1,
      (eVariationOn.mono _ hs).trans (hin v).2.2⟩

end AcExtensionPrinciple

end
