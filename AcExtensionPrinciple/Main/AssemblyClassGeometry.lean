module

public import AcExtensionPrinciple.Main.AssemblyGauge

/-!
# Characteristic cover and field agreement for the continuation patch

Paper `e1a0fd5`, `equations.tex` lines 1411–1422. Every characteristic
segment is contained in one chart or splits once at the selected cone.
-/

public section

namespace AcExtensionPrinciple

open Set

/-- The seven-field conjunction is equivalent to equality of field values.
Paper `e1a0fd5`, `thm:main`, line 133 and lines 1411–1422. -/
theorem fieldsAgreeAt_iff_values {S₁ S₂ : SSFields} {p : ℝ × ℝ} :
    FieldsAgreeAt S₁ S₂ p ↔ S₁.values p.1 p.2 = S₂.values p.1 p.2 := by
  constructor
  · rintro ⟨hr, hp, hm, hl, hn, hd, hz⟩
    simp only [SSFields.values, hr, hp, hm, hl, hn, hd, hz]
  · intro he
    exact ⟨congrArg FieldValues.r he, congrArg FieldValues.phi he,
      congrArg FieldValues.m he, congrArg FieldValues.lam he, congrArg FieldValues.nu he,
      congrArg FieldValues.dvpsi he, congrArg FieldValues.dupsi he⟩

/-- Coordinates characterize the old off-axis domain. Paper `e1a0fd5`,
`eq:past-triangle`, lines 107–110 and 1411–1422. -/
theorem past_offaxis_iff {ui u v : ℝ} :
    (u, v) ∈ pastTriangle ui \ axis ui ↔ ui ≤ u ∧ u < 0 ∧ u < v ∧ v ≤ 0 := by
  constructor
  · rintro ⟨hp, ha⟩
    refine ⟨hp.1, hp.2.1, lt_of_le_of_ne hp.2.2.1 ?_, hp.2.2.2⟩
    intro he
    exact ha ⟨hp.1, hp.2.1, he.symm⟩
  · rintro ⟨hu, hu0, huv, hv0⟩
    exact ⟨⟨hu, hu0, huv.le, hv0⟩, fun ha => (ne_of_lt huv) ha.2.2.symm⟩

/-- The old domain has the equivalent generic off-axis representation.
Paper `e1a0fd5`, lines 107–110 and 1411–1422. -/
theorem past_offaxis_eq (ui : ℝ) : pastTriangle ui \ axis ui = offAxis (pastTriangle ui) := by
  ext p
  obtain ⟨u, v⟩ := p
  rw [past_offaxis_iff]
  simp only [offAxis, mem_sdiff, mem_ofPred_eq, pastTriangle]
  constructor
  · rintro ⟨hui, hu0, huv, hv0⟩
    exact ⟨⟨hui, hu0, huv.le, hv0⟩, ne_of_lt huv⟩
  · rintro ⟨⟨hui, hu0, huv, hv0⟩, hne⟩
    exact ⟨hui, hu0, lt_of_le_of_ne huv hne, hv0⟩

/-- Primitive agreement plus complete derivative agreement identifies the
patch with the pulled-back development on the entire late region.
Paper `e1a0fd5`, lines 1411–1422. -/
theorem continuationFields_values_late {ui ū : ℝ} {S Sdev : SSFields} {T dT : ℝ → ℝ}
    (he : ∀ u v, ū ≤ u → u < v → v ≤ 0 →
      FieldsAgreeAt S (Sdev.pullback T dT) (u, v))
    {p : ℝ × ℝ} (hp : p ∈ lateContinuationDomain ū) :
    (continuationFields ui S Sdev T dT).values p.1 p.2 =
      (Sdev.pullback T dT).values p.1 p.2 := by
  by_cases ho : p ∈ pastTriangle ui \ axis ui
  · have hh := he p.1 p.2 hp.1 hp.2 ho.1.2.2.2
    exact (fieldsAgreeAt_iff_values.mp (continuationFields_agree ui S Sdev T dT ho)).trans
      (fieldsAgreeAt_iff_values.mp hh)
  · exact fieldsAgreeAt_iff_values.mp (continuationFields_new ui S Sdev T dT ho)

/-- An outgoing segment belongs wholly to one continuation chart.
Paper `e1a0fd5`, lines 1411–1422. -/
theorem continuation_out_cover {ui ū u a b : ℝ} (hū : ū ∈ Ioo ui 0)
    (hs : outSeg u a b ⊆ continuationDomain ui ū) :
    outSeg u a b ⊆ pastTriangle ui \ axis ui ∨
      outSeg u a b ⊆ lateContinuationDomain ū := by
  by_cases hu : ū ≤ u
  · right
    intro p hp
    have hp1 : p.1 = u := hp.1
    exact ⟨hp1.symm ▸ hu, (continuationDomain_coordinates hū (hs hp)).2⟩
  · left
    intro p hp
    rcases hs hp with ho | hn
    · exact ho
    · have hp1 : p.1 = u := hp.1
      exact (hu (hp1 ▸ hn.1)).elim

/-- Incoming segments beginning after the cut belong to the development.
Paper `e1a0fd5`, lines 1411–1422. -/
theorem continuation_in_late {ui ū v a b : ℝ} (hū : ū ∈ Ioo ui 0) (ha : ū ≤ a)
    (hs : inSeg v a b ⊆ continuationDomain ui ū) :
    inSeg v a b ⊆ lateContinuationDomain ū := by
  intro p hp
  exact ⟨ha.trans hp.1.1, (continuationDomain_coordinates hū (hs hp)).2⟩

/-- A segment starting before the cut and ending at or before it lies in the
old domain. The initial point fixes v ≤ 0. Paper `e1a0fd5`, lines 1411–1422. -/
theorem continuation_in_old {ui ū v a b : ℝ} (hū : ū ∈ Ioo ui 0)
    (hab : a ≤ b) (ha : a < ū) (hb : b ≤ ū)
    (hs : inSeg v a b ⊆ continuationDomain ui ū) :
    inSeg v a b ⊆ pastTriangle ui \ axis ui := by
  have hv0 : v ≤ 0 := by
    rcases hs (show (a, v) ∈ inSeg v a b from ⟨⟨le_rfl, hab⟩, by simp⟩) with ho | hn
    · exact ho.1.2.2.2
    · exact (not_le_of_gt ha hn.1).elim
  intro p hp
  have hcoord := continuationDomain_coordinates hū (hs hp)
  have hpv : p.2 = v := hp.2
  have ho : (p.1, p.2) ∈ pastTriangle ui \ axis ui := past_offaxis_iff.mpr
    ⟨hcoord.1, (hp.1.2.trans hb).trans_lt hū.2, hcoord.2, hpv.symm ▸ hv0⟩
  exact ho

/-- Incoming segments crossing the cut split into an old and a new segment.
Paper `e1a0fd5`, lines 1411–1422. -/
theorem continuation_in_split {ui ū v a b : ℝ} (hū : ū ∈ Ioo ui 0)
    (ha : a < ū) (hb : ū ≤ b) (hs : inSeg v a b ⊆ continuationDomain ui ū) :
    inSeg v a ū ⊆ pastTriangle ui \ axis ui ∧
      inSeg v ū b ⊆ lateContinuationDomain ū := by
  constructor
  · exact continuation_in_old hū ha.le ha le_rfl
      ((prod_mono_left (Icc_subset_Icc le_rfl hb)).trans hs)
  · exact continuation_in_late hū le_rfl
      ((prod_mono_left (Icc_subset_Icc ha.le le_rfl)).trans hs)

/-- AC concatenates across a shared endpoint. Paper `e1a0fd5`, lines 1411–1422. -/
theorem ac_concat {f : ℝ → ℝ} {a c b : ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    (hl : AbsolutelyContinuousOnInterval f a c)
    (hr : AbsolutelyContinuousOnInterval f c b) : AbsolutelyContinuousOnInterval f a b := by
  have hprim {x y : ℝ} (hh : AbsolutelyContinuousOnInterval f x y) :
      IntervalPrimitive f (deriv f) x y :=
    ⟨hh.intervalIntegrable_deriv, hh.integral_deriv_eq_sub.symm⟩
  apply intervalPrimitive_ac (g := deriv f) (hac.trans hcb)
  intro x hx
  by_cases hxc : x ≤ c
  · exact hprim (hl.mono (by
      simpa only [uIcc_of_le hx.1, uIcc_of_le hac] using Icc_subset_Icc le_rfl hxc))
  · have hcx := (not_le.mp hxc).le
    exact (hprim hl).trans (hprim (hr.mono (by
      simpa only [uIcc_of_le hcx, uIcc_of_le hcb] using Icc_subset_Icc le_rfl hx.2)))

end AcExtensionPrinciple

end
