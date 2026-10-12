module

public import AcExtensionPrinciple.Gauge.GluingFields
public import AcExtensionPrinciple.Solution.LocalBVFull

/-!
# Integral and variation gluing across an outgoing cone

Components for paper `e1a0fd5`, `equations.tex` lines 1411–1422.
Incoming segments crossing the cone concatenate at the shared trace. Outgoing
segments stay on one side. The transverse equations use off-axis segments.
-/

public section

namespace AcExtensionPrinciple

open Set
open scoped ENNReal

/-- Incoming primitive gluing for any two pointwise field quantities. Paper
`e1a0fd5`, `equations.tex` lines 1411–1422. -/
theorem glue_primitive_in {D₁ D₂ : Set (ℝ × ℝ)} {S₁ S₂ : SSFields}
    {qf qg : SSFields → ℝ → ℝ → ℝ} {c a b v : ℝ}
    (hd : ConeGluingDomains D₁ D₂ c) (he : FieldsAgreeOn (D₁ ∩ D₂) S₁ S₂)
    (hf : LocalQuantity qf) (hg : LocalQuantity qg) (hac : a ≤ c) (hcb : c ≤ b)
    (hs : inSeg v a b ⊆ D₁ ∪ D₂)
    (h₁ : IntervalPrimitive (fun u => qf S₁ u v) (fun u => qg S₁ u v) a c)
    (h₂ : IntervalPrimitive (fun u => qf S₂ u v) (fun u => qg S₂ u v) c b) :
    IntervalPrimitive (fun u => qf (S₁.glue S₂ c) u v)
      (fun u => qg (S₁.glue S₂ c) u v) a b := by
  have hleft (q : SSFields → ℝ → ℝ → ℝ) (hq : LocalQuantity q) :
      EqOn (fun u => q S₁ u v) (fun u => q (S₁.glue S₂ c) u v) (uIcc a c) := by
    intro u hu
    rw [uIcc_of_le hac] at hu
    exact (hq _ _ u v (glue_values_left (p := (u, v)) hd (hd.in_left hcb hs ⟨hu, by simp⟩))).symm
  have hright (q : SSFields → ℝ → ℝ → ℝ) (hq : LocalQuantity q) :
      EqOn (fun u => q S₂ u v) (fun u => q (S₁.glue S₂ c) u v) (uIcc c b) := by
    intro u hu
    rw [uIcc_of_le hcb] at hu
    exact (hq _ _ u v
      (glue_values_right (p := (u, v)) hd he (hd.in_right hac hs ⟨hu, by simp⟩))).symm
  exact (h₁.congr (hleft _ hf) (hleft _ hg)).trans
    (h₂.congr (hright _ hf) (hright _ hg))

/-- An outgoing segment in the union lies wholly in its selected side. Paper
`e1a0fd5`, `equations.tex` lines 1411–1422. -/
theorem glue_primitive_out {D₁ D₂ : Set (ℝ × ℝ)} {S₁ S₂ : SSFields}
    {qf qg : SSFields → ℝ → ℝ → ℝ} {c a b u : ℝ}
    (hd : ConeGluingDomains D₁ D₂ c) (he : FieldsAgreeOn (D₁ ∩ D₂) S₁ S₂)
    (hf : LocalQuantity qf) (hg : LocalQuantity qg) (hab : a ≤ b)
    (hs : outSeg u a b ⊆ D₁ ∪ D₂)
    (h₁ : outSeg u a b ⊆ D₁ → IntervalPrimitive (qf S₁ u) (qg S₁ u) a b)
    (h₂ : outSeg u a b ⊆ D₂ → IntervalPrimitive (qf S₂ u) (qg S₂ u) a b) :
    IntervalPrimitive (qf (S₁.glue S₂ c) u) (qg (S₁.glue S₂ c) u) a b := by
  by_cases hu : u ≤ c
  · have hseg : outSeg u a b ⊆ D₁ := by
      intro p hp
      rcases hs hp with h | h
      · exact h
      · have hpu : p.1 = u := hp.1
        exact hd.cut_left p (le_antisymm (hpu.symm ▸ hu) (hd.right p h)) h
    apply (h₁ hseg).congr
    · intro v hv
      rw [uIcc_of_le hab] at hv
      exact (hf _ _ u v (glue_values_left (p := (u, v)) hd (hseg ⟨by simp, hv⟩))).symm
    · intro v hv
      rw [uIcc_of_le hab] at hv
      exact (hg _ _ u v (glue_values_left (p := (u, v)) hd (hseg ⟨by simp, hv⟩))).symm
  · have hseg : outSeg u a b ⊆ D₂ := by
      intro p hp
      rcases hs hp with h | h
      · have hpu : p.1 = u := hp.1
        exact (hu (hpu ▸ hd.left p h)).elim
      · exact h
    apply (h₂ hseg).congr
    · intro v hv
      rw [uIcc_of_le hab] at hv
      exact (hf _ _ u v (glue_values_right (p := (u, v)) hd he (hseg ⟨by simp, hv⟩))).symm
    · intro v hv
      rw [uIcc_of_le hab] at hv
      exact (hg _ _ u v (glue_values_right (p := (u, v)) hd he (hseg ⟨by simp, hv⟩))).symm

section Components

variable {D₁ D₂ : Set (ℝ × ℝ)} {S₁ S₂ : SSFields} {c : ℝ}
  (hd : ConeGluingDomains D₁ D₂ c) (he : FieldsAgreeOn (D₁ ∩ D₂) S₁ S₂)
  (h₁ : LocalBVSolutionFull D₁ S₁) (h₂ : LocalBVSolutionFull D₂ S₂)

include hd he h₁ h₂

/-- Glued radius in identity per segment. Paper `e1a0fd5`,
`equations.tex` lines 1411–1422. -/
theorem glue_radius_in {v a b : ℝ}
    (hac : a ≤ c) (hcb : c ≤ b)
    (hs : inSeg v a b ⊆ D₁ ∪ D₂) :
    IntervalPrimitive (fun u => (S₁.glue S₂ c).r u v)
      (fun u => (S₁.glue S₂ c).nu u v) a b := by
  exact glue_primitive_in hd he local_r local_nu hac hcb hs
    (h₁.radius_in v a c hac (hd.in_left hcb hs))
    (h₂.radius_in v c b hcb (hd.in_right hac hs))

/-- Glued psi in identity per segment. Paper `e1a0fd5`,
`equations.tex` lines 1411–1422. -/
theorem glue_psi_in {v a b : ℝ}
    (hac : a ≤ c) (hcb : c ≤ b)
    (hs : inSeg v a b ⊆ D₁ ∪ D₂) :
    IntervalPrimitive (fun u => (S₁.glue S₂ c).r u v * (S₁.glue S₂ c).phi u v)
      (fun u => (S₁.glue S₂ c).dupsi u v) a b := by
  exact glue_primitive_in hd he (local_r.mul local_phi) local_dupsi hac hcb hs
    (h₁.psi_in v a c hac (hd.in_left hcb hs))
    (h₂.psi_in v c b hcb (hd.in_right hac hs))

/-- Glued mass in identity per segment. Paper `e1a0fd5`,
`equations.tex` lines 1411–1422. -/
theorem glue_mass_in {v a b : ℝ}
    (hac : a ≤ c) (hcb : c ≤ b)
    (hs : inSeg v a b ⊆ D₁ ∪ D₂) :
    IntervalPrimitive (fun u => (S₁.glue S₂ c).m u v)
      (fun u => (S₁.glue S₂ c).massU u v) a b := by
  exact glue_primitive_in hd he local_m local_massU hac hcb hs
    (h₁.mass_in v a c hac (hd.in_left hcb hs))
    (h₂.mass_in v c b hcb (hd.in_right hac hs))

/-- Glued lam in identity per segment. Paper `e1a0fd5`,
`equations.tex` lines 1411–1422. -/
theorem glue_lam_in {v a b : ℝ}
    (hac : a ≤ c) (hcb : c ≤ b)
    (hs : inSeg v a b ⊆ offAxis (D₁ ∪ D₂)) :
    IntervalPrimitive (fun u => (S₁.glue S₂ c).lam u v)
      (fun u => (S₁.glue S₂ c).radiusCoeff u v) a b := by
  have hs' : inSeg v a b ⊆ offAxis D₁ ∪ offAxis D₂ := by
    rwa [← offAxis_union]
  have he' : FieldsAgreeOn (offAxis D₁ ∩ offAxis D₂) S₁ S₂ :=
    fun p hp => he p ⟨hp.1.1, hp.2.1⟩
  exact glue_primitive_in hd.offAxis he' local_lam local_radiusCoeff hac hcb hs'
    (h₁.lam_in v a c hac (hd.offAxis.in_left hcb hs'))
    (h₂.lam_in v c b hcb (hd.offAxis.in_right hac hs'))

/-- Glued dvpsi in identity per segment. Paper `e1a0fd5`,
`equations.tex` lines 1411–1422. -/
theorem glue_dvpsi_in {v a b : ℝ}
    (hac : a ≤ c) (hcb : c ≤ b)
    (hs : inSeg v a b ⊆ offAxis (D₁ ∪ D₂)) :
    IntervalPrimitive (fun u => (S₁.glue S₂ c).dvpsi u v)
      (fun u => (S₁.glue S₂ c).radiusCoeff u v * (S₁.glue S₂ c).phi u v) a b := by
  have hs' : inSeg v a b ⊆ offAxis D₁ ∪ offAxis D₂ := by
    rwa [← offAxis_union]
  have he' : FieldsAgreeOn (offAxis D₁ ∩ offAxis D₂) S₁ S₂ :=
    fun p hp => he p ⟨hp.1.1, hp.2.1⟩
  exact glue_primitive_in hd.offAxis he' local_dvpsi (local_radiusCoeff.mul local_phi) hac hcb hs'
    (h₁.dvpsi_in v a c hac (hd.offAxis.in_left hcb hs'))
    (h₂.dvpsi_in v c b hcb (hd.offAxis.in_right hac hs'))

/-- Glued radius out identity per segment. Paper `e1a0fd5`,
`equations.tex` lines 1411–1422. -/
theorem glue_radius_out {u a b : ℝ}
    (hab : a ≤ b)
    (hs : outSeg u a b ⊆ D₁ ∪ D₂) :
    IntervalPrimitive (fun v => (S₁.glue S₂ c).r u v)
      (fun v => (S₁.glue S₂ c).lam u v) a b := by
  exact glue_primitive_out hd he local_r local_lam hab hs
    (fun h => h₁.radius_out u a b hab h) (fun h => h₂.radius_out u a b hab h)

/-- Glued psi out identity per segment. Paper `e1a0fd5`,
`equations.tex` lines 1411–1422. -/
theorem glue_psi_out {u a b : ℝ}
    (hab : a ≤ b)
    (hs : outSeg u a b ⊆ D₁ ∪ D₂) :
    IntervalPrimitive (fun v => (S₁.glue S₂ c).r u v * (S₁.glue S₂ c).phi u v)
      (fun v => (S₁.glue S₂ c).dvpsi u v) a b := by
  exact glue_primitive_out hd he (local_r.mul local_phi) local_dvpsi hab hs
    (fun h => h₁.psi_out u a b hab h) (fun h => h₂.psi_out u a b hab h)

/-- Glued mass out identity per segment. Paper `e1a0fd5`,
`equations.tex` lines 1411–1422. -/
theorem glue_mass_out {u a b : ℝ}
    (hab : a ≤ b)
    (hs : outSeg u a b ⊆ D₁ ∪ D₂) :
    IntervalPrimitive (fun v => (S₁.glue S₂ c).m u v)
      (fun v => (S₁.glue S₂ c).massV u v) a b := by
  exact glue_primitive_out hd he local_m local_massV hab hs
    (fun h => h₁.mass_out u a b hab h) (fun h => h₂.mass_out u a b hab h)

/-- Glued nu out identity per segment. Paper `e1a0fd5`,
`equations.tex` lines 1411–1422. -/
theorem glue_nu_out {u a b : ℝ}
    (hab : a ≤ b)
    (hs : outSeg u a b ⊆ offAxis (D₁ ∪ D₂)) :
    IntervalPrimitive (fun v => (S₁.glue S₂ c).nu u v)
      (fun v => (S₁.glue S₂ c).radiusCoeff u v) a b := by
  have hs' : outSeg u a b ⊆ offAxis D₁ ∪ offAxis D₂ := by
    rwa [← offAxis_union]
  have he' : FieldsAgreeOn (offAxis D₁ ∩ offAxis D₂) S₁ S₂ :=
    fun p hp => he p ⟨hp.1.1, hp.2.1⟩
  exact glue_primitive_out hd.offAxis he' local_nu local_radiusCoeff hab hs'
    (fun h => h₁.nu_out u a b hab h) (fun h => h₂.nu_out u a b hab h)

/-- Glued dupsi out identity per segment. Paper `e1a0fd5`,
`equations.tex` lines 1411–1422. -/
theorem glue_dupsi_out {u a b : ℝ}
    (hab : a ≤ b)
    (hs : outSeg u a b ⊆ offAxis (D₁ ∪ D₂)) :
    IntervalPrimitive (fun v => (S₁.glue S₂ c).dupsi u v)
      (fun v => (S₁.glue S₂ c).radiusCoeff u v * (S₁.glue S₂ c).phi u v) a b := by
  have hs' : outSeg u a b ⊆ offAxis D₁ ∪ offAxis D₂ := by
    rwa [← offAxis_union]
  have he' : FieldsAgreeOn (offAxis D₁ ∩ offAxis D₂) S₁ S₂ :=
    fun p hp => he p ⟨hp.1.1, hp.2.1⟩
  exact glue_primitive_out hd.offAxis he' local_dupsi (local_radiusCoeff.mul local_phi) hab hs'
    (fun h => h₁.dupsi_out u a b hab h) (fun h => h₂.dupsi_out u a b hab h)

end Components

/-- Exact variation additivity across a shared endpoint. Paper `e1a0fd5`,
`equations.tex` lines 1439–1443. -/
theorem variation_add_across (f : ℝ → ℝ) {a b c : ℝ} (hac : a ≤ c) (hcb : c ≤ b) :
    eVariationOn f (Icc a c) + eVariationOn f (Icc c b) = eVariationOn f (Icc a b) := by
  simpa using eVariationOn.Icc_add_Icc f (s := univ) hac hcb (mem_univ c)

/-- Variation of a glued incoming field is the sum of the two variations, with
agreement at the cut preventing a jump term. Paper `e1a0fd5`, 1315–1319, 1329–1333. -/
theorem variation_glue_in {D₁ D₂ : Set (ℝ × ℝ)} {S₁ S₂ : SSFields}
    {q : SSFields → ℝ → ℝ → ℝ} {c a b v : ℝ}
    (hd : ConeGluingDomains D₁ D₂ c) (he : FieldsAgreeOn (D₁ ∩ D₂) S₁ S₂)
    (hq : LocalQuantity q) (hac : a ≤ c) (hcb : c ≤ b)
    (hs : inSeg v a b ⊆ D₁ ∪ D₂) :
    eVariationOn (fun u => q (S₁.glue S₂ c) u v) (Icc a b) =
      eVariationOn (fun u => q S₁ u v) (Icc a c) +
        eVariationOn (fun u => q S₂ u v) (Icc c b) := by
  have hleft : EqOn (fun u => q (S₁.glue S₂ c) u v) (fun u => q S₁ u v) (Icc a c) :=
    fun u hu => hq _ _ u v (glue_values_left (p := (u, v)) hd (hd.in_left hcb hs ⟨hu, by simp⟩))
  have hright : EqOn (fun u => q (S₁.glue S₂ c) u v) (fun u => q S₂ u v) (Icc c b) :=
    fun u hu => hq _ _ u v
      (glue_values_right (p := (u, v)) hd he (hd.in_right hac hs ⟨hu, by simp⟩))
  rw [← variation_add_across _ hac hcb, eVariationOn.congr hleft, eVariationOn.congr hright]

end AcExtensionPrinciple

end
