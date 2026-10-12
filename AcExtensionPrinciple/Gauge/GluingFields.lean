module

public import AcExtensionPrinciple.Gauge.Primitive

/-!
# Pointwise and domain components of gluing across an outgoing cone

Components for paper `e1a0fd5`, `equations.tex` lines 1411–1422.
The common boundary is represented explicitly; domain membership at the cut
must pass in both directions. No rectangular-domain assumption is imposed.
-/

public section

namespace AcExtensionPrinciple

open Set

/-- Seven field values at a point. Paper `e1a0fd5`, `equations.tex` 1315–1319. -/
structure FieldValues where
  r : ℝ
  phi : ℝ
  m : ℝ
  lam : ℝ
  nu : ℝ
  dvpsi : ℝ
  dupsi : ℝ

/-- Evaluating the primitive fields at a point. Paper `e1a0fd5`,
`equations.tex` lines 1411–1422. -/
@[expose] noncomputable def SSFields.values (S : SSFields) (u v : ℝ) : FieldValues :=
  ⟨S.r u v, S.phi u v, S.m u v, S.lam u v, S.nu u v, S.dvpsi u v, S.dupsi u v⟩

/-- Equality of all seven fields on a domain. Paper `e1a0fd5`,
`equations.tex` lines 1411–1422. -/
@[expose] def FieldsAgreeOn (D : Set (ℝ × ℝ)) (S₁ S₂ : SSFields) : Prop :=
  ∀ p ∈ D, S₁.values p.1 p.2 = S₂.values p.1 p.2

/-- A quantity determined by the fields at the same point. Paper `e1a0fd5`,
`equations.tex` lines 1411–1422. -/
@[expose] def LocalQuantity (q : SSFields → ℝ → ℝ → ℝ) : Prop :=
  ∀ S₁ S₂ u v, S₁.values u v = S₂.values u v → q S₁ u v = q S₂ u v

/-- Radius is a pointwise quantity. Paper `e1a0fd5`, lines 1411–1422. -/
theorem local_r : LocalQuantity SSFields.r := fun _ _ _ _ h => congrArg FieldValues.r h
/-- Scalar is a pointwise quantity. Paper `e1a0fd5`, lines 1411–1422. -/
theorem local_phi : LocalQuantity SSFields.phi := fun _ _ _ _ h => congrArg FieldValues.phi h
/-- Mass is a pointwise quantity. Paper `e1a0fd5`, lines 1411–1422. -/
theorem local_m : LocalQuantity SSFields.m := fun _ _ _ _ h => congrArg FieldValues.m h
/-- Outgoing expansion is pointwise. Paper `e1a0fd5`, lines 1411–1422. -/
theorem local_lam : LocalQuantity SSFields.lam := fun _ _ _ _ h => congrArg FieldValues.lam h
/-- Incoming expansion is pointwise. Paper `e1a0fd5`, lines 1411–1422. -/
theorem local_nu : LocalQuantity SSFields.nu := fun _ _ _ _ h => congrArg FieldValues.nu h
/-- Outgoing scalar derivative is pointwise. Paper `e1a0fd5`, lines 1411–1422. -/
theorem local_dvpsi : LocalQuantity SSFields.dvpsi := fun _ _ _ _ h => congrArg FieldValues.dvpsi h
/-- Incoming scalar derivative is pointwise. Paper `e1a0fd5`, lines 1411–1422. -/
theorem local_dupsi : LocalQuantity SSFields.dupsi := fun _ _ _ _ h => congrArg FieldValues.dupsi h

/-- Products of pointwise quantities are pointwise. Paper `e1a0fd5`, 1315–1319. -/
theorem LocalQuantity.mul {q q' : SSFields → ℝ → ℝ → ℝ}
    (h : LocalQuantity q) (h' : LocalQuantity q') :
    LocalQuantity (fun S u v => q S u v * q' S u v) := by
  intro S₁ S₂ u v he
  dsimp only
  rw [h S₁ S₂ u v he, h' S₁ S₂ u v he]

/-- Radius transport coefficient is pointwise. Paper `e1a0fd5`, 1315–1319. -/
theorem local_radiusCoeff : LocalQuantity SSFields.radiusCoeff := by
  intro S₁ S₂ u v h
  exact congrArg (fun p : FieldValues => massRatio p.r p.m * p.lam * p.nu /
    ((1 - massRatio p.r p.m) * p.r)) h

/-- Outgoing mass density is pointwise. Paper `e1a0fd5`, 1315–1319. -/
theorem local_massV : LocalQuantity SSFields.massV := by
  intro S₁ S₂ u v h
  exact congrArg (fun p : FieldValues => (1 - massRatio p.r p.m) *
    (p.dvpsi - p.lam * p.phi) ^ 2 / (2 * p.lam)) h

/-- Incoming mass density is pointwise. Paper `e1a0fd5`, 1315–1319. -/
theorem local_massU : LocalQuantity SSFields.massU := by
  intro S₁ S₂ u v h
  exact congrArg (fun p : FieldValues => (1 - massRatio p.r p.m) *
    (p.dupsi - p.nu * p.phi) ^ 2 / (2 * p.nu)) h

/-- The two domains lie on opposite sides, with the cut shared by both.
Paper `e1a0fd5`, `equations.tex` lines 1411–1422. -/
structure ConeGluingDomains (D₁ D₂ : Set (ℝ × ℝ)) (c : ℝ) : Prop where
  left : ∀ p ∈ D₁, p.1 ≤ c
  right : ∀ p ∈ D₂, c ≤ p.1
  cut_left : ∀ p, p.1 = c → p ∈ D₂ → p ∈ D₁
  cut_right : ∀ p, p.1 = c → p ∈ D₁ → p ∈ D₂

/-- Restricting away from the axis preserves the cut geometry. Paper `e1a0fd5`,
`equations.tex` lines 1411–1422. -/
theorem ConeGluingDomains.offAxis {D₁ D₂ : Set (ℝ × ℝ)} {c : ℝ}
    (h : ConeGluingDomains D₁ D₂ c) : ConeGluingDomains (offAxis D₁) (offAxis D₂) c where
  left p hp := h.left p hp.1
  right p hp := h.right p hp.1
  cut_left p he hp := ⟨h.cut_left p he hp.1, hp.2⟩
  cut_right p he hp := ⟨h.cut_right p he hp.1, hp.2⟩

/-- Off-axis restriction commutes with the union. Paper `e1a0fd5`, 1315–1319. -/
theorem offAxis_union (D₁ D₂ : Set (ℝ × ℝ)) :
    offAxis (D₁ ∪ D₂) = offAxis D₁ ∪ offAxis D₂ := by
  ext p
  simp [offAxis, or_and_right]

/-- Left half of an incoming segment belongs to the left domain. Paper
`e1a0fd5`, `equations.tex` lines 1411–1422. -/
theorem ConeGluingDomains.in_left {D₁ D₂ : Set (ℝ × ℝ)} {c a b v : ℝ}
    (h : ConeGluingDomains D₁ D₂ c) (hcb : c ≤ b)
    (hs : inSeg v a b ⊆ D₁ ∪ D₂) : inSeg v a c ⊆ D₁ := by
  intro p hp
  rcases hp with ⟨⟨hpa, hpc⟩, hpv⟩
  rcases hs ⟨⟨hpa, hpc.trans hcb⟩, hpv⟩ with h₁ | h₂
  · exact h₁
  · exact h.cut_left p (le_antisymm hpc (h.right p h₂)) h₂

/-- Right half of an incoming segment belongs to the right domain. Paper
`e1a0fd5`, `equations.tex` lines 1411–1422. -/
theorem ConeGluingDomains.in_right {D₁ D₂ : Set (ℝ × ℝ)} {c a b v : ℝ}
    (h : ConeGluingDomains D₁ D₂ c) (hac : a ≤ c)
    (hs : inSeg v a b ⊆ D₁ ∪ D₂) : inSeg v c b ⊆ D₂ := by
  intro p hp
  rcases hp with ⟨⟨hpc, hpb⟩, hpv⟩
  rcases hs ⟨⟨hac.trans hpc, hpb⟩, hpv⟩ with h₁ | h₂
  · exact h.cut_right p (le_antisymm (h.left p h₁) hpc) h₁
  · exact h₂

/-- Glued fields, taking the left trace on the cut. Paper `e1a0fd5`,
`equations.tex` lines 1411–1422. -/
@[expose] noncomputable def SSFields.glue (S₁ S₂ : SSFields) (c : ℝ) : SSFields where
  r u v := if u ≤ c then S₁.r u v else S₂.r u v
  phi u v := if u ≤ c then S₁.phi u v else S₂.phi u v
  m u v := if u ≤ c then S₁.m u v else S₂.m u v
  lam u v := if u ≤ c then S₁.lam u v else S₂.lam u v
  nu u v := if u ≤ c then S₁.nu u v else S₂.nu u v
  dvpsi u v := if u ≤ c then S₁.dvpsi u v else S₂.dvpsi u v
  dupsi u v := if u ≤ c then S₁.dupsi u v else S₂.dupsi u v

/-- All fields select the same side. Paper `e1a0fd5`, lines 1411–1422. -/
theorem SSFields.glue_values (S₁ S₂ : SSFields) (c u v : ℝ) :
    (S₁.glue S₂ c).values u v = if u ≤ c then S₁.values u v else S₂.values u v := by
  by_cases h : u ≤ c <;> simp [SSFields.values, SSFields.glue, h]

/-- Equality with the left fields throughout the left domain. Paper `e1a0fd5`,
`equations.tex` lines 1411–1422. -/
theorem glue_values_left {D₁ D₂ : Set (ℝ × ℝ)} {S₁ S₂ : SSFields} {c : ℝ}
    (hd : ConeGluingDomains D₁ D₂ c) {p : ℝ × ℝ} (hp : p ∈ D₁) :
    (S₁.glue S₂ c).values p.1 p.2 = S₁.values p.1 p.2 := by
  rw [SSFields.glue_values, ite_eq_left (hd.left p hp)]

/-- Equality with the right fields, using agreement on the shared cut. Paper
`e1a0fd5`, `equations.tex` lines 1411–1422. -/
theorem glue_values_right {D₁ D₂ : Set (ℝ × ℝ)} {S₁ S₂ : SSFields} {c : ℝ}
    (hd : ConeGluingDomains D₁ D₂ c) (he : FieldsAgreeOn (D₁ ∩ D₂) S₁ S₂)
    {p : ℝ × ℝ} (hp : p ∈ D₂) :
    (S₁.glue S₂ c).values p.1 p.2 = S₂.values p.1 p.2 := by
  rw [SSFields.glue_values]
  split_ifs with hc
  · exact he p ⟨hd.cut_left p (le_antisymm hc (hd.right p hp)) hp, hp⟩
  · rfl

/-- Concatenation of primitives across a cut. Paper `e1a0fd5`,
`equations.tex` lines 1411–1422. -/
theorem IntervalPrimitive.trans {f g : ℝ → ℝ} {a b c : ℝ}
    (h₁ : IntervalPrimitive f g a b) (h₂ : IntervalPrimitive f g b c) :
    IntervalPrimitive f g a c := by
  refine ⟨h₁.1.trans h₂.1, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals h₁.1 h₂.1, ← h₁.2, ← h₂.2]
  ring

end AcExtensionPrinciple

end
