module

public import AcExtensionPrinciple.Main.AssemblyContinuity
public import AcExtensionPrinciple.Main.AssemblyPrimitives

/-!
# Christodoulou core of the continuation

Paper `e1a0fd5`, `equations.tex` lines 1411–1422. The old and new fields
agree on their entire overlap. Characteristic primitives, scalar AC,
right continuity and regular-axis conditions therefore assemble exactly.
-/

public section

namespace AcExtensionPrinciple

open Set

/-- Seven-field overlap agreement assembles all core class clauses.
Paper `e1a0fd5`, lines 222 and 1411–1422. Source cores and agreement will be
discharged by the standing class and the selected E1 development. -/
theorem continuation_core_of_late_core {ui ū : ℝ} {S N P : SSFields}
    (hū : ū ∈ Ioo ui 0)
    (hold : FieldsAgreeOn (pastTriangle ui \ axis ui) P S)
    (hnew : FieldsAgreeOn (lateContinuationDomain ū) P N)
    (h₁ : ChrBVCore (pastTriangle ui \ axis ui) (Ico ui 0) S)
    (h₂ : ChrBVCore (lateContinuationDomain ū) (Ici ū) N) :
    ChrBVCore (continuationDomain ui ū) (Ici ui) P := by
  have haxis (a : ℝ) (ha : a ∈ Ici ui) :=
    continuation_axis_conditions hū hold hnew h₁ h₂ ha
  exact {
    off_axis := fun p hp => (continuationDomain_coordinates hū hp).2
    radius_out := fun _ _ _ hab hs => continuation_primitive_out hū hold hnew
      local_r local_lam h₁.radius_out h₂.radius_out hab hs
    radius_in := fun _ _ _ hab hs => continuation_primitive_in hū hold hnew
      local_r local_nu h₁.radius_in h₂.radius_in hab hs
    psi_out := fun _ _ _ hab hs => continuation_primitive_out hū hold hnew
      (local_r.mul local_phi) local_dvpsi h₁.psi_out h₂.psi_out hab hs
    psi_in := fun _ _ _ hab hs => continuation_primitive_in hū hold hnew
      (local_r.mul local_phi) local_dupsi h₁.psi_in h₂.psi_in hab hs
    mass_out := fun _ _ _ hab hs => continuation_primitive_out hū hold hnew
      local_m local_massV h₁.mass_out h₂.mass_out hab hs
    mass_in := fun _ _ _ hab hs => continuation_primitive_in hū hold hnew
      local_m local_massU h₁.mass_in h₂.mass_in hab hs
    lam_in := fun _ _ _ hab hs => continuation_primitive_in hū hold hnew
      local_lam local_radiusCoeff h₁.lam_in h₂.lam_in hab hs
    nu_out := fun _ _ _ hab hs => continuation_primitive_out hū hold hnew
      local_nu local_radiusCoeff h₁.nu_out h₂.nu_out hab hs
    dvpsi_in := fun _ _ _ hab hs => continuation_primitive_in hū hold hnew
      local_dvpsi (local_radiusCoeff.mul local_phi) h₁.dvpsi_in h₂.dvpsi_in hab hs
    dupsi_out := fun _ _ _ hab hs => continuation_primitive_out hū hold hnew
      local_dupsi (local_radiusCoeff.mul local_phi) h₁.dupsi_out h₂.dupsi_out hab hs
    scalar_ac_out := fun _ _ _ hab hs => continuation_scalar_ac_out hū hold hnew
      h₁.scalar_ac_out h₂.scalar_ac_out hab hs
    scalar_ac_in := fun _ _ _ hab hs => continuation_scalar_ac_in hū hold hnew
      h₁.scalar_ac_in h₂.scalar_ac_in hab hs
    radius_axis_limit := fun a ha => (haxis a ha).1
    mass_axis_limit := fun a ha => (haxis a ha).2.1
    expansion_axis_limit := fun a ha => (haxis a ha).2.2.1
    scalar_axis_variation := fun a ha => (haxis a ha).2.2.2.1
    psi_axis_limit := fun a ha => (haxis a ha).2.2.2.2
    lam_right_cont := fun p hp => continuation_right_cont_out hū hold hnew
      local_lam h₁.lam_right_cont h₂.lam_right_cont hp
    theta_right_cont := fun p hp => continuation_right_cont_out hū hold hnew
      local_theta h₁.theta_right_cont h₂.theta_right_cont hp
    nu_right_cont := fun p hp => continuation_right_cont_in hū hold hnew
      local_nu h₁.nu_right_cont h₂.nu_right_cont hp
    zeta_right_cont := fun p hp => continuation_right_cont_in hū hold hnew
      local_zeta h₁.zeta_right_cont h₂.zeta_right_cont hp }

/-- The actual representative-preserving patch has the complete core.
Paper `e1a0fd5`, `thm:main`, line 133 and lines 1411–1422. -/
theorem StandingFull.continuationFields_core {ui ū : ℝ} {S Sdev : SSFields}
    (h : StandingFull ui S) (hū : ū ∈ Ioo ui 0) {T dT : ℝ → ℝ}
    (he : ∀ u v, ū ≤ u → u < v → v ≤ 0 →
      FieldsAgreeAt S (Sdev.pullback T dT) (u, v))
    (hnew : ChrBVCore (lateContinuationDomain ū) (Ici ū) (Sdev.pullback T dT)) :
    ChrBVCore (continuationDomain ui ū) (Ici ui) (continuationFields ui S Sdev T dT) := by
  apply continuation_core_of_late_core hū
    (fun p hp => fieldsAgreeAt_iff_values.mp (continuationFields_agree ui S Sdev T dT hp))
    (fun _ hp => continuationFields_values_late he hp) _ hnew
  apply h.regularCenter.chr_core
  · rw [past_offaxis_eq]
  · intro a ha
    exact ⟨ha.1, ha.2, rfl⟩

end AcExtensionPrinciple

end
