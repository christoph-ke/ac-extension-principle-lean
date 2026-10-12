module

public import AcExtensionPrinciple.Renormalized.ClassConeIntegrability
public import AcExtensionPrinciple.Renormalized.ClassPrimitive

/-!
# Lemma 3.1 at class level

This module packages Lemma 3.1 for the solution class.
Paper `e1a0fd5`, `equations.tex` lines 1006–1078.
Its only inputs beyond the standing assumptions are exactly the three
Lemma 2.2 conclusions in `SectionThreeDatumInputs`.
The Lemma 2.2 inputs are supplied by `StandingFull.sectionThreeDatumInputs` in
`Integration/DatumRepresentative.lean`, and consumed in `Integration/SectionThree.lean`.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- Lemma 3.1, including its preceding cone Hardy estimate and the uniform
L¹ and incoming-amplitude conclusions used in its proof. Paper `e1a0fd5`,
`lem:renormalized-equations`, `eq:scalar-radial-hardy`, lines 1006–1078. -/
structure RenormalizedEquationsPackage (ui : ℝ) (S : SSFields) (q : ℝ → ℝ → ℝ) : Prop where
  radius_profile_ac : ∀ u, ui ≤ u → u < 0 →
    AbsolutelyContinuousOnInterval (S.coneRadiusProfile u) 0 (S.r u 0)
  scalar_radial_primitive : ∀ u v, ui ≤ u → u < 0 → u < v → v ≤ 0 →
    S.r u v / S.lam u v * S.dvphi u v =
      (1 / S.r u v) * ∫ ρ in 0..S.r u v, ρ * deriv (S.coneRadiusProfile u) ρ
  scalar_cone_hardy : ∀ u, ui ≤ u → u < 0 →
    (∫⁻ v in Ioc u 0,
      ENNReal.ofReal (S.lam u v * |S.r u v / S.lam u v * S.dvphi u v| / S.r u v)) ≤
        S.outgoingVariation u
  scalar_cone_primitive : ∀ u v, ui ≤ u → u < 0 → u < v → v ≤ 0 →
    S.r u v / S.lam u v * S.dvphi u v =
      (1 / S.r u v) * ∫ s in u..v, S.r u s * (S.lam u s * q u s)
  incoming_ac : ∀ v a b, a ≤ b → ui ≤ a → b < 0 → b < v → v ≤ 0 →
    AbsolutelyContinuousOnInterval (fun u => S.renormalizedDerivative q u v) a b
  incoming_ae : ∀ v a b, a ≤ b → ui ≤ a → b < 0 → b < v → v ≤ 0 →
    ∀ᵐ x, x ∈ Ioo a b → HasDerivAt (fun u => S.renormalizedDerivative q u v)
      (S.incomingFlux x v * S.renormalizedDerivative q x v +
        (3 * S.nu x v / S.r x v) * S.dvphi x v * S.renormalizedInteraction x v) x
  incoming_primitive : ∀ v a b, a ≤ b → ui ≤ a → b < 0 → b < v → v ≤ 0 →
    IntervalPrimitive (fun u => S.renormalizedDerivative q u v)
      (fun u => S.incomingFlux u v * S.renormalizedDerivative q u v +
        (3 * S.nu u v / S.r u v) * S.dvphi u v * S.renormalizedInteraction u v) a b
  radial_ae : ∀ u a b, a ≤ b → ui ≤ u → u < 0 → u < a → b ≤ 0 →
    ∀ᵐ x, x ∈ Ioo a b → HasDerivAt (S.renormalizedInteraction u)
      ((S.r u x / S.nu u x * S.duphi u x) * S.renormalizedDerivative q u x -
        (S.lam u x / S.r u x) * S.renormalizedInteraction u x) x
  radial_primitive : ∀ u a b, a ≤ b → ui ≤ u → u < 0 → u < a → b ≤ 0 →
    IntervalPrimitive (S.renormalizedInteraction u)
      (fun v => (S.r u v / S.nu u v * S.duphi u v) * S.renormalizedDerivative q u v -
        (S.lam u v / S.r u v) * S.renormalizedInteraction u v) a b
  incoming_amplitude_uniform : ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ pastTriangle ui,
    |S.r p.1 p.2 / S.nu p.1 p.2 * S.duphi p.1 p.2| ≤ C
  cone_l1_uniform : ∃ C : ℝ, 0 ≤ C ∧ ∀ u, ui ≤ u → u < 0 →
    (∫⁻ v in Ioc u 0, ENNReal.ofReal |S.renormalizedDerivative q u v|) ≤
      ENNReal.ofReal C * S.outgoingVariation u ∧
    IntegrableOn (S.renormalizedDerivative q u) (Ioc u 0)
  axis_primitive : ∀ u v, ui ≤ u → u < 0 → u < v → v ≤ 0 →
    S.renormalizedInteraction u v / S.r u v =
      (1 / S.r u v ^ 2) * ∫ s in u..v,
        S.r u s * (S.r u s / S.nu u s * S.duphi u s) * S.renormalizedDerivative q u s

namespace SectionThreeDatumInputs

variable {ui : ℝ} {S : SSFields} {q : ℝ → ℝ → ℝ}
    (D : SectionThreeDatumInputs ui S q) (h : StandingFull ui S)
include D h

/-- The scalar primitive with the prescribed q representative in the
original cone coordinate. Paper `e1a0fd5`,
`eq:scalar-radial-primitive`, lines 1006–1009, pulled back by `dr=λdv`. -/
theorem scalar_cone_primitive {u v : ℝ} (hu : ui ≤ u) (hu0 : u < 0)
    (huv : u < v) (hv0 : v ≤ 0) :
    S.r u v / S.lam u v * S.dvphi u v =
      (1 / S.r u v) * ∫ s in u..v, S.r u s * (S.lam u s * q u s) := by
  have hP : AbsolutelyContinuousOnInterval (S.outgoingDatum u) u v := by
    apply (D.outgoing_ac u hu hu0).mono
    rw [uIcc_of_le huv.le, uIcc_of_le hu0.le]
    exact Icc_subset_Icc le_rfl hv0
  have he := D.radial_eq u hu hu0
  change ∀ᵐ s ∂volume.restrict (Ioc u 0), q u s = S.radialDatumDerivative u s at he
  rw [ae_restrict_iff' measurableSet_Ioc] at he
  have hi : (∫ s in u..v, S.r u s * (S.lam u s * q u s)) =
      ∫ s in u..v, S.r u s * (S.lam u s * S.radialDatumDerivative u s) := by
    apply intervalIntegral.integral_congr_ae_restrict
    simp only [uIoc_of_le huv.le]
    filter_upwards [ae_restrict_of_ae he, ae_restrict_mem measurableSet_Ioc] with s hs hsI
    rw [hs ⟨hsI.1, hsI.2.trans hv0⟩]
  rw [hi]
  exact h.scalar_cone_primitive_of_ac_datum hu hu0 huv hv0 hP

/-- The interaction's axis primitive with every boundedness, local transport,
and integrability premise discharged. Paper `e1a0fd5`,
`eq:renormalized-radial-primitive`, lines 1038–1043 and 1078. -/
theorem renormalized_axis_primitive {u v : ℝ} (hu : ui ≤ u) (hu0 : u < 0)
    (huv : u < v) (hv0 : v ≤ 0) :
    S.renormalizedInteraction u v / S.r u v =
      (1 / S.r u v ^ 2) * ∫ s in u..v,
        S.r u s * (S.r u s / S.nu u s * S.duphi u s) * S.renormalizedDerivative q u s := by
  obtain ⟨M, _, hM⟩ := h.section3_uniform_coefficients
  apply h.renormalized_axis_primitive_of_local_transport hu hu0 huv hv0
    (M := 1 + 2 * M ^ 2)
  · intro s hs
    exact (hM (u, s) ⟨hu, hu0, hs.1.le, hs.2.le.trans hv0⟩).2.2
  · intro a ha
    apply h.radius_interaction_primitive_of_ac_datum ha.2.le hu hu0 ha.1 hv0
    · apply (D.outgoing_ac u hu hu0).mono
      rw [uIcc_of_le ha.2.le, uIcc_of_le hu0.le]
      exact Icc_subset_Icc ha.1.le hv0
    · exact D.outgoing_ae h ha.2.le hu hu0 ha.1.le hv0
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le huv.le]
    exact (D.radius_interaction_source_integrable h hu hu0).mono_set (Ioc_subset_Ioc_right hv0)

/-- Lemma 3.1 as a package with exactly Lemma 2.2's three conclusions as
remaining inputs. Paper `e1a0fd5`, `lem:renormalized-equations`,
`eq:renormalized-local-l1`, lines 1006–1078. -/
theorem renormalized_equations_package : RenormalizedEquationsPackage ui S q := by
  refine {
    radius_profile_ac := fun u hu hu0 =>
      h.coneRadiusProfile_ac_of_ac_datum hu hu0 (D.outgoing_ac u hu hu0)
    scalar_radial_primitive := fun u v hu hu0 huv hv0 =>
      h.scalar_radial_primitive_of_ac_datum hu hu0 huv hv0 (D.outgoing_ac u hu hu0)
    scalar_cone_hardy := fun u hu hu0 =>
      h.scalar_cone_hardy_of_ac_datum hu hu0 (D.outgoing_ac u hu hu0)
    scalar_cone_primitive := fun u v hu hu0 huv hv0 => D.scalar_cone_primitive h hu hu0 huv hv0
    incoming_ac := ?_, incoming_ae := ?_, incoming_primitive := ?_
    radial_ae := ?_, radial_primitive := ?_, incoming_amplitude_uniform := ?_
    cone_l1_uniform := D.renormalized_cone_l1 h
    axis_primitive := fun u v hu hu0 huv hv0 => D.renormalized_axis_primitive h hu hu0 huv hv0 }
  · intro v a b hab ha hb0 hbv hv0
    exact h.renormalizedDerivative_ac_in_of_ac_datum hab ha hb0 hbv hv0
      (D.incoming_ac hab ha hb0 hbv hv0)
  · intro v a b hab ha hb0 hbv hv0
    exact h.renormalized_incoming_ae_of_datum_transport hab ha hb0 hbv hv0
      (D.incoming_ae hab ha hb0 hbv hv0)
  · intro v a b hab ha hb0 hbv hv0
    exact h.renormalized_incoming_primitive_of_ac_datum hab ha hb0 hbv hv0
      (D.incoming_ac hab ha hb0 hbv hv0) (D.incoming_ae hab ha hb0 hbv hv0)
  · intro u a b hab hu hu0 hua hb0
    exact h.renormalized_radial_ae_of_datum_derivative hab hu hu0 hua hb0
      (D.outgoing_ae h hab hu hu0 hua.le hb0)
  · intro u a b hab hu hu0 hua hb0
    apply h.renormalized_radial_primitive_of_ac_datum hab hu hu0 hua hb0
    · apply (D.outgoing_ac u hu hu0).mono
      rw [uIcc_of_le hab, uIcc_of_le hu0.le]
      exact Icc_subset_Icc hua.le hb0
    · exact D.outgoing_ae h hab hu hu0 hua.le hb0
  · obtain ⟨M, hM0, hM⟩ := h.section3_uniform_coefficients
    exact ⟨2 * M, by positivity, fun p hp => (hM p hp).2.1⟩

end SectionThreeDatumInputs

end AcExtensionPrinciple

end
