module

public import AcExtensionPrinciple.Renormalized.ClassLemma31

/-!
# Lemma 3.2 at class level

This module packages Lemma 3.2 for the solution class.
Paper `e1a0fd5`, `equations.tex` lines 1082–1125.
All geometric, scalar, measurability, and cone integrability premises are
discharged. Only the stated Lemma 2.2 conclusions remain as inputs.
The Lemma 2.2 inputs are supplied by `StandingFull.sectionThreeDatumInputs` in
`Integration/DatumRepresentative.lean`, and consumed in `Integration/SectionThree.lean`.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped ENNReal

/-- The transported datum and remainder conclusions of Lemma 3.2.
Paper `e1a0fd5`, `lem:renormalized-splitting-bounds`, lines 1082–1125. -/
structure RenormalizedSplittingPackage (ui : ℝ) (S : SSFields) (q : ℝ → ℝ → ℝ) : Prop where
  initial_integrable : IntegrableOn (S.renormalizedDerivative q ui) (Ioc ui 0)
  initial_value : ∀ v ∈ Icc ui 0, S.renormalizedInitial q ui ui v = S.renormalizedDerivative q ui v
  initial_ae : ∀ v a b, a ≤ b → ui ≤ a → b < 0 → b < v → v ≤ 0 →
    ∀ᵐ x, x ∈ Ioo a b → HasDerivAt (fun u => S.renormalizedInitial q ui u v)
      (S.incomingFlux x v * S.renormalizedInitial q ui x v) x
  initial_primitive : ∀ v a b, a ≤ b → ui ≤ a → b < 0 → b < v → v ≤ 0 →
    IntervalPrimitive (fun u => S.renormalizedInitial q ui u v)
      (fun u => S.incomingFlux u v * S.renormalizedInitial q ui u v) a b
  initial_domination : ∀ p ∈ pastTriangle ui,
    |S.renormalizedInitial q ui p.1 p.2| ≤
      ((1 / initialGap ui S) / Real.exp (-Bstar ui S)) * |S.renormalizedDerivative q ui p.2|
  remainder_zero : ∀ v ∈ Icc ui 0, S.renormalizedRemainder q ui ui v = 0
  remainder_ae : ∀ v a b, a ≤ b → ui ≤ a → b < 0 → b < v → v ≤ 0 →
    ∀ᵐ x, x ∈ Ioo a b → HasDerivAt (fun u => S.renormalizedRemainder q ui u v)
      (S.incomingFlux x v * S.renormalizedRemainder q ui x v +
        (3 * S.nu x v / S.r x v) * S.dvphi x v * S.renormalizedInteraction x v) x
  remainder_primitive : ∀ v a b, a ≤ b → ui ≤ a → b < 0 → b < v → v ≤ 0 →
    IntervalPrimitive (fun u => S.renormalizedRemainder q ui u v)
      (fun u => S.incomingFlux u v * S.renormalizedRemainder q ui u v +
        (3 * S.nu u v / S.r u v) * S.dvphi u v * S.renormalizedInteraction u v) a b
  remainder_pointwise : ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ pastTriangle ui, p.1 < p.2 →
    |S.renormalizedRemainder q ui p.1 p.2| ≤
      C * ∫ s in ui..p.1, -S.nu s p.2 / S.r s p.2 ^ 2 ∧
    |S.renormalizedRemainder q ui p.1 p.2| ≤ C / S.r p.1 p.2
  energy_uniform : ∃ C : ℝ, 0 ≤ C ∧ ∀ u, ui ≤ u → u < 0 →
    IntegrableOn (S.renormalizedRemainderEnergy q ui u) (Ioc u 0) ∧
    (∫ v in Ioc u 0, S.renormalizedRemainderEnergy q ui u v) ≤
      C * ∫ v in Ioc u 0, |S.renormalizedRemainder q ui u v|

namespace SectionThreeDatumInputs

variable {ui : ℝ} {S : SSFields} {q : ℝ → ℝ → ℝ}
    (D : SectionThreeDatumInputs ui S q) (h : StandingFull ui S)
include D h

/-- Uniform remainder pointwise estimate after discharging the source and
flux bounds. Paper `e1a0fd5`, `eq:renormalized-remainder-pointwise`, lines 1107–1120. -/
theorem remainder_pointwise_uniform :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ pastTriangle ui, p.1 < p.2 →
      |S.renormalizedRemainder q ui p.1 p.2| ≤
        C * ∫ s in ui..p.1, -S.nu s p.2 / S.r s p.2 ^ 2 ∧
      |S.renormalizedRemainder q ui p.1 p.2| ≤ C / S.r p.1 p.2 := by
  obtain ⟨M, hM0, hM⟩ := h.section3_uniform_coefficients
  let C₀ := 3 * M * (1 + 2 * M ^ 2)
  let Λ := Bstar ui S + Real.log (1 / initialGap ui S)
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  refine ⟨C₀ * Real.exp Λ, mul_nonneg hC₀ (Real.exp_pos _).le, fun p hp huv => ?_⟩
  have E := D.renormalized_equations_package h
  have hAC := h.renormalizedRemainder_ac_of_incoming_ac q hp.1 le_rfl hp.2.1 huv hp.2.2.2
    (E.incoming_ac p.2 ui p.1 hp.1 le_rfl hp.2.1 huv hp.2.2.2)
  have hODE := h.renormalizedRemainder_ae_of_incoming_transport q hp.1 le_rfl hp.2.1 huv hp.2.2.2
    (E.incoming_ae p.2 ui p.1 hp.1 le_rfl hp.2.1 huv hp.2.2.2)
  apply h.renormalizedRemainder_bound_of_transport hp huv hC₀ hAC hODE
    (h.partial_incoming_flux_le hp huv)
  intro x hx
  have hxp : (x, p.2) ∈ pastTriangle ui :=
    ⟨hx.1, hx.2.trans_lt hp.2.1, (hx.2.trans_lt huv).le, hp.2.2.2⟩
  exact renormalized_source_bound (h.r_pos hxp (hx.2.trans_lt huv)) (h.lam_pos hxp)
    (h.lam_bounds hxp).2 (h.nu_neg hxp) (hM (x, p.2) hxp).1 (hM (x, p.2) hxp).2.2

/-- Finite weighted initial energy with one constant for all proper cones,
and no L² hypothesis on the initial derivative. Paper `e1a0fd5`,
`eq:renormalized-initial-energy`, lines 1112–1124. -/
theorem remainder_energy_uniform :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u, ui ≤ u → u < 0 →
      IntegrableOn (S.renormalizedRemainderEnergy q ui u) (Ioc u 0) ∧
      (∫ v in Ioc u 0, S.renormalizedRemainderEnergy q ui u v) ≤
        C * ∫ v in Ioc u 0, |S.renormalizedRemainder q ui u v| := by
  obtain ⟨M, hM0, hM⟩ := D.remainder_pointwise_uniform h
  let c := initialGap ui S * Real.exp (-Bstar ui S)
  let d := Real.exp (-Bstar ui S)
  have hc : 0 < c := mul_pos h.initialGap_pos (Real.exp_pos _)
  have hd : 0 < d := Real.exp_pos _
  refine ⟨M / (c ^ 2 * d), div_nonneg hM0 (mul_nonneg (sq_nonneg _) hd.le), fun u hu hu0 => ?_⟩
  apply h.renormalized_initial_energy_of_l1_and_geometric hu hu0 hc hd
  · intro v hv
    have hp : (u, v) ∈ pastTriangle ui := ⟨hu, hu0, hv.1.le, hv.2⟩
    exact ⟨h.mass_gap_lower hp, (h.lam_bounds hp).1⟩
  · intro v hv
    have hp : (u, v) ∈ pastTriangle ui := ⟨hu, hu0, hv.1.le, hv.2⟩
    have hb := (hM (u, v) hp hv.1).2
    have he := (le_div_iff₀ (h.r_pos hp hv.1)).mp hb
    simpa only [mul_comm] using he
  · exact (D.splitting_cone_integrable h hu hu0).2.2
  · exact (D.splitting_fields_measurable h hu hu0).2.2

/-- Lemma 3.2 as a package with only the stated Lemma 2.2 conclusions as
remaining inputs. Paper `e1a0fd5`, `lem:renormalized-splitting-bounds`,
lines 1082–1125. -/
theorem renormalized_splitting_package : RenormalizedSplittingPackage ui S q := by
  have E := D.renormalized_equations_package h
  refine {
    initial_integrable := (D.splitting_cone_integrable h le_rfl h.initial_negative).1
    initial_value := ?_
    initial_ae := fun v a b hab ha hb0 hbv hv0 => h.renormalizedInitial_ae q hab ha hb0 hbv hv0
    initial_primitive := fun v a b hab ha hb0 hbv hv0 =>
      h.renormalizedInitial_primitive q hab ha hb0 hbv hv0
    initial_domination := h.section3_initial_domination q
    remainder_zero := fun v hv => h.renormalizedRemainder_initial q hv
    remainder_ae := ?_, remainder_primitive := ?_
    remainder_pointwise := D.remainder_pointwise_uniform h
    energy_uniform := D.remainder_energy_uniform h }
  · intro v hv
    have he := h.renormalizedRemainder_initial q hv
    unfold SSFields.renormalizedRemainder at he
    linarith
  · intro v a b hab ha hb0 hbv hv0
    exact h.renormalizedRemainder_ae_of_incoming_transport q hab ha hb0 hbv hv0
      (E.incoming_ae v a b hab ha hb0 hbv hv0)
  · intro v a b hab ha hb0 hbv hv0
    exact h.renormalizedRemainder_primitive_of_incoming_transport q hab ha hb0 hbv hv0
      (E.incoming_ac v a b hab ha hb0 hbv hv0) (E.incoming_ae v a b hab ha hb0 hbv hv0)

end SectionThreeDatumInputs

end AcExtensionPrinciple

end
