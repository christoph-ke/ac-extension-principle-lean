module

public import AcExtensionPrinciple.Integration.SmallConesFromSmallMass
public import AcExtensionPrinciple.Main.Theorem1Assembly

/-!
# Continuation assembled from observation and energy estimates

Paper `e1a0fd5`, `thm:main`, equations.tex lines 112–146 and 1390–1445.
The continuation assembly consumes exactly the small-cone sequence
obtained from the small-mass estimate and Proposition 3.4 energy.
These premises are proved in `Integration/ObservabilityComplete.lean` and
`Weighted/Prop34.lean`, respectively.
E1 and E2 remain the original explicit external trust boundaries.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory
open scoped ENNReal

/-- The complete continuation and terminal BV conclusions, with Proposition 3.5's small-cone premise
discharged. The remaining inputs are exactly the small-mass estimate, finite coercive energy, E1 and
E2. Paper `e1a0fd5`, `thm:main`, lines 112–146 and 1390–1445. -/
theorem main_of_small_mass_and_energy (hE1 : SmallBVExistence) (hE2 : BVUniqueness)
    (ui : ℝ) (S : SSFields) (h : StandingFull ui S)
    (hsmall : PropA4.SmallMassEstimate h.integrationCylinderK)
    (henergy : ∃ a : ℝ, ui ≤ a ∧ a < 0 ∧
      (∫⁻ u in Ioo a 0, ∫⁻ v in Ioc u 0,
        ENNReal.ofReal (weightedRemainderDensity S (u, v) *
          |S.renormalizedRemainder S.radialDatumDerivative ui u v| ^ 2)) < ⊤) :
    (∃ ū ∈ Ioo ui 0, ∃ Splus : SSFields,
      LocalChristodoulouBV (continuationDomain ui ū) (Ici ui) Splus ∧
      ∀ p ∈ pastTriangle ui \ axis ui, FieldsAgreeAt Splus S p) ∧
    eVariationOn (fun u => S.dupsi u 0 / S.nu u 0) (Ico ui 0) ≠ ⊤ ∧
    eVariationOn (fun u => S.phi u 0) (Ico ui 0) ≠ ⊤ ∧
    eVariationOn (fun u => Real.log (-S.nu u 0)) (Ico ui 0) ≠ ⊤ ∧
    eVariationOn (fun u => S.nu u 0) (Ico ui 0) ≠ ⊤ ∧
    eVariationOn (fun u => S.dupsi u 0) (Ico ui 0) ≠ ⊤ := by
  exact main_of_small_cones hE1 hE2 ui S h
    (h.small_outgoing_cones_of_small_mass_and_energy hsmall henergy)

/-- The exact main statement follows from producers of the small-mass and
energy estimates. They are supplied by `StandingFull.integration_small_mass_estimate`
in `Integration/ObservabilityComplete.lean` and `StandingFull.proposition34`
in `Weighted/Prop34.lean`. Paper `e1a0fd5`, `thm:main`,
lines 112–146, 1324–1330 and 1390–1445. -/
theorem main_statement_of_small_mass_and_energy
    (hsmall : ∀ ui S (h : StandingFull ui S),
      PropA4.SmallMassEstimate h.integrationCylinderK)
    (henergy : ∀ ui S, StandingFull ui S → ∃ a : ℝ, ui ≤ a ∧ a < 0 ∧
      (∫⁻ u in Ioo a 0, ∫⁻ v in Ioc u 0,
        ENNReal.ofReal (weightedRemainderDensity S (u, v) *
          |S.renormalizedRemainder S.radialDatumDerivative ui u v| ^ 2)) < ⊤) :
    MainTheoremStatement :=
  main_statement_of_small_cones (fun ui S h =>
    h.small_outgoing_cones_of_small_mass_and_energy (hsmall ui S h) (henergy ui S h))

end AcExtensionPrinciple

end
