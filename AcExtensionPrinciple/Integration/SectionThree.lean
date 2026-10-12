module

public import AcExtensionPrinciple.Integration.DatumRepresentative
public import AcExtensionPrinciple.Renormalized.ClassLemma32

/-!
# Lemmas 3.1 and 3.2 under the standing assumptions

Paper `e1a0fd5`, `lem:renormalized-equations` and
`lem:renormalized-splitting-bounds`, lines 1006–1125.
The transported representative supplies the three Lemma 2.2 inputs.
-/

public section

namespace AcExtensionPrinciple.StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Lemma 3.1 without additional datum premises. The chosen q agrees with
the radial derivative almost everywhere on every cone. Paper `e1a0fd5`,
`lem:renormalized-equations`, lines 1006–1078. -/
theorem lemma31 :
    RenormalizedEquationsPackage ui S (transportedRadialDatum ui S) :=
  h.sectionThreeDatumInputs.renormalized_equations_package h

/-- Lemma 3.2 without additional datum, geometry, scalar, or integrability
premises. Paper `e1a0fd5`, `lem:renormalized-splitting-bounds`, lines 1082–1125. -/
theorem lemma32 :
    RenormalizedSplittingPackage ui S (transportedRadialDatum ui S) :=
  h.sectionThreeDatumInputs.renormalized_splitting_package h

end AcExtensionPrinciple.StandingFull

end
