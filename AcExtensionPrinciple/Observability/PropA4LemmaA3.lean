module

public import AcExtensionPrinciple.Observability.PropA4Statements
public import AcExtensionPrinciple.Observability.LemmaA3

/-!
# Discharging the uniform positive-mass observation premise

Paper `e1a0fd5`, `lem:observability-positive-mass`, lines 1533–1663.
The globally quantified interface required for the smaller cylinder is
supplied by the proved normalized-chart Lemma A.3, including translations.
-/

public section

namespace AcExtensionPrinciple
namespace PropA4

/-- Both files use exactly the same logarithmic observation duration.
Paper `e1a0fd5`, `eq:observability-positive-mass-duration`, lines 1633–1639. -/
theorem positiveMassDuration_eq_lemmaA3Duration (K ε : ℝ) :
    positiveMassDuration K ε = lemmaA3Duration K ε := rfl

/-- The two translation conventions agree after reversing the shift sign.
Paper `e1a0fd5`, line 1540, `eq:observability-energy-integral`, lines 1477–1480. -/
theorem translatedScalarEnergy_eq_chartTranslatedEnergy (S : SSFields) (T shift : ℝ) :
    translatedScalarEnergy S T shift = chartTranslatedEnergy S T (-shift) := by
  simp only [translatedScalarEnergy, chartTranslatedEnergy, sub_eq_add_neg]

/-- The proved A.3 discharges the entire uniform chart-and-translation
interface, with no auxiliary hypothesis. Paper `e1a0fd5`,
`lem:observability-positive-mass`, lines 1533–1663 and its use at line 1901. -/
theorem lemmaA3Statement {K : ℝ} (hK : 1 ≤ K) : LemmaA3Statement K := by
  obtain ⟨c, hc, hobs⟩ := lemmaA3_translated hK
  refine ⟨c, hc, ?_⟩
  intro ε b S hε hε1 h hμ shift
  rw [positiveMassDuration_eq_lemmaA3Duration] at h ⊢
  rw [translatedScalarEnergy_eq_chartTranslatedEnergy]
  exact hobs ε hε hε1 b S h hμ (-shift)

end PropA4
end AcExtensionPrinciple

end
