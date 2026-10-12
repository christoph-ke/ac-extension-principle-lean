module

public import AcExtensionPrinciple.ACDatum.InitialTail
public import AcExtensionPrinciple.BoundaryEnergy.Stability
public import AcExtensionPrinciple.Decay.ScalarVariation

/-!
# The initial derivative tail is exactly total variation

Paper `e1a0fd5`, `eq:initial-ac-tail`, `equations.tex` lines 537–543.
The two proved variation inequalities identify the integral tail with the
variation of the initial absolutely continuous datum.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Exact identification of ω with the initial total variation.
Paper `e1a0fd5`, `eq:initial-ac-tail`, lines 539–543. -/
theorem initialACTail_eq_variation {u : ℝ} (hu : ui ≤ u) (hu0 : u ≤ 0) :
    eVariationOn (S.dvpsi ui) (Icc u 0) = ENNReal.ofReal (initialACTail ui S u) := by
  have hac := h.initial_ac_data.mono (show uIcc u 0 ⊆ uIcc ui 0 by
    rw [uIcc_of_le hu0, uIcc_of_le h.initial_negative.le]
    exact Icc_subset_Icc hu le_rfl)
  have hbv : BoundedVariationOn (S.dvpsi ui) (Icc u 0) := by
    simpa only [uIcc_of_le hu0] using hac.boundedVariationOn
  apply le_antisymm
  · exact ac_variation_le_integral_abs_deriv hu0 hac
  · have hb := integral_abs_deriv_le_variation hu0 hbv
    exact (ENNReal.ofReal_le_ofReal hb).trans_eq (ENNReal.ofReal_toReal hbv)

end StandingFull

end AcExtensionPrinciple

end
