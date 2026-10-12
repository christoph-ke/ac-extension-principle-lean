module

public import AcExtensionPrinciple.Weighted.Prop34TerminalEnergy
public import AcExtensionPrinciple.Integration.DecayComplete

/-!
# Proposition 3.4 under the standing assumptions alone

Paper `e1a0fd5`, `prop:weighted-remainder-control`, lines 1226–1319. Unconditional Propositions 2.7
and 2.8 produce the late bounds; both numerical thresholds, the fixed point, Kato identification and
terminal limit are discharged.
-/

public section

namespace AcExtensionPrinciple.StandingFull

open Set MeasureTheory
open scoped ENNReal

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Proposition 3.4's quantitative coercive bound holds on every sufficiently
late cone. The explicit constants in `weightedCoerciveBound` depend only on
the original geometry and δ=1/6, before the start time. Its right-hand side
is a constant times I₀ plus a constant times ε² times the original initial
L¹ norm squared. Paper `e1a0fd5`, `prop:weighted-remainder-control`,
`eq:coercive-remainder-bound`, lines 1226–1238 and 1316–1319. -/
theorem prop34_coercive_remainder_control :
    ∃ ε : ℝ, 0 < ε ∧ ∃ a : ℝ, ui ≤ a ∧ a < 0 ∧
      ∀ u₀ : ℝ, a ≤ u₀ → u₀ < 0 →
        (∫⁻ u in Ioo u₀ 0, ∫⁻ v in Ioc u 0, ENNReal.ofReal
          (weightedRemainderDensity S (u, v) *
            |S.renormalizedRemainder S.radialDatumDerivative ui u v| ^ 2)) ≤
              weightedCoerciveBound ui S u₀ (1 / 6) ε ∧
        (∫⁻ u in Ioo u₀ 0, ∫⁻ v in Ioc u 0, ENNReal.ofReal
          (weightedRemainderDensity S (u, v) *
            |S.renormalizedRemainder S.radialDatumDerivative ui u v| ^ 2)) < ⊤ := by
  obtain ⟨ε, hε, hbudget, hcontract⟩ := exists_weighted_identification_epsilon
    (δ := 1 / 6) (by norm_num) h.weightedGapConstant_pos (Real.exp_pos (-Bstar ui S))
  obtain ⟨a, hi, ha, hsmall⟩ := h.weighted_late_smallness
    (by norm_num : (0 : ℝ) < 1 / 6) hε
  refine ⟨ε, hε, a, hi, ha, ?_⟩
  intro u₀ hau hu₀
  exact h.prop34_terminal_actual_energy (hi.trans hau) hu₀ (by norm_num) hε.le
    (fun p hp hpu => hsmall p hp (hau.trans hpu)) hbudget hcontract

/-- The exact E(a) premise in `main_of_small_mass_and_energy` and
`main_of_energy`, now under the standing assumptions alone.
Paper `e1a0fd5`, `prop:weighted-remainder-control`,
`eq:coercive-remainder-bound`, lines 1233–1236 and 1318. -/
theorem proposition34 :
    ∃ a : ℝ, ui ≤ a ∧ a < 0 ∧
      (∫⁻ u in Ioo a 0, ∫⁻ v in Ioc u 0, ENNReal.ofReal
        (weightedRemainderDensity S (u, v) *
          |S.renormalizedRemainder S.radialDatumDerivative ui u v| ^ 2)) < ⊤ := by
  obtain ⟨_, _, a, hi, ha, hbound⟩ := h.prop34_coercive_remainder_control
  exact ⟨a, hi, ha, (hbound a le_rfl ha).2⟩

end AcExtensionPrinciple.StandingFull

end
