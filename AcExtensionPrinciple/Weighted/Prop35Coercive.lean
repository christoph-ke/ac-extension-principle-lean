module

public import AcExtensionPrinciple.Weighted.Prop34TerminalEnergy
public import AcExtensionPrinciple.Weighted.Prop35
public import AcExtensionPrinciple.Integration.DecayFromSmallMass

/-!
# Small outgoing BV cones with coercive energy discharged

Paper `e1a0fd5`, `prop:small-outgoing-bv-cones`, lines 1324–1356. Proposition 3.4 now produces the
exact actual remainder energy consumed by the logarithmic subsequence argument. Only Propositions
2.7 and 2.8 remain as inputs. The decay premises are proved by `StandingFull.uniform_mass_decay` and
`StandingFull.common_scalar_limit` in `Integration/DecayComplete.lean`.
-/

public section

namespace AcExtensionPrinciple.StandingFull

open Set Filter MeasureTheory
open scoped ENNReal Topology

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Proposition 3.5's exact sequence conclusion with the coercive energy premise discharged by
Proposition 3.4. The remaining inputs are precisely Propositions 2.7 and 2.8. Paper `e1a0fd5`,
`prop:small-outgoing-bv-cones`, lines 1324–1356. -/
theorem small_outgoing_cones_of_decay
    (hmass : UniformMassDecayStatement ui S)
    (hamp : NormalizedScalarAmplitudesVanishStatement ui S) :
    ∃ u : ℕ → ℝ, (∀ n, u n ∈ Ioo ui 0) ∧ Tendsto u atTop (𝓝 0) ∧
      Tendsto (fun n => eVariationOn
        (fun v => S.dvpsi (u n) v / S.lam (u n) v) (Icc (u n) 0)) atTop (𝓝 0) := by
  obtain ⟨a, hai, ha0, henergy⟩ := h.coercive_energy_of_decay hmass hamp
  obtain ⟨b, hbi, hb0, hsmall⟩ := h.weighted_late_smallness_of_decay hmass hamp
    (by norm_num : (0 : ℝ) < 1 / 6) (by norm_num : (0 : ℝ) < 1 / 2)
  apply h.small_outgoing_cones_of_coercive_energy (hai.trans (le_max_left _ _))
    (max_lt ha0 hb0) (by norm_num : (1 / 2 : ℝ) ^ 2 < 1)
    (fun p hp hpu => hsmall p hp ((le_max_right _ _).trans hpu))
  exact (lintegral_mono_set
    (Ioo_subset_Ioo (le_max_left a b) le_rfl)).trans_lt henergy

/-- The exact actual E(a) interface used by `main_of_small_mass_and_energy`,
now produced from its existing small-mass premise. No energy premise remains.
Paper `e1a0fd5`, `eq:coercive-remainder-bound`, lines 1233–1236 and 1318. -/
theorem coercive_energy_of_small_mass
    (hsmall : PropA4.SmallMassEstimate h.integrationCylinderK) :
    ∃ a : ℝ, ui ≤ a ∧ a < 0 ∧
      (∫⁻ u in Ioo a 0, ∫⁻ v in Ioc u 0, ENNReal.ofReal
        (weightedRemainderDensity S (u, v) *
          |S.renormalizedRemainder S.radialDatumDerivative ui u v| ^ 2)) < ⊤ :=
  h.coercive_energy_of_decay (h.uniform_mass_decay_of_small_mass hsmall)
    (h.common_scalar_limit_of_small_mass hsmall).2

/-- Proposition 3.5's exact sequence conclusion from the existing small-mass interface, with
Proposition 3.4 energy fully discharged. Paper `e1a0fd5`, `prop:small-outgoing-bv-cones`, lines
1324–1356. -/
theorem small_outgoing_cones_of_small_mass
    (hsmall : PropA4.SmallMassEstimate h.integrationCylinderK) :
    ∃ u : ℕ → ℝ, (∀ n, u n ∈ Ioo ui 0) ∧ Tendsto u atTop (𝓝 0) ∧
      Tendsto (fun n => eVariationOn
        (fun v => S.dvpsi (u n) v / S.lam (u n) v) (Icc (u n) 0)) atTop (𝓝 0) :=
  h.small_outgoing_cones_of_decay (h.uniform_mass_decay_of_small_mass hsmall)
    (h.common_scalar_limit_of_small_mass hsmall).2

end AcExtensionPrinciple.StandingFull

end
