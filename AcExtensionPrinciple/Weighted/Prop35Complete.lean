module

public import AcExtensionPrinciple.Weighted.Prop34
public import AcExtensionPrinciple.Integration.SmallConesFromEnergy

/-!
# Proposition 3.5 under the standing assumptions alone

Paper `e1a0fd5`, `prop:small-outgoing-bv-cones`, lines 1324–1356.
Consume the proved actual terminal energy from Proposition 3.4 in the
logarithmic subsequence and outgoing variation argument.
-/

public section

namespace AcExtensionPrinciple.StandingFull

open Set Filter MeasureTheory
open scoped Topology ENNReal

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Proposition 3.5's exact small outgoing cone sequence, with all energy
and late-smallness premises discharged. Paper `e1a0fd5`,
`prop:small-outgoing-bv-cones`, `eq:small-outgoing-bv-cones`, lines 1324–1356. -/
theorem proposition35 :
    ∃ u : ℕ → ℝ, (∀ n, u n ∈ Ioo ui 0) ∧ Tendsto u atTop (𝓝 0) ∧
      Tendsto (fun n => eVariationOn
        (fun v => S.dvpsi (u n) v / S.lam (u n) v) (Icc (u n) 0)) atTop (𝓝 0) :=
  h.small_outgoing_cones_of_energy h.proposition34

end AcExtensionPrinciple.StandingFull

end
