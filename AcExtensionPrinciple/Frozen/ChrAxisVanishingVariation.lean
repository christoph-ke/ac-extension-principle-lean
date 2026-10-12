module

public import AcExtensionPrinciple.Frozen.SSFields

/-!
# Frozen anchor `ChrAxisVanishingVariation_v1`

Declaration `AcExtensionPrinciple.ChrAxisVanishingVariation` of approval package v1.4 (paper
`203e554`), moved from `AcExtensionPrinciple/External/ChristodoulouBV.lean` with its code unchanged.
Manifest entry `ChrAxisVanishingVariation_v1` in `planning/frozen-anchors.json`. Do not edit this
file: any change needs an author-approved versioned successor.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- Christodoulou item 4, with its original δ-ranges and portions in D.
Paper `203e554`, line 216, author ruling Q5; CPAM pp. 1146–1147.
Families 2 and 4 include δ = 0 and exclude δ = ε, unlike Luk–Oh Def. 2.1(5). -/
structure ChrAxisVanishingVariation (D : Set (ℝ × ℝ)) (S : SSFields) (a : ℝ) : Prop where
  past_outgoing : Tendsto (fun ε : ℝ => ⨆ δ ∈ Ioc 0 ε,
    eVariationOn (S.phi (a - δ)) {v | v ∈ Ioo (a - δ) a ∧ (a - δ, v) ∈ D})
    (𝓝[>] 0) (𝓝 0)
  past_incoming : Tendsto (fun ε : ℝ => ⨆ δ ∈ Ico 0 ε,
    eVariationOn (fun u => S.phi u (a - δ))
      {u | u ∈ Ioo (a - ε) (a - δ) ∧ (u, a - δ) ∈ D})
    (𝓝[>] 0) (𝓝 0)
  future_incoming : Tendsto (fun ε : ℝ => ⨆ δ ∈ Ioc 0 ε,
    eVariationOn (fun u => S.phi u (a + δ))
      {u | u ∈ Ioo a (a + δ) ∧ (u, a + δ) ∈ D})
    (𝓝[>] 0) (𝓝 0)
  future_outgoing : Tendsto (fun ε : ℝ => ⨆ δ ∈ Ico 0 ε,
    eVariationOn (S.phi (a + δ))
      {v | v ∈ Ioo (a + δ) (a + ε) ∧ (a + δ, v) ∈ D})
    (𝓝[>] 0) (𝓝 0)

end AcExtensionPrinciple

end
