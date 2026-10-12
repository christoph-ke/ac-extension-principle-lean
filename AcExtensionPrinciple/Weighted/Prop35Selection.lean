module

public import AcExtensionPrinciple.Analysis.LogarithmicSubsequence
public import AcExtensionPrinciple.Renormalized.ClassVariation

/-!
# Selecting outgoing cones from a finite logarithmic remainder integral

Helpers for paper `e1a0fd5`, `prop:small-outgoing-bv-cones`,
`equations.tex` lines 1340–1356. The analytic inputs are stated separately
from the source proposition: the variation estimate, the initial L¹ tail,
and the logarithmic remainder integral.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- Transfer the logarithmic vanishing sequence to the actual closed-cone
variation. Paper `e1a0fd5`, `eq:outgoing-variation-remainder` and
`eq:logarithmic-remainder-integrability`, lines 1340–1356.
The conclusion is exactly the sequence in `SmallOutgoingConesStatement`.
This helper does not assert that its analytic premises have been produced. -/
theorem small_outgoing_cones_of_logarithmic_remainder
    {ui u₀ C : ℝ} {S : SSFields} {A R : ℝ → ℝ}
    (hi : ui ≤ u₀) (hu₀ : u₀ < 0)
    (hA : Tendsto A (𝓝[Ioo u₀ 0] 0) (𝓝 0))
    (hlog : (∫⁻ u in Ioo u₀ 0, ENNReal.ofReal (R u ^ 2 / (-u))) < ∞)
    (hvariation : ∀ u ∈ Ioo u₀ 0,
      S.outgoingVariation u ≤ ENNReal.ofReal (C * (A u + R u))) :
    ∃ u : ℕ → ℝ, (∀ n, u n ∈ Ioo ui 0) ∧
      Tendsto u atTop (𝓝 0) ∧
      Tendsto (fun n => eVariationOn
        (fun v => S.dvpsi (u n) v / S.lam (u n) v) (Icc (u n) 0))
        atTop (𝓝 0) := by
  obtain ⟨u, hu, hlim, hR⟩ :=
    exists_sequence_tendsto_zero_of_logarithmic_lintegral_finite hu₀ hlog
  have hwithin : Tendsto u atTop (𝓝[Ioo u₀ 0] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall hu⟩
  have hsum : Tendsto (fun n => C * (A (u n) + R (u n))) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, add_zero, mul_zero] using
      tendsto_const_nhds.mul ((hA.comp hwithin).add hR)
  have hupper : Tendsto (fun n => ENNReal.ofReal (C * (A (u n) + R (u n))))
      atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hsum
  refine ⟨u, fun n => ⟨hi.trans_lt (hu n).1, (hu n).2⟩, hlim, ?_⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun _ => bot_le) (fun n => hvariation (u n) (hu n))

end AcExtensionPrinciple

end
