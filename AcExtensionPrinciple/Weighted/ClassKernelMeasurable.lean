module

public import AcExtensionPrinciple.Weighted.ClassMeasurableStrip
public import AcExtensionPrinciple.Weighted.ClassTransportKernel

/-!
# Measurable representatives of the transported kernel

Paper `e1a0fd5`, `eq:transported-radial-estimate`,
`equations.tex` lines 1189–1202. All measurable extensions are constructed
from the class, rather than added as a premise of the paper lemma.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- A jointly measurable extension of G_a from the truncated domain,
valid for every initial label. Paper `e1a0fd5`, lines 1189–1202. -/
theorem weighted_exists_measurable_transport_kernel {u₀ U : ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) :
    ∃ K : (ℝ × ℝ) → ℝ → ℝ, Measurable (Function.uncurry K) ∧
      ∀ p ∈ weightedTruncatedDomain u₀ U, ∀ a, K p a = weightedTransportKernel S a p := by
  classical
  obtain ⟨R, hR, heR⟩ := weighted_exists_measurable_geometry hi hU h.regularCenter.continuous_r
  obtain ⟨A, hA, heA⟩ := h.weighted_exists_measurable_amplitude_strip hi hU
  let K := fun (p : ℝ × ℝ) (a : ℝ) =>
    if p.1 < a ∧ a < p.2 then R (p.1, a) / R p ^ 2 * A (p.1, a) else 0
  have hm : Measurable (Function.uncurry K) := by
    apply Measurable.ite
      ((measurableSet_lt (measurable_fst.comp measurable_fst) measurable_snd).inter
        (measurableSet_lt measurable_snd (measurable_snd.comp measurable_fst)))
    · exact ((hR.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).div
        ((hR.comp measurable_fst).pow_const 2)).mul
        (hA.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
    · exact measurable_const
  refine ⟨K, hm, ?_⟩
  intro p hp a
  by_cases ha : p.1 < a ∧ a < p.2
  · have hpa : (p.1, a) ∈ weightedTruncatedDomain u₀ U :=
      ⟨hp.1, hp.2.1, ha.1.le, ha.2.le.trans hp.2.2.2⟩
    have hpas : (p.1, a) ∈ weightedOffAxisStrip u₀ U :=
      ⟨hp.1, hp.2.1, ha.1, ha.2.le.trans hp.2.2.2⟩
    simp only [K, weightedTransportKernel, ite_eq_left ha, ← heR hpa, ← heR hp, ← heA hpas]
  · simp [K, weightedTransportKernel, ha]

/-- A measurable extension of the unweighted source density from D_U.
Paper `e1a0fd5`, lines 1187 and 1198–1202. -/
theorem weighted_exists_measurable_base_source {u₀ U : ℝ} (hi : ui ≤ u₀) (hU : U < 0) :
    ∃ ω : ℝ × ℝ → ℝ, Measurable ω ∧
      EqOn (fun p => (-S.nu p.1 p.2) * S.lam p.1 p.2) ω (weightedTruncatedDomain u₀ U) := by
  obtain ⟨N, hN, heN⟩ := weighted_exists_measurable_geometry hi hU h.regularCenter.continuous_nu
  obtain ⟨L, hL, heL⟩ := weighted_exists_measurable_geometry hi hU h.regularCenter.continuous_lam
  refine ⟨fun p => (-N p) * L p, hN.neg.mul hL, ?_⟩
  intro p hp
  dsimp only
  rw [← heN hp, ← heL hp]

end StandingFull

end AcExtensionPrinciple

end
