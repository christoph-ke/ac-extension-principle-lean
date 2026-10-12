module

public import AcExtensionPrinciple.Weighted.Prop34ActualRadial
public import AcExtensionPrinciple.Weighted.Prop34GlobalKato
public import AcExtensionPrinciple.Weighted.Prop34ConstructedRepresentative

/-!
# Incoming equations of the actual and constructed difference

Paper `e1a0fd5`, `eq:remainder-difference-kato`, lines 1289–1316.
All incoming regularity and integrability premises follow from the actual
transport representative and the finite-source frozen formula.
-/

public section

namespace AcExtensionPrinciple.StandingFull

open Set Filter MeasureTheory
open scoped ENNReal Topology

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The actual/constructed difference supplies every ray premise of
the integrated Kato theorem. Paper `e1a0fd5`, lines 1289–1316. -/
theorem prop34_difference_kato_rays {u₀ U : ℝ} {R W H F : ℝ × ℝ → ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (J₀ : ℝ → ℝ)
    (heR : EqOn (fun p => S.renormalizedRemainder (transportedRadialDatum ui S) ui p.1 p.2)
      R (weightedOffAxisStrip u₀ U))
    (heW : EqOn (weightedFrozenSolution S u₀ J₀ F) W (weightedOffAxisStrip u₀ U))
    (heH : EqOn (fun p => S.renormalizedInteraction p.1 p.2 / S.r p.1 p.2)
      H (weightedOffAxisStrip u₀ U))
    (hH : Measurable H) (hF : Measurable F) (hFs : weightedSourceNormSq S u₀ U F < ⊤)
    (heInitial : S.renormalizedRemainder (transportedRadialDatum ui S) ui u₀
      =ᵐ[volume.restrict (Ioc u₀ 0)] J₀) :
    ∀ b c : ℝ, u₀ ≤ b → b ≤ U → b < c → c ≤ 0 →
      ∀ᵐ v ∂volume.restrict (Icc c 0),
        AbsolutelyContinuousOnInterval (fun s => R (s, v) - W (s, v)) u₀ b ∧
        (∀ᵐ x, x ∈ Ioo u₀ b → HasDerivAt (fun s => R (s, v) - W (s, v))
          (S.incomingFlux x v * (R (x, v) - W (x, v)) +
            3 * S.nu x v * S.dvphi x v * (H (x, v) - F (x, v))) x) ∧
        IntervalIntegrable (fun s => H (s, v) - F (s, v)) volume u₀ b ∧
          R (u₀, v) - W (u₀, v) = 0 := by
  intro b c hab hbU hbc hc0
  have hs : Icc c 0 ⊆ Ioc u₀ 0 := fun v hv => ⟨(hab.trans_lt hbc).trans_le hv.1, hv.2⟩
  filter_upwards [h.weightedFrozenSolution_ac_ae_of_finite_source hi hU hab hbU hbc
    J₀ hF hFs, h.weighted_source_integrable_ae_rectangle hi hU hab hbU hbc hF hFs,
    ae_restrict_of_ae_restrict_of_subset hs heInitial, ae_restrict_mem measurableSet_Icc]
    with v hZ hFi hI hv
  have hb0 := hbU.trans_lt hU
  have hbv := hbc.trans_le hv.1
  have hp (s : ℝ) (hs : s ∈ Icc u₀ b) : (s, v) ∈ weightedOffAxisStrip u₀ U :=
    ⟨hs.1, hs.2.trans hbU, hs.2.trans_lt hbv, hv.2⟩
  let A := fun s => S.renormalizedRemainder (transportedRadialDatum ui S) ui s v
  let Z := fun s => weightedFrozenSolution S u₀ J₀ F (s, v)
  have hA := h.renormalizedRemainder_ac_of_incoming_ac (transportedRadialDatum ui S)
    hab hi hb0 hbv hv.2 (h.lemma31.incoming_ac v u₀ b hab hi hb0 hbv hv.2)
  have he (s : ℝ) (hs : s ∈ Icc u₀ b) : A s - Z s = R (s, v) - W (s, v) := by
    exact congrArg₂ (· - ·) (heR (hp s hs)) (heW (hp s hs))
  refine ⟨(hA.fun_sub hZ.1).congr (by
    intro s hs
    rw [uIcc_of_le hab] at hs
    exact he s hs), ?_,
    (h.prop34_interactionSource_integrable_in hi hU hab hbU hbv hv.2 hH heH).sub hFi, ?_⟩
  · have hAo := h.lemma32.remainder_ae v u₀ b hab hi hb0 hbv hv.2
    filter_upwards [hAo, hZ.2] with x hxA hxZ hx
    have hevent : (fun s => A s - Z s) =ᶠ[𝓝 x] (fun s => R (s, v) - W (s, v)) := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with s hs
      exact he s ⟨hs.1.le, hs.2.le⟩
    have hder := ((hxA hx).sub (hxZ hx)).congr_of_eventuallyEq hevent.symm
    apply hder.congr_deriv
    have hRx := heR (hp x ⟨hx.1.le, hx.2.le⟩)
    have hWx := heW (hp x ⟨hx.1.le, hx.2.le⟩)
    have hHx := heH (hp x ⟨hx.1.le, hx.2.le⟩)
    dsimp only at hRx hWx hHx
    rw [hRx, hWx, ← hHx]
    ring
  · have hR₀ := heR (hp u₀ ⟨le_rfl, hab⟩)
    have hW₀ := heW (hp u₀ ⟨le_rfl, hab⟩)
    dsimp only at hR₀ hW₀
    rw [← hR₀, ← hW₀, hI,
      h.weightedFrozenSolution_initial hi (hab.trans_lt hb0) (hab.trans_lt hbv) hv.2]
    exact sub_self _

end AcExtensionPrinciple.StandingFull

end
