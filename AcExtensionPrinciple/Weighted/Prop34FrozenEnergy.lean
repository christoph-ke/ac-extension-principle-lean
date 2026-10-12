module

public import AcExtensionPrinciple.Weighted.Prop34RayEnergy

/-!
# The literal frozen solution's ray energy and difference bounds

Paper `e1a0fd5`, `eq:frozen-solution-operators`, lines 1265–1276.
Finite M_U supplies every integrability premise almost everywhere. The
source-difference formula has zero initial datum, as required for the
operator's Lipschitz estimate.
-/

public section

namespace AcExtensionPrinciple.StandingFull

open Set Filter MeasureTheory
open scoped ENNReal

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The actual finite-M_U incoming formula satisfies the uniform integrated
coercive ray estimate almost everywhere. No energy finiteness premise on Z
is assumed. Paper `e1a0fd5`, `eq:frozen-solution-operators`, lines 1265–1276. -/
theorem weightedFrozenSolution_ray_energy_bound_ae {u₀ U b c δ ε : ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hab : u₀ ≤ b) (hbU : b ≤ U)
    (hbc : b < c) (_hc0 : c ≤ 0) (hδ : δ < 1 / 3)
    (hsmall : WeightedLateSmallness ui S u₀ δ ε)
    (J₀ : ℝ → ℝ) {F : ℝ × ℝ → ℝ} (hF : Measurable F)
    (hsource : weightedSourceNormSq S u₀ U F < ⊤) :
    ∀ᵐ v ∂volume.restrict (Icc c 0),
      (∫ s in u₀..b, weightedRemainderDensity S (s, v) *
        |weightedFrozenSolution S u₀ J₀ F (s, v)| ^ 2) ≤
      (S.r u₀ v * J₀ v ^ 2 / ((1 - S.mu u₀ v) ^ 2 * S.lam u₀ v) +
        (18 * ε ^ 2 / (1 - 3 * δ)) * ∫ s in u₀..b,
          weightedSourceDensity S (s, v) * |F (s, v)| ^ 2) / ((1 - 3 * δ) / 2) := by
  filter_upwards [h.weightedFrozenSolution_ac_ae_of_finite_source hi hU hab hbU hbc J₀ hF hsource,
    h.weighted_source_square_integrable_ae_rectangle hi hU hab hbU hbc hF hsource,
    ae_restrict_mem measurableSet_Icc] with v hJ hFs hv
  have hb0 := hbU.trans_lt hU
  have hbv := hbc.trans_le hv.1
  have htrace := h.weightedFrozenSolution_initial hi (hab.trans_lt hb0)
    (hab.trans_lt hbv) hv.2 J₀ F
  simpa only [sq_abs, htrace] using
    h.frozen_ray_coercive_energy_bound hab hi hb0 hbv hv.2 hδ hsmall hJ.1 hJ.2 hFs

/-- Subtracting two frozen formulas with the same initial datum gives the
zero-initial frozen formula of the source difference. The local ray
integrability inputs hold a.e. for finite-M_U sources. Paper `e1a0fd5`,
`eq:frozen-solution-operators`, lines 1265–1276. -/
theorem weightedFrozenSolution_sub {u₀ b v : ℝ}
    (hi : ui ≤ u₀) (hab : u₀ ≤ b) (hb : b < 0) (hbv : b < v) (hv : v ≤ 0)
    (J₀ : ℝ → ℝ) (F₁ F₂ : ℝ × ℝ → ℝ)
    (hF₁ : IntervalIntegrable (fun s => F₁ (s, v)) volume u₀ b)
    (hF₂ : IntervalIntegrable (fun s => F₂ (s, v)) volume u₀ b) :
    weightedFrozenSolution S u₀ J₀ F₁ (b, v) - weightedFrozenSolution S u₀ J₀ F₂ (b, v) =
      weightedFrozenSolution S u₀ (fun _ => 0) (fun p => F₁ p - F₂ p) (b, v) := by
  have hk := h.kappa_ac_in hab hi hb hbv hv
  have hn : ContinuousOn (fun s => S.nu s v) (uIcc u₀ b) := by
    rw [uIcc_of_le hab]
    exact continuous_in h.regularCenter.continuous_nu (inSeg_subset_triangle hi hb hbv.le hv)
  have hp := (h.incoming_components_ac hab hi hb hbv hv).2.2.2
  have hcoef := (((hk.continuousOn.const_mul 3).mul hn).mul hp.continuousOn)
  have hG₁ := hF₁.continuousOn_mul hcoef
  have hG₂ := hF₂.continuousOn_mul hcoef
  have he : (∫ s in u₀..b, 3 * S.kappa s v * S.nu s v * S.dvphi s v *
      (F₁ (s, v) - F₂ (s, v))) =
      (∫ s in u₀..b, 3 * S.kappa s v * S.nu s v * S.dvphi s v * F₁ (s, v)) -
        ∫ s in u₀..b, 3 * S.kappa s v * S.nu s v * S.dvphi s v * F₂ (s, v) := by
    simp_rw [mul_sub]
    exact intervalIntegral.integral_sub hG₁ hG₂
  simp only [weightedFrozenSolution, mul_zero, zero_add]
  rw [he]
  ring

end AcExtensionPrinciple.StandingFull

end
