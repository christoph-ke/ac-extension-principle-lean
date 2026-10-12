module

public import AcExtensionPrinciple.Weighted.Prop34Frozen
public import AcExtensionPrinciple.Weighted.Prop34Cutoff
public import AcExtensionPrinciple.Weighted.ClassWeights
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Finite source energy supplies the frozen incoming equation

Paper `e1a0fd5`, `eq:frozen-linear-transport`, lines 1257–1276.
Finite M_U controls unweighted L². Tonelli then supplies integrable
incoming sources almost everywhere on every off-axis rectangle.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped ENNReal

/-- Local square integrability implies integrability on a finite interval.
Paper `e1a0fd5`, lines 1268–1276, justification of the incoming formula. -/
theorem incoming_integrable_of_square {a b : ℝ} {f : ℝ → ℝ}
    (hab : a ≤ b) (hf : Measurable f)
    (hfinite : (∫⁻ s in Icc a b, ENNReal.ofReal (|f s| ^ 2)) < ⊤) :
    IntervalIntegrable f volume a b := by
  have hi : IntegrableOn f (Icc a b) := by
    refine ⟨hf.aestronglyMeasurable, hasFiniteIntegral_iff_enorm.mpr ?_⟩
    simp only [Real.enorm_eq_ofReal_abs]
    calc
      _ ≤ ∫⁻ s in Icc a b, 1 + ENNReal.ofReal (|f s| ^ 2) := by
        apply lintegral_mono
        intro s
        dsimp only
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num) (sq_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (|f s| - 1)])
      _ = _ := lintegral_add_left measurable_const _
      _ < ⊤ := ENNReal.add_lt_top.mpr ⟨by simp, hfinite⟩
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
    (hi.mono_set Ioc_subset_Icc_self)

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

omit h in
/-- Finite M_U (as opposed to its squared definition) gives the same source
finiteness input. Paper `e1a0fd5`, lines 1257–1276. -/
theorem weighted_source_normSq_lt_top_of_norm {u₀ U : ℝ} {F : ℝ × ℝ → ℝ}
    (hsource : weightedSourceNorm S u₀ U F < ⊤) :
    weightedSourceNormSq S u₀ U F < ⊤ := by
  rw [← weightedSourceNorm_sq]
  simpa only [pow_two] using ENNReal.mul_lt_top hsource hsource

/-- A fixed positive lower bound for the source weight, including the axis.
Paper `e1a0fd5`, lines 1152 and 1265–1276, from G1, G3 and 0≤μ<1. -/
theorem weightedSourceDensity_lower {p : ℝ × ℝ} (hp : p ∈ pastTriangle ui) :
    Real.exp (-Bstar ui S) ^ 2 ≤ weightedSourceDensity S p := by
  have hn := (neg_pos.mpr (h.nu_neg hp)).le
  have hl := (h.lam_pos hp).le
  have hc := (Real.exp_pos (-Bstar ui S)).le
  have hb : Real.exp (-Bstar ui S) ^ 2 ≤ (-S.nu p.1 p.2) * S.lam p.1 p.2 := by
    simpa only [pow_two] using mul_le_mul (h.neg_nu_lower hp) (h.lam_bounds hp).1 hc hn
  apply hb.trans
  unfold weightedSourceDensity
  rw [div_eq_mul_inv]
  exact le_mul_of_one_le_right (mul_nonneg hn hl) (h.weighted_gap_factor_bounds hp).1

/-- Finite M_U controls the unweighted source-square integral on D_U.
Paper `e1a0fd5`, lines 1257–1276. No source regularity is assumed in this bound. -/
theorem weighted_source_square_lt_top {u₀ U : ℝ} {F : ℝ × ℝ → ℝ}
    (hi : ui ≤ u₀) (hU : U < 0)
    (hsource : weightedSourceNormSq S u₀ U F < ⊤) :
    (∫⁻ p in weightedTruncatedDomain u₀ U, ENNReal.ofReal (|F p| ^ 2)) < ⊤ := by
  let c := Real.exp (-Bstar ui S) ^ 2
  have hc : 0 < c := sq_pos_of_pos (Real.exp_pos _)
  calc
    _ ≤ ∫⁻ p in weightedTruncatedDomain u₀ U, ENNReal.ofReal c⁻¹ *
        ENNReal.ofReal (weightedSourceDensity S p * |F p| ^ 2) := by
      apply setLIntegral_mono' (measurableSet_weightedTruncatedDomain u₀ U)
      intro p hp
      rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hc.le)]
      apply ENNReal.ofReal_le_ofReal
      have hb := mul_le_mul_of_nonneg_right
        (h.weightedSourceDensity_lower (weightedTruncatedDomain_subset_triangle hi hU hp))
        (sq_nonneg |F p|)
      calc
        _ = c⁻¹ * (c * |F p| ^ 2) := by rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hc.le)
    _ = ENNReal.ofReal c⁻¹ * weightedSourceNormSq S u₀ U F :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hsource

/-- Finite source energy gives the reversed L² rectangle integral required
for Tonelli and the Volterra estimate. Paper `e1a0fd5`, lines 1268–1276. -/
theorem weighted_source_rectangle_square_lt_top {u₀ U b c : ℝ} {F : ℝ × ℝ → ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hbU : b ≤ U) (hbc : b < c)
    (hF : Measurable F) (hsource : weightedSourceNormSq S u₀ U F < ⊤) :
    (∫⁻ v in Icc c 0, ∫⁻ s in Icc u₀ b, ENNReal.ofReal (|F (s, v)| ^ 2)) < ⊤ := by
  have hm : Measurable (fun p => ENNReal.ofReal (|F p| ^ 2)) := by
    simpa only [Real.norm_eq_abs] using (hF.norm.pow_const 2).ennreal_ofReal
  rw [← setLIntegral_prod_symm _ hm.aemeasurable,
    ← Measure.volume_eq_prod]
  exact (lintegral_mono_set (show Icc u₀ b ×ˢ Icc c 0 ⊆ weightedTruncatedDomain u₀ U from
    fun p hp => ⟨hp.1.1, hp.1.2.trans hbU,
      (hp.1.2.trans_lt (hbc.trans_le hp.2.1)).le, hp.2.2⟩)).trans_lt
        (h.weighted_source_square_lt_top hi hU hsource)

/-- A finite-M_U measurable source is integrable on almost every incoming ray of an off-axis
rectangle. Paper `e1a0fd5`, lines 1257–1276. -/
theorem weighted_source_integrable_ae_rectangle {u₀ U b c : ℝ} {F : ℝ × ℝ → ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hab : u₀ ≤ b) (hbU : b ≤ U) (hbc : b < c)
    (hF : Measurable F) (hsource : weightedSourceNormSq S u₀ U F < ⊤) :
    ∀ᵐ v ∂volume.restrict (Icc c 0),
      IntervalIntegrable (fun s => F (s, v)) volume u₀ b := by
  have hm := (hF.norm.pow_const 2).ennreal_ofReal.lintegral_prod_left'
    (μ := volume.restrict (Icc u₀ b))
  have ht := ae_lt_top hm (h.weighted_source_rectangle_square_lt_top hi hU hbU hbc
    hF hsource).ne
  filter_upwards [ht] with v hv
  exact incoming_integrable_of_square hab
    (hF.comp (measurable_id.prodMk measurable_const)) hv

/-- The same finite-M_U hypothesis also supplies the ray's source-square
integrability used by the coercive energy estimate. Paper `e1a0fd5`,
`eq:frozen-solution-operators`, lines 1265–1276. -/
theorem weighted_source_square_integrable_ae_rectangle {u₀ U b c : ℝ}
    {F : ℝ × ℝ → ℝ} (hi : ui ≤ u₀) (hU : U < 0) (hab : u₀ ≤ b)
    (hbU : b ≤ U) (hbc : b < c) (hF : Measurable F)
    (hsource : weightedSourceNormSq S u₀ U F < ⊤) :
    ∀ᵐ v ∂volume.restrict (Icc c 0),
      IntervalIntegrable (fun s => F (s, v) ^ 2) volume u₀ b := by
  have hm := (hF.norm.pow_const 2).ennreal_ofReal.lintegral_prod_left'
    (μ := volume.restrict (Icc u₀ b))
  have ht := ae_lt_top hm (h.weighted_source_rectangle_square_lt_top hi hU hbU hbc
    hF hsource).ne
  filter_upwards [ht] with v hv
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  have hfi : IntegrableOn (fun s => F (s, v) ^ 2) (Icc u₀ b) := by
    refine ⟨((hF.comp (measurable_id.prodMk measurable_const)).pow_const 2).aestronglyMeasurable,
      hasFiniteIntegral_iff_enorm.mpr ?_⟩
    simpa only [Real.enorm_eq_ofReal_abs, Real.norm_eq_abs, abs_pow, sq_abs] using hv
  exact hfi.mono_set Ioc_subset_Icc_self

/-- The literal frozen formula solves the incoming equation on almost
every ray for every finite-M_U source. Paper `e1a0fd5`,
`eq:frozen-linear-transport`, lines 1257–1276. -/
theorem weightedFrozenSolution_ac_ae_of_finite_source {u₀ U b c : ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hab : u₀ ≤ b) (hbU : b ≤ U)
    (hbc : b < c) (J₀ : ℝ → ℝ) {F : ℝ × ℝ → ℝ}
    (hF : Measurable F) (hsource : weightedSourceNormSq S u₀ U F < ⊤) :
    ∀ᵐ v ∂volume.restrict (Icc c 0),
      AbsolutelyContinuousOnInterval (fun s => weightedFrozenSolution S u₀ J₀ F (s, v))
        u₀ b ∧
      (∀ᵐ x, x ∈ Ioo u₀ b → HasDerivAt
        (fun s => weightedFrozenSolution S u₀ J₀ F (s, v))
        (S.incomingFlux x v * weightedFrozenSolution S u₀ J₀ F (x, v) +
          3 * S.nu x v * S.dvphi x v * F (x, v)) x) := by
  filter_upwards [h.weighted_source_integrable_ae_rectangle hi hU hab hbU hbc hF hsource,
    ae_restrict_mem measurableSet_Icc] with v hv hvI
  exact h.weightedFrozenSolution_ac_and_transport hi hab (hbU.trans_lt hU)
    (hbc.trans_le hvI.1) hvI.2 J₀ F hv

end StandingFull

end AcExtensionPrinciple

end
