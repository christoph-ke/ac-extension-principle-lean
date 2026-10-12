module

public import AcExtensionPrinciple.Weighted.ClassTransportKernel

/-!
# The transported initial datum and its radial domination

Paper `e1a0fd5`, `eq:renormalized-initial-domination`
and `eq:transported-radial-estimate`, lines 1090–1093 and 1189–1191.
The datum is transported by the κ ratio, exactly as in Lemma 3.2.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory
open scoped ENNReal

/-- The explicit transported datum from the original initial cone.
Paper `e1a0fd5`, `eq:renormalized-initial-domination`, lines 1090–1093. -/
@[expose] noncomputable def weightedTransportedDatum
    (ui : ℝ) (S : SSFields) (f : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  (S.kappa ui p.2 / S.kappa p.1 p.2) * f p.2

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The transported datum's domination constant is the inverse geometric
gap constant. Paper `e1a0fd5`, `eq:renormalized-initial-domination`,
lines 1090–1093 and the use at line 1191. -/
theorem weightedTransportedDatum_abs_le {p : ℝ × ℝ} (hp : p ∈ pastTriangle ui) (f : ℝ → ℝ) :
    |weightedTransportedDatum ui S f p| ≤ (weightedGapConstant ui S)⁻¹ * |f p.2| := by
  have hpi : (ui, p.2) ∈ pastTriangle ui :=
    ⟨le_rfl, h.initial_negative, hp.1.trans hp.2.2.1, hp.2.2.2⟩
  have hka := h.kappa_pos hpi
  have hkb := h.kappa_pos hp
  have hci := h.initialGap_pos
  have hc : S.kappa ui p.2 / S.kappa p.1 p.2 ≤ (weightedGapConstant ui S)⁻¹ := by
    calc
      _ ≤ (1 / initialGap ui S) / Real.exp (-Bstar ui S) :=
        div_le_div₀ (by positivity) (h.kappa_upper hpi) (Real.exp_pos _) (h.kappa_lower hp)
      _ = _ := by simp [weightedGapConstant, div_eq_mul_inv, mul_inv_rev, mul_comm]
  rw [weightedTransportedDatum, abs_mul, abs_of_pos (div_pos hka hkb)]
  exact mul_le_mul_of_nonneg_right hc (abs_nonneg _)

/-- Pointwise kernel domination for the actual κ-ratio transport.
Paper `e1a0fd5`, `eq:transported-radial-estimate`, lines 1189–1191. -/
theorem weightedTransportedDatum_radial_domination {u₀ U : ℝ} {p : ℝ × ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hp : p ∈ weightedTruncatedDomain u₀ U) (f : ℝ → ℝ) :
    ENNReal.ofReal |weightedRadialOperator S (weightedTransportedDatum ui S f) p| ≤
      ENNReal.ofReal ((weightedGapConstant ui S)⁻¹) *
        ∫⁻ a in Ioc u₀ 0,
          ENNReal.ofReal |f a| * ENNReal.ofReal |weightedTransportKernel S a p| := by
  have hpt := weightedTruncatedDomain_subset_triangle hi hU hp
  have hpord := hp.2.2.1
  have hc : 0 ≤ (weightedGapConstant ui S)⁻¹ := inv_nonneg.mpr h.weightedGapConstant_pos.le
  have hfactor : 0 ≤ (S.r p.1 p.2 ^ 2)⁻¹ := by positivity
  have hbase :
      ENNReal.ofReal |weightedRadialOperator S (weightedTransportedDatum ui S f) p| ≤
      ∫⁻ a in Ioo p.1 p.2, ENNReal.ofReal
        ((S.r p.1 p.2 ^ 2)⁻¹ * |S.r p.1 a *
          (weightedIncomingAmplitude S p.1 a * weightedTransportedDatum ui S f (p.1, a))|) := by
    rw [weightedRadialOperator, abs_mul, abs_of_nonneg hfactor, ENNReal.ofReal_mul hfactor,
      intervalIntegral.integral_of_le hpord, integral_Ioc_eq_integral_Ioo]
    simp_rw [ENNReal.ofReal_mul hfactor]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply mul_le_mul le_rfl ?_ zero_le zero_le
    simpa only [Real.enorm_eq_ofReal_abs] using enorm_integral_le_lintegral_enorm
      (μ := volume.restrict (Ioo p.1 p.2))
      (fun a => S.r p.1 a *
        (weightedIncomingAmplitude S p.1 a * weightedTransportedDatum ui S f (p.1, a)))
  have hdom : (∫⁻ a in Ioo p.1 p.2, ENNReal.ofReal
      ((S.r p.1 p.2 ^ 2)⁻¹ * |S.r p.1 a *
        (weightedIncomingAmplitude S p.1 a * weightedTransportedDatum ui S f (p.1, a))|)) ≤
      ENNReal.ofReal ((weightedGapConstant ui S)⁻¹) *
        ∫⁻ a in Ioo p.1 p.2,
          ENNReal.ofReal |f a| * ENNReal.ofReal |weightedTransportKernel S a p| := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply setLIntegral_mono' measurableSet_Ioo
    intro a ha
    have hpa : (p.1, a) ∈ pastTriangle ui :=
      ⟨hpt.1, hpt.2.1, ha.1.le, ha.2.le.trans hp.2.2.2⟩
    have hrad := (h.r_pos hpa ha.1).le
    rw [weightedTransportKernel, ite_eq_left ⟨ha.1, ha.2⟩,
      ← ENNReal.ofReal_mul (abs_nonneg _), ← ENNReal.ofReal_mul hc,
      abs_mul, abs_mul, abs_of_nonneg hrad]
    apply ENNReal.ofReal_le_ofReal
    have hid : (weightedGapConstant ui S)⁻¹ *
        (|f a| * |S.r p.1 a / S.r p.1 p.2 ^ 2 * weightedIncomingAmplitude S p.1 a|) =
        (S.r p.1 p.2 ^ 2)⁻¹ * (S.r p.1 a * |weightedIncomingAmplitude S p.1 a|) *
          ((weightedGapConstant ui S)⁻¹ * |f a|) := by
      rw [abs_mul, abs_div, abs_of_nonneg hrad,
        abs_of_nonneg (sq_nonneg (S.r p.1 p.2))]
      ring
    rw [hid, ← mul_assoc]
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left (h.weightedTransportedDatum_abs_le hpa f)
        (mul_nonneg hfactor (mul_nonneg hrad (abs_nonneg (weightedIncomingAmplitude S p.1 a))))
  refine (hbase.trans hdom).trans ?_
  apply mul_le_mul le_rfl ?_ zero_le zero_le
  exact lintegral_mono_set (fun a ha => ⟨hp.1.trans_lt ha.1, ha.2.le.trans hp.2.2.2⟩)

end StandingFull

end AcExtensionPrinciple

end
