module

public import AcExtensionPrinciple.Weighted.ClassInitialTransport
public import AcExtensionPrinciple.Weighted.ClassKernelMeasurable
public import AcExtensionPrinciple.Weighted.Lemma33Kernel

/-!
# Lemma 3.3: the transported initial datum

Paper `e1a0fd5`, `eq:transported-radial-estimate`,
`equations.tex` lines 1171–1173 and 1187–1202. The initial derivative
needs only measurable L¹ data, not L². The proof constructs every
measurability premise of Tonelli from the local BV class.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory
open scoped ENNReal

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- W3: the squared transported-data estimate for the actual κ-ratio
transport. Every constant is chosen from δ and the original geometry.
Paper `e1a0fd5`, `eq:transported-radial-estimate`, lines 1171–1173, 1187–1202. -/
theorem lemma33_transported_sq_of_late_mass_bound {u₀ U δ : ℝ} {f : ℝ → ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hδ : δ < 3)
    (hf : AEMeasurable f (volume.restrict (Ioc ui 0)))
    (hsmall : ∀ p ∈ pastTriangle ui, u₀ ≤ p.1 → S.mu p.1 p.2 / (1 - S.mu p.1 p.2) ≤ δ) :
    weightedSourceNormSq S u₀ U
        (weightedRadialOperator S (weightedTransportedDatum ui S f)) ≤
      ENNReal.ofReal ((weightedGapConstant ui S)⁻¹ ^ 4 *
        ((Bstar ui S + Real.log (1 / initialGap ui S)) / (3 - δ))) *
          (∫⁻ a in Ioc ui 0, ENNReal.ofReal |f a|) ^ 2 := by
  obtain ⟨K, hK, heK⟩ := h.weighted_exists_measurable_transport_kernel hi hU
  obtain ⟨ω, hω, heω⟩ := h.weighted_exists_measurable_base_source hi hU
  let μ := volume.restrict (weightedTruncatedDomain u₀ U)
  let σ := volume.restrict (Ioc u₀ 0)
  let B := ENNReal.ofReal ((Bstar ui S + Real.log (1 / initialGap ui S)) / (3 - δ))
  let c := ENNReal.ofReal ((weightedGapConstant ui S)⁻¹)
  let q := ENNReal.ofReal ((weightedGapConstant ui S ^ 2)⁻¹)
  let E := fun p => ∫⁻ a in Ioc u₀ 0, ENNReal.ofReal |f a| * ENNReal.ofReal |K p a|
  have hωpos (p : ℝ × ℝ) (hp : p ∈ weightedTruncatedDomain u₀ U) : 0 ≤ ω p := by
    rw [← heω hp]
    have hpt := weightedTruncatedDomain_subset_triangle hi hU hp
    exact mul_nonneg (neg_pos.mpr (h.nu_neg hpt)).le (h.lam_pos hpt).le
  have hf' : AEMeasurable (fun a => ENNReal.ofReal |f a|) σ :=
    (hf.mono_measure (Measure.restrict_mono (Ioc_subset_Ioc_left hi) le_rfl)).norm.ennreal_ofReal
  have hKm : AEMeasurable (Function.uncurry (fun p a => ENNReal.ofReal |K p a|)) (μ.prod σ) := by
    change AEMeasurable (fun z : (ℝ × ℝ) × ℝ => ENNReal.ofReal |K z.1 z.2|) (μ.prod σ)
    simpa only [Real.norm_eq_abs, Function.uncurry] using hK.norm.ennreal_ofReal.aemeasurable
  have hbound : ∀ᵐ a ∂σ, (∫⁻ p, ENNReal.ofReal (ω p) * ENNReal.ofReal |K p a| ^ 2 ∂μ) ≤ B := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with a ha
    have he : (∫⁻ p, ENNReal.ofReal (ω p) * ENNReal.ofReal |K p a| ^ 2 ∂μ) =
        ∫⁻ p in weightedTruncatedDomain u₀ U, ENNReal.ofReal
          ((-S.nu p.1 p.2) * S.lam p.1 p.2 * |weightedTransportKernel S a p| ^ 2) := by
      apply setLIntegral_congr_fun (measurableSet_weightedTruncatedDomain u₀ U)
      intro p hp
      dsimp only
      rw [heK p hp a, ← ENNReal.ofReal_pow (abs_nonneg _),
        ← ENNReal.ofReal_mul (hωpos p hp), ← heω hp]
    rw [he]
    exact h.weighted_transport_kernel_energy_le hi hU ha hδ hsmall
  have hlabel := weighted_label_kernel_l2_le_ae hf' hKm hω.ennreal_ofReal.aemeasurable hbound
  have hL (p : ℝ × ℝ) (hp : p ∈ weightedTruncatedDomain u₀ U) :
      ENNReal.ofReal |weightedRadialOperator S (weightedTransportedDatum ui S f) p| ≤ c * E p := by
    have he : E p = ∫⁻ a in Ioc u₀ 0,
        ENNReal.ofReal |f a| * ENNReal.ofReal |weightedTransportKernel S a p| := by
      simp only [E, heK p hp]
    rw [he]
    exact h.weightedTransportedDatum_radial_domination hi hU hp f
  have hpoint (p : ℝ × ℝ) (hp : p ∈ weightedTruncatedDomain u₀ U) :
      ENNReal.ofReal (weightedSourceDensity S p *
        |weightedRadialOperator S (weightedTransportedDatum ui S f) p| ^ 2) ≤
      (q * c ^ 2) * (ENNReal.ofReal (ω p) * E p ^ 2) := by
    have he : ENNReal.ofReal ((-S.nu p.1 p.2) * S.lam p.1 p.2 *
        |weightedRadialOperator S (weightedTransportedDatum ui S f) p| ^ 2) =
        ENNReal.ofReal (ω p) * ENNReal.ofReal
          |weightedRadialOperator S (weightedTransportedDatum ui S f) p| ^ 2 := by
      rw [← ENNReal.ofReal_pow (abs_nonneg _), ← ENNReal.ofReal_mul (hωpos p hp), ← heω hp]
    refine (h.weighted_source_sq_le_base
      (weightedTruncatedDomain_subset_triangle hi hU hp) _).trans ?_
    rw [he]
    have hs := pow_le_pow_left' (hL p hp) 2
    rw [mul_pow] at hs
    calc
      _ ≤ q * (ENNReal.ofReal (ω p) * (c ^ 2 * E p ^ 2)) :=
        mul_le_mul le_rfl (mul_le_mul le_rfl hs zero_le zero_le) zero_le zero_le
      _ = _ := by ring
  have hdatum : (∫⁻ a in Ioc u₀ 0, ENNReal.ofReal |f a|) ^ 2 ≤
      (∫⁻ a in Ioc ui 0, ENNReal.ofReal |f a|) ^ 2 :=
    pow_le_pow_left' (lintegral_mono_set (Ioc_subset_Ioc_left hi)) 2
  calc
    _ ≤ (q * c ^ 2) * ∫⁻ p, ENNReal.ofReal (ω p) * E p ^ 2 ∂μ := by
      rw [← lintegral_const_mul' _ _ (by dsimp [q, c]; finiteness)]
      exact setLIntegral_mono' (measurableSet_weightedTruncatedDomain u₀ U) hpoint
    _ ≤ (q * c ^ 2) * (B * (∫⁻ a in Ioc u₀ 0, ENNReal.ofReal |f a|) ^ 2) :=
      mul_le_mul le_rfl hlabel zero_le zero_le
    _ ≤ (q * c ^ 2) * (B * (∫⁻ a in Ioc ui 0, ENNReal.ofReal |f a|) ^ 2) :=
      mul_le_mul le_rfl (mul_le_mul le_rfl hdatum zero_le zero_le) zero_le zero_le
    _ = _ := by
      dsimp only [q, c, B]
      rw [← ENNReal.ofReal_pow (inv_nonneg.mpr h.weightedGapConstant_pos.le),
        ← ENNReal.ofReal_mul (by positivity), ← mul_assoc,
        ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      simp only [inv_pow]
      ring

/-- The fixed incoming flux constant is nonnegative. Paper `e1a0fd5`,
`eq:incoming-flux-bound`, lines 1198–1201. -/
theorem weighted_initial_flux_constant_nonneg :
    0 ≤ Bstar ui S + Real.log (1 / initialGap ui S) := by
  have hB : 0 ≤ Bstar ui S := ENNReal.toReal_nonneg
  have hci := h.initialGap_pos
  have hc : 1 ≤ 1 / initialGap ui S := (le_div_iff₀ hci).mpr (by
    simpa using h.initialGap_le_one)
  exact add_nonneg hB (Real.log_nonneg hc)

/-- W3 in the transported-data norm form. Paper `e1a0fd5`,
`eq:transported-radial-estimate`, lines 1171–1173 and 1187–1202. -/
theorem lemma33_transported_of_late_mass_bound {u₀ U δ : ℝ} {f : ℝ → ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hδ : δ < 3)
    (hf : AEMeasurable f (volume.restrict (Ioc ui 0)))
    (hsmall : ∀ p ∈ pastTriangle ui, u₀ ≤ p.1 → S.mu p.1 p.2 / (1 - S.mu p.1 p.2) ≤ δ) :
    weightedSourceNorm S u₀ U (weightedRadialOperator S (weightedTransportedDatum ui S f)) ≤
      ENNReal.ofReal ((weightedGapConstant ui S)⁻¹ ^ 2 *
        Real.sqrt ((Bstar ui S + Real.log (1 / initialGap ui S)) / (3 - δ))) *
          ∫⁻ a in Ioc ui 0, ENNReal.ofReal |f a| := by
  have hflux : 0 ≤ (Bstar ui S + Real.log (1 / initialGap ui S)) / (3 - δ) :=
    div_nonneg h.weighted_initial_flux_constant_nonneg (by linarith)
  have hc : 0 ≤ (weightedGapConstant ui S)⁻¹ ^ 2 *
      Real.sqrt ((Bstar ui S + Real.log (1 / initialGap ui S)) / (3 - δ)) := by positivity
  have hs : weightedSourceNorm S u₀ U
        (weightedRadialOperator S (weightedTransportedDatum ui S f)) ^ 2 ≤
      (ENNReal.ofReal ((weightedGapConstant ui S)⁻¹ ^ 2 *
        Real.sqrt ((Bstar ui S + Real.log (1 / initialGap ui S)) / (3 - δ))) *
          ∫⁻ a in Ioc ui 0, ENNReal.ofReal |f a|) ^ 2 := by
    rw [weightedSourceNorm_sq, mul_pow, ← ENNReal.ofReal_pow hc]
    convert h.lemma33_transported_sq_of_late_mass_bound hi hU hδ hf hsmall using 1
    congr 2
    rw [mul_pow, Real.sq_sqrt hflux, ← pow_mul]
  exact (ENNReal.rpow_le_rpow_iff (by norm_num : 0 < (2 : ℝ))).mp
    (by simpa only [ENNReal.rpow_two] using hs)

end StandingFull

end AcExtensionPrinciple

end
