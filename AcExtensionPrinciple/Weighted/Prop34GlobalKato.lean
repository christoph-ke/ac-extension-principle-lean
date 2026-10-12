module

public import AcExtensionPrinciple.Weighted.Prop34KatoIntegral
public import AcExtensionPrinciple.Weighted.Prop34GlobalEnergy
public import AcExtensionPrinciple.Weighted.Prop34Identification
public import AcExtensionPrinciple.Weighted.Lemma33

/-!
# Integrated Kato on the full proper triangle

Paper `e1a0fd5`, `eq:remainder-difference-kato`, lines 1305–1318.
Countable incoming exhaustion discards the nonnegative future flux.
The full source is retained throughout the exhaustion.
-/

public section

namespace AcExtensionPrinciple.StandingFull

open Set Filter MeasureTheory
open scoped ENNReal

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The full-domain Kato bound follows from the local incoming equation,
zero initial trace, and local source integrability. These ray premises
are supplied by the actual remainder and frozen incoming formulas.
Paper `e1a0fd5`, `eq:remainder-difference-kato`, lines 1305–1316. -/
theorem weighted_global_kato_bound {u₀ U δ ε : ℝ} {W F : ℝ × ℝ → ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hδ : δ < 1 / 3) (hε : 0 ≤ ε)
    (hsmall : WeightedLateSmallness ui S u₀ δ ε) (hF : Measurable F)
    (hray : ∀ b c : ℝ, u₀ ≤ b → b ≤ U → b < c → c ≤ 0 →
      ∀ᵐ v ∂volume.restrict (Icc c 0),
        AbsolutelyContinuousOnInterval (fun s => W (s, v)) u₀ b ∧
        (∀ᵐ x, x ∈ Ioo u₀ b → HasDerivAt (fun s => W (s, v))
          (S.incomingFlux x v * W (x, v) + 3 * S.nu x v * S.dvphi x v * F (x, v)) x) ∧
        IntervalIntegrable (fun s => F (s, v)) volume u₀ b ∧ W (u₀, v) = 0) :
    weightedRemainderL1 S u₀ U W ≤
      ENNReal.ofReal (3 * ε / (1 - 3 * δ)) * weightedSourceL1 S u₀ U F := by
  have hc : 0 < 1 - 3 * δ := by linarith
  let k := 3 * ε / (1 - 3 * δ)
  have hk : 0 ≤ k := by dsimp [k]; positivity
  obtain ⟨ω, hω, heω⟩ := h.weighted_exists_measurable_remainder_density hi hU
  obtain ⟨L, hL, heL⟩ := weighted_exists_measurable_geometry hi hU
    h.regularCenter.continuous_lam
  let Q := fun p => ENNReal.ofReal (ω p * L p * |F p|)
  have hQ : Measurable Q := ((hω.mul hL).mul hF.norm).ennreal_ofReal
  have heQ (p : ℝ × ℝ) (hp : p ∈ weightedTruncatedDomain u₀ U) :
      ENNReal.ofReal ((-S.nu p.1 p.2) / (1 - S.mu p.1 p.2) ^ 2 * |F p|) = Q p := by
    dsimp only [Q]
    rw [← heω hp, ← heL hp]
    unfold weightedRemainderDensity
    congr 1
    field_simp [(h.lam_pos (weightedTruncatedDomain_subset_triangle hi hU hp)).ne']
  have heSource : weightedSourceL1 S u₀ U F =
      ∫⁻ v in Ioc u₀ 0, ∫⁻ s in Ico u₀ (min U v), Q (s, v) := by
    change (∫⁻ p in weightedTruncatedDomain u₀ U, _) = _
    rw [setLIntegral_congr_fun (measurableSet_weightedTruncatedDomain u₀ U) heQ]
    exact weighted_triangle_lintegral_eq_incoming u₀ U hQ
  let q := fun p => ENNReal.ofReal (weightedRemainderDensity S p * |W p|)
  have hrect (b c : ℚ) : ∀ᵐ v ∂volume,
      (u₀ ≤ (b : ℝ) ∧ (b : ℝ) ≤ U ∧ (b : ℝ) < (c : ℝ) ∧ (c : ℝ) ≤ 0) →
      v ∈ Icc (c : ℝ) 0 →
      (∫⁻ s in Icc u₀ (b : ℝ), q (s, v)) ≤
        ENNReal.ofReal k * ∫⁻ s in Icc u₀ (b : ℝ), Q (s, v) := by
    by_cases ht : u₀ ≤ (b : ℝ) ∧ (b : ℝ) ≤ U ∧ (b : ℝ) < (c : ℝ) ∧ (c : ℝ) ≤ 0
    swap
    · exact ae_of_all _ (fun _ ht' _ => False.elim (ht ht'))
    have hr := hray b c ht.1 ht.2.1 ht.2.2.1 ht.2.2.2
    rw [ae_restrict_iff' measurableSet_Icc] at hr
    filter_upwards [hr] with v hv _ hvI
    obtain ⟨hWac, hWode, hFi, hWzero⟩ := hv hvI
    have hb0 := ht.2.1.trans_lt hU
    have hbv := ht.2.2.1.trans_le hvI.1
    have hp (s : ℝ) (hs : s ∈ Icc u₀ (b : ℝ)) : (s, v) ∈ pastTriangle ui :=
      ⟨hi.trans hs.1, hs.2.trans_lt hb0, (hs.2.trans_lt hbv).le, hvI.2⟩
    have hn := (h.weighted_densities_continuous_in ht.1 hi hb0 hbv hvI.2).1
    have hl := continuous_in h.regularCenter.continuous_lam
      (inSeg_subset_triangle hi hb0 hbv.le hvI.2)
    have htcont : ContinuousOn (fun s => (-S.nu s v) / (1 - S.mu s v) ^ 2)
        (Icc u₀ (b : ℝ)) := by
      apply (hn.mul hl).congr
      intro s hs
      dsimp only [Pi.mul_apply]
      unfold weightedRemainderDensity
      field_simp [(h.lam_pos (hp s hs)).ne']
    have hqi : IntervalIntegrable (fun s => weightedRemainderDensity S (s, v) * |W (s, v)|)
        volume u₀ b := (hn.mul (by
          simpa only [uIcc_of_le ht.1, Real.norm_eq_abs] using
            hWac.continuousOn.norm)).intervalIntegrable_of_Icc ht.1
    have hgi := hFi.abs.continuousOn_mul
      (by simpa only [← uIcc_of_le ht.1] using htcont)
    have hb := h.frozen_ray_kato_integral_bound ht.1 hi hb0 hbv hvI.2 hδ hsmall
      hWac hWode hFi
    rw [hWzero, abs_zero, mul_zero, zero_div, zero_add] at hb
    have hbr : (∫ s in u₀..(b : ℝ), weightedRemainderDensity S (s, v) * |W (s, v)|) ≤
        0 * 0 + k * ∫ s in u₀..(b : ℝ),
          (-S.nu s v) / (1 - S.mu s v) ^ 2 * |F (s, v)| := by
      convert hb using 1 <;> dsimp only [k] <;> ring
    have hg := incoming_lintegral_bound_of_real ht.1 (le_refl 0) hk hqi hgi
      (fun s hs => mul_nonneg (div_nonneg (neg_pos.mpr (h.nu_neg (hp s hs))).le
        (mul_nonneg (sq_nonneg _) (h.lam_pos (hp s hs)).le)) (abs_nonneg _))
      (fun s hs => mul_nonneg (div_nonneg (neg_pos.mpr (h.nu_neg (hp s hs))).le
        (sq_nonneg _)) (abs_nonneg _)) hbr
    simp only [ENNReal.ofReal_zero, zero_mul, zero_add] at hg
    convert hg using 2
    apply setLIntegral_congr_fun measurableSet_Icc
    intro s hs
    exact (heQ (s, v) ⟨hs.1, hs.2.trans ht.2.1, (hs.2.trans_lt hbv).le, hvI.2⟩).symm
  have hall := eventually_countable_forall.mpr
    (fun b => eventually_countable_forall.mpr (hrect b))
  have hr : ∀ᵐ v ∂volume.restrict (Ioc u₀ 0), ∀ b : ℚ,
      u₀ ≤ (b : ℝ) → (b : ℝ) ≤ U → (b : ℝ) < v →
      (∫⁻ s in Icc u₀ (b : ℝ), q (s, v)) ≤
        ENNReal.ofReal k * ∫⁻ s in Ico u₀ (min U v), Q (s, v) := by
    filter_upwards [ae_restrict_of_ae hall, ae_restrict_mem measurableSet_Ioc] with v hv hvI
    intro b hab hbU hbv
    obtain ⟨c, hbc, hcv⟩ := exists_rat_btwn hbv
    apply (hv b c ⟨hab, hbU, hbc, hcv.le.trans hvI.2⟩ ⟨hcv.le, hvI.2⟩).trans
    apply mul_le_mul_of_nonneg_left _ zero_le
    rw [← restrict_Ico_eq_restrict_Icc]
    exact lintegral_mono_set (fun s hs =>
      ⟨hs.1, lt_min (hs.2.trans_le hbU) (hs.2.trans hbv)⟩)
  have hb := weighted_triangle_lintegral_le_of_ray_bounds q
    (fun v => ENNReal.ofReal k * ∫⁻ s in Ico u₀ (min U v), Q (s, v)) hr
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← heSource] at hb
  exact hb

/-- The integrated Kato estimate and the full radial L¹ estimate identify
a finite-L¹ difference. The source agrees with T W on the whole proper
domain, including all radii below every cutoff. Paper `e1a0fd5`,
`eq:remainder-difference-l1`, lines 1292–1318. -/
theorem weighted_identification_of_global_kato {u₀ U δ ε : ℝ}
    {W F : ℝ × ℝ → ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hδ : δ < 1 / 3) (hε : 0 ≤ ε)
    (hsmall : WeightedLateSmallness ui S u₀ δ ε) (hW : Measurable W)
    (hfinite : weightedRemainderL1 S u₀ U W < ⊤)
    (heF : F =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)] weightedRadialOperator S W)
    (hKato : weightedRemainderL1 S u₀ U W ≤
      ENNReal.ofReal (3 * ε / (1 - 3 * δ)) * weightedSourceL1 S u₀ U F)
    (hcontract : (3 * ε / (1 - 3 * δ)) *
      ((weightedGapConstant ui S ^ 2)⁻¹ /
        (Real.exp (-Bstar ui S) * (1 - δ)) * ε) < 1) :
    W =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)] 0 := by
  have he : weightedSourceL1 S u₀ U F =
      weightedSourceL1 S u₀ U (weightedRadialOperator S W) := by
    apply lintegral_congr_ae
    filter_upwards [heF] with p hp
    rw [hp]
  rw [he] at hKato
  have hrad := h.lemma33_l1_of_late_smallness hi hU (by linarith) hε hW hsmall
  have hb := hKato.trans (mul_le_mul_of_nonneg_left hrad zero_le)
  have hc : 0 < 1 - 3 * δ := by linarith
  have hd : 0 < 1 - δ := by linarith
  let k := (3 * ε / (1 - 3 * δ)) *
    ((weightedGapConstant ui S ^ 2)⁻¹ / (Real.exp (-Bstar ui S) * (1 - δ)) * ε)
  have hk : 0 ≤ k := by dsimp [k]; positivity
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)] at hb
  have hbr := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite.ne) hb
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hk] at hbr
  have hzero : (weightedRemainderL1 S u₀ U W).toReal = 0 := by
    nlinarith [ENNReal.toReal_nonneg (a := weightedRemainderL1 S u₀ U W)]
  apply h.weighted_remainder_eq_zero_ae_of_l1_zero hi hU hW
  rw [← ENNReal.ofReal_toReal hfinite.ne, hzero, ENNReal.ofReal_zero]

end AcExtensionPrinciple.StandingFull

end
