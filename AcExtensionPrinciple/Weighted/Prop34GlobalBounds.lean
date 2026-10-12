module

public import AcExtensionPrinciple.Weighted.Prop34GlobalEnergy

/-!
# Uniform global bounds for the actual frozen incoming formula

Paper `e1a0fd5`, `eq:frozen-solution-operators`, lines 1265–1276.
Countably many rectangle estimates give almost-everywhere bounds on
every proper incoming segment, then on the full triangular domain.
-/

public section

namespace AcExtensionPrinciple.StandingFull

open Set Filter MeasureTheory
open scoped ENNReal

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Choose a measurable source-weight extension from the proper triangle.
Paper `e1a0fd5`, lines 1152 and 1265–1276. -/
theorem weighted_exists_measurable_source_density {u₀ U : ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) :
    ∃ σ : ℝ × ℝ → ℝ, Measurable σ ∧
      EqOn (weightedSourceDensity S) σ (weightedTruncatedDomain u₀ U) := by
  obtain ⟨ω, hω, heω⟩ := h.weighted_exists_measurable_remainder_density hi hU
  obtain ⟨L, hL, heL⟩ := weighted_exists_measurable_geometry hi hU
    h.regularCenter.continuous_lam
  refine ⟨fun p => ω p * L p ^ 2, hω.mul (hL.pow_const 2), ?_⟩
  intro p hp
  change weightedSourceDensity S p = ω p * L p ^ 2
  rw [← heω hp, ← heL hp]
  exact weightedSourceDensity_eq S (h.lam_pos
    (weightedTruncatedDomain_subset_triangle hi hU hp)).ne'

/-- The initial energy density has a measurable extension from its cone
for any measurable initial datum. Paper `e1a0fd5`,
`eq:renormalized-initial-energy`, lines 1112–1124 and 1275–1276. -/
theorem frozen_initial_energy_measurable {u₀ U : ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (h₀U : u₀ ≤ U)
    {J₀ : ℝ → ℝ} (hJ₀ : Measurable J₀) :
    ∃ e : ℝ → ℝ≥0∞, Measurable e ∧
      EqOn (fun v => ENNReal.ofReal
        (S.r u₀ v * J₀ v ^ 2 / ((1 - S.mu u₀ v) ^ 2 * S.lam u₀ v))) e (Ioc u₀ 0) := by
  obtain ⟨R, hR, heR⟩ := weighted_exists_measurable_geometry hi hU
    h.regularCenter.continuous_r
  obtain ⟨M, hM, heM⟩ := weighted_exists_measurable_geometry hi hU
    h.regularCenter.continuous_m
  obtain ⟨L, hL, heL⟩ := weighted_exists_measurable_geometry hi hU
    h.regularCenter.continuous_lam
  let P := fun v : ℝ => (u₀, v)
  have hP : Measurable P := measurable_const.prodMk measurable_id
  refine ⟨fun v => ENNReal.ofReal
    (R (P v) * J₀ v ^ 2 / ((1 - massRatio (R (P v)) (M (P v))) ^ 2 * L (P v))),
    (((hR.comp hP).mul (hJ₀.pow_const 2)).div
      ((measurable_const.sub (((hM.comp hP).const_mul 2).div (hR.comp hP))).pow_const 2
        |>.mul (hL.comp hP))).ennreal_ofReal, ?_⟩
  intro v hv
  have hp : P v ∈ weightedTruncatedDomain u₀ U := ⟨le_rfl, h₀U, hv.1.le, hv.2⟩
  simp only [← heR hp, ← heM hp, ← heL hp, P, SSFields.mu]

/-- The literal finite-M_U frozen formula satisfies the global squared
energy estimate. The constants are independent of U; no finiteness of
N_U(Z) is assumed. Paper `e1a0fd5`, `eq:frozen-solution-operators`,
lines 1265–1276. -/
theorem weightedFrozenSolution_global_energy_bound {u₀ U δ ε : ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hδ : δ < 1 / 3)
    (hsmall : WeightedLateSmallness ui S u₀ δ ε)
    {J₀ : ℝ → ℝ} {F : ℝ × ℝ → ℝ} (hJ₀ : Measurable J₀) (hF : Measurable F)
    (hsource : weightedSourceNormSq S u₀ U F < ⊤) :
    weightedRemainderNormSq S u₀ U (weightedFrozenSolution S u₀ J₀ F) ≤
      ENNReal.ofReal (((1 - 3 * δ) / 2)⁻¹) * (∫⁻ v in Ioc u₀ 0, ENNReal.ofReal
        (S.r u₀ v * J₀ v ^ 2 / ((1 - S.mu u₀ v) ^ 2 * S.lam u₀ v))) +
      ENNReal.ofReal ((18 * ε ^ 2 / (1 - 3 * δ)) * ((1 - 3 * δ) / 2)⁻¹) *
        weightedSourceNormSq S u₀ U F := by
  by_cases h₀U : u₀ ≤ U
  swap
  · have he : weightedTruncatedDomain u₀ U = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      exact fun p hp => h₀U (hp.1.trans hp.2.1)
    simp only [weightedRemainderNormSq, he, Measure.restrict_empty, lintegral_zero_measure]
    exact zero_le
  let A := ENNReal.ofReal (((1 - 3 * δ) / 2)⁻¹)
  let B := ENNReal.ofReal ((18 * ε ^ 2 / (1 - 3 * δ)) * ((1 - 3 * δ) / 2)⁻¹)
  let q := fun p => ENNReal.ofReal (weightedRemainderDensity S p *
    |weightedFrozenSolution S u₀ J₀ F p| ^ 2)
  obtain ⟨σ, hσ, heσ⟩ := h.weighted_exists_measurable_source_density hi hU
  let Q := fun p => ENNReal.ofReal (σ p * |F p| ^ 2)
  have hQ : Measurable Q := (hσ.mul (hF.norm.pow_const 2)).ennreal_ofReal
  obtain ⟨e, he, hee⟩ := h.frozen_initial_energy_measurable hi hU h₀U hJ₀
  have hsourceEq : weightedSourceNormSq S u₀ U F =
      ∫⁻ v in Ioc u₀ 0, ∫⁻ s in Ico u₀ (min U v), Q (s, v) := by
    calc
      _ = ∫⁻ p in weightedTruncatedDomain u₀ U, Q p := by
        apply setLIntegral_congr_fun (measurableSet_weightedTruncatedDomain u₀ U)
        intro p hp
        dsimp only [Q]
        rw [heσ hp]
      _ = _ := weighted_triangle_lintegral_eq_incoming u₀ U hQ
  have hrect (b c : ℚ) : ∀ᵐ v ∂volume,
      (u₀ ≤ (b : ℝ) ∧ (b : ℝ) ≤ U ∧ (b : ℝ) < (c : ℝ) ∧ (c : ℝ) ≤ 0) →
      v ∈ Icc (c : ℝ) 0 →
      (∫⁻ s in Icc u₀ (b : ℝ), q (s, v)) ≤
        A * ENNReal.ofReal (S.r u₀ v * J₀ v ^ 2 /
          ((1 - S.mu u₀ v) ^ 2 * S.lam u₀ v)) +
        B * ∫⁻ s in Icc u₀ (b : ℝ),
          ENNReal.ofReal (weightedSourceDensity S (s, v) * |F (s, v)| ^ 2) := by
    by_cases ht : u₀ ≤ (b : ℝ) ∧ (b : ℝ) ≤ U ∧ (b : ℝ) < (c : ℝ) ∧ (c : ℝ) ≤ 0
    · have hr := h.weightedFrozenSolution_ray_lintegral_bound_ae hi hU ht.1 ht.2.1
        ht.2.2.1 ht.2.2.2 hδ hsmall J₀ hF hsource
      rw [ae_restrict_iff' measurableSet_Icc] at hr
      exact hr.mono (fun _ hv _ hvI => hv hvI)
    · exact ae_of_all _ (fun _ ht' _ => False.elim (ht ht'))
  have hall : ∀ᵐ v ∂volume, ∀ b c : ℚ,
      (u₀ ≤ (b : ℝ) ∧ (b : ℝ) ≤ U ∧ (b : ℝ) < (c : ℝ) ∧ (c : ℝ) ≤ 0) →
      v ∈ Icc (c : ℝ) 0 →
      (∫⁻ s in Icc u₀ (b : ℝ), q (s, v)) ≤
        A * ENNReal.ofReal (S.r u₀ v * J₀ v ^ 2 /
          ((1 - S.mu u₀ v) ^ 2 * S.lam u₀ v)) +
        B * ∫⁻ s in Icc u₀ (b : ℝ),
          ENNReal.ofReal (weightedSourceDensity S (s, v) * |F (s, v)| ^ 2) :=
    eventually_countable_forall.mpr (fun b => eventually_countable_forall.mpr (hrect b))
  have hray : ∀ᵐ v ∂volume.restrict (Ioc u₀ 0), ∀ b : ℚ,
      u₀ ≤ (b : ℝ) → (b : ℝ) ≤ U → (b : ℝ) < v →
      (∫⁻ s in Icc u₀ (b : ℝ), q (s, v)) ≤
        A * e v + B * ∫⁻ s in Ico u₀ (min U v), Q (s, v) := by
    filter_upwards [ae_restrict_of_ae hall, ae_restrict_mem measurableSet_Ioc] with v hv hvI
    intro b hab hbU hbv
    obtain ⟨c, hbc, hcv⟩ := exists_rat_btwn hbv
    have hr := hv b c ⟨hab, hbU, hbc, hcv.le.trans hvI.2⟩ ⟨hcv.le, hvI.2⟩
    have heval := hee hvI
    dsimp only at heval
    rw [heval] at hr
    apply hr.trans
    apply add_le_add le_rfl
    refine mul_le_mul_of_nonneg_left ?_ (zero_le : (0 : ℝ≥0∞) ≤ B)
    calc
      _ = ∫⁻ s in Icc u₀ (b : ℝ), Q (s, v) := by
        apply setLIntegral_congr_fun measurableSet_Icc
        intro s hs
        dsimp only [Q]
        rw [heσ (x := (s, v))
          ⟨hs.1, hs.2.trans hbU, (hs.2.trans_lt hbv).le, hvI.2⟩]
      _ = ∫⁻ s in Ico u₀ (b : ℝ), Q (s, v) := by
        rw [restrict_Ico_eq_restrict_Icc]
      _ ≤ ∫⁻ s in Ico u₀ (min U v), Q (s, v) :=
        lintegral_mono_set (fun s hs =>
          ⟨hs.1, lt_min (hs.2.trans_le hbU) (hs.2.trans hbv)⟩)
  have hg := weighted_triangle_lintegral_le_of_ray_bounds q
    (fun v => A * e v + B * ∫⁻ s in Ico u₀ (min U v), Q (s, v)) hray
  rw [lintegral_add_left (f := fun v => A * e v) (measurable_const.mul he),
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← hsourceEq] at hg
  have heq : (∫⁻ v in Ioc u₀ 0, e v) = ∫⁻ v in Ioc u₀ 0,
      ENNReal.ofReal (S.r u₀ v * J₀ v ^ 2 / ((1 - S.mu u₀ v) ^ 2 * S.lam u₀ v)) := by
    apply setLIntegral_congr_fun measurableSet_Ioc
    intro v hv
    exact (hee hv).symm
  simpa only [heq, A, B, q, weightedRemainderNormSq] using hg

/-- Finite admissible initial energy and finite source energy give finite global frozen energy
directly from the incoming formula. Paper `e1a0fd5`, `eq:frozen-solution-operators`, lines
1265–1276. -/
theorem weightedFrozenSolution_global_energy_lt_top {u₀ U δ ε : ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hδ : δ < 1 / 3)
    (hsmall : WeightedLateSmallness ui S u₀ δ ε)
    {J₀ : ℝ → ℝ} {F : ℝ × ℝ → ℝ} (hJ₀ : Measurable J₀) (hF : Measurable F)
    (hinitial : (∫⁻ v in Ioc u₀ 0, ENNReal.ofReal
      (S.r u₀ v * J₀ v ^ 2 / ((1 - S.mu u₀ v) ^ 2 * S.lam u₀ v))) < ⊤)
    (hsource : weightedSourceNormSq S u₀ U F < ⊤) :
    weightedRemainderNormSq S u₀ U (weightedFrozenSolution S u₀ J₀ F) < ⊤ :=
  (h.weightedFrozenSolution_global_energy_bound hi hU hδ hsmall hJ₀ hF hsource).trans_lt
    (ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hinitial,
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hsource⟩)

/-- The global zero-initial source estimate, with the exact squared
Lipschitz constant. Paper `e1a0fd5`, `eq:frozen-solution-operators`,
lines 1265–1276. -/
theorem weightedFrozenSolution_zero_global_energy_bound {u₀ U δ ε : ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hδ : δ < 1 / 3)
    (hsmall : WeightedLateSmallness ui S u₀ δ ε)
    {F : ℝ × ℝ → ℝ} (hF : Measurable F)
    (hsource : weightedSourceNormSq S u₀ U F < ⊤) :
    weightedRemainderNormSq S u₀ U (weightedFrozenSolution S u₀ (fun _ => 0) F) ≤
      ENNReal.ofReal ((18 * ε ^ 2 / (1 - 3 * δ)) * ((1 - 3 * δ) / 2)⁻¹) *
        weightedSourceNormSq S u₀ U F := by
  simpa only [sq, mul_zero, zero_div, ENNReal.ofReal_zero, lintegral_zero,
    mul_zero, zero_add] using
    h.weightedFrozenSolution_global_energy_bound (J₀ := fun _ => 0)
      hi hU hδ hsmall measurable_const hF hsource

end AcExtensionPrinciple.StandingFull

end
