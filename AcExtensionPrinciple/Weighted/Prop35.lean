module

public import AcExtensionPrinciple.Weighted.Prop35Variation
public import AcExtensionPrinciple.Weighted.Prop35Logarithmic
public import AcExtensionPrinciple.Weighted.Prop34Measure
public import AcExtensionPrinciple.Weighted.Prop35Inputs

/-!
# Proposition 3.5 assembled from coercive energy and the Section 3 inputs

Assembly conditional on coercive energy and late smallness, paper `e1a0fd5`,
`prop:small-outgoing-bv-cones`, `equations.tex` lines 1324–1356.
The coercive energy input is precisely Proposition 3.4's finiteness
conclusion. Hardy and cone L¹ inputs are discharged from the standing class.
No global measurability premise is imposed on the remainder.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- The tail of any initial L¹ datum tends to zero at the terminal endpoint.
Paper `e1a0fd5`, line 1345 and `eq:renormalized-local-l1`, lines 1072–1078. -/
theorem initial_l1_tail_tendsto_zero {ui u₀ : ℝ} {f : ℝ → ℝ}
    (hui : ui ≤ 0) (hi : ui ≤ u₀)
    (hf : IntervalIntegrable f volume ui 0) :
    Tendsto (fun u => ∫ v in u..0, |f v|) (𝓝[Ioo u₀ 0] 0) (𝓝 0) := by
  have hc := intervalIntegral.continuousOn_primitive_interval' hf.abs
    (show (0 : ℝ) ∈ uIcc ui 0 by simp)
  have hmem : (0 : ℝ) ∈ uIcc ui 0 := by simp
  have hsub : Ioo u₀ 0 ⊆ uIcc ui 0 := by
    rw [uIcc_of_le hui]
    exact fun _ hx => ⟨hi.trans hx.1.le, hx.2.le⟩
  have ht := (hc 0 hmem).tendsto.mono_left (nhdsWithin_mono 0 hsub)
  have heq : (fun u => ∫ v in u..0, |f v|) =
      (fun u => -(∫ v in 0..u, |f v|)) := by
    funext u
    exact intervalIntegral.integral_symm (f := fun v => |f v|) (μ := volume) 0 u
  rw [heq]
  simpa only [intervalIntegral.integral_same, neg_zero] using ht.neg

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The global positive lower bound for the remainder weight.
Paper `e1a0fd5`, `eq:mass-gap-and-nu-bound`, lines 1346–1350. -/
theorem weightedRemainderDensity_lower {p : ℝ × ℝ} (hp : p ∈ pastTriangle ui) :
    Real.exp (-Bstar ui S) ≤ weightedRemainderDensity S p := by
  have hn := neg_pos.mpr (h.nu_neg hp)
  have hl := h.lam_pos hp
  have hg := sub_pos.mpr (h.mu_bounds hp).2
  have hg1 : 1 - S.mu p.1 p.2 ≤ 1 := by linarith [(h.mu_bounds hp).1]
  have hsq : (1 - S.mu p.1 p.2) ^ 2 ≤ 1 := by nlinarith
  have hden : (1 - S.mu p.1 p.2) ^ 2 * S.lam p.1 p.2 ≤ 1 :=
    (mul_le_mul_of_nonneg_right hsq hl.le).trans (by simpa using (h.lam_bounds hp).2)
  apply (h.neg_nu_lower hp).trans
  unfold weightedRemainderDensity
  apply (le_div_iff₀ (mul_pos (sq_pos_of_pos hg) hl)).mpr
  exact mul_le_of_le_one_right hn.le hden

/-- Cauchy–Schwarz for the actual remainder on a cone, with its integrable
representative supplied by Lemma 3.2. Paper `e1a0fd5`, lines 1346–1350. -/
theorem renormalized_remainder_cone_log_bound {u : ℝ}
    (hu : ui ≤ u) (hu0 : u < 0)
    (hR : IntegrableOn (S.renormalizedRemainder S.radialDatumDerivative ui u) (Ioc u 0)) :
    ENNReal.ofReal ((∫ v in u..0,
      |S.renormalizedRemainder S.radialDatumDerivative ui u v|) ^ 2 / (-u)) ≤
      ENNReal.ofReal (Real.exp (-Bstar ui S))⁻¹ * ∫⁻ v in Ioc u 0,
        ENNReal.ofReal (weightedRemainderDensity S (u, v) *
          |S.renormalizedRemainder S.radialDatumDerivative ui u v| ^ 2) := by
  obtain ⟨ω, hω, heω⟩ := h.weighted_exists_measurable_remainder_density
    (u₀ := u) (U := u) hu hu0
  have he (v : ℝ) (hv : v ∈ Ioc u 0) : weightedRemainderDensity S (u, v) = ω (u, v) :=
    heω ⟨le_rfl, le_rfl, hv.1.le, hv.2⟩
  have hbound := cone_l1_sq_div_le_lintegral_energy_of_integrable hu0
    (Real.exp_pos (-Bstar ui S)) (hω.comp (measurable_const.prodMk measurable_id))
    (fun v hv => (h.weightedRemainderDensity_lower ⟨hu, hu0, hv.1.le, hv.2⟩).trans_eq
      (he v hv)) hR
  refine hbound.trans_eq ?_
  congr 1
  apply setLIntegral_congr_fun measurableSet_Ioc
  intro v hv
  simp only [Function.comp_apply, id_eq]
  rw [← he v hv]

/-- Proposition 3.5's exact sequence conclusion from Proposition 3.4 and
the stated Lemma 3.1/3.2 inputs. Paper `e1a0fd5`,
`prop:small-outgoing-bv-cones`, lines 1324–1356.
This internal helper exposes the cone inputs, discharged by
`small_outgoing_cones_of_coercive_energy`. Its energy input is proved by
`StandingFull.proposition34` in `Weighted/Prop34.lean` and consumed in
`Main/Theorem1Proof.lean`. -/
theorem small_outgoing_cones_of_coercive_energy_and_hardy
    {u₀ δ ε : ℝ} (hi : ui ≤ u₀) (hu₀ : u₀ < 0) (hε : ε ^ 2 < 1)
    (hsmall : WeightedLateSmallness ui S u₀ δ ε)
    (hinitial : IntervalIntegrable
      (S.renormalizedDerivative S.radialDatumDerivative ui) volume ui 0)
    (hR : ∀ u ∈ Ioo u₀ 0, IntegrableOn
      (S.renormalizedRemainder S.radialDatumDerivative ui u) (Ioc u 0))
    (hg : ∀ u ∈ Ioo u₀ 0, IntervalIntegrable
      (fun v => S.lam u v / S.r u v * |S.r u v / S.lam u v * S.dvphi u v|) volume u 0)
    (hHardy : ∀ u ∈ Ioo u₀ 0, (∫ v in u..0,
      S.lam u v / S.r u v * |S.r u v / S.lam u v * S.dvphi u v|) ≤
        (S.outgoingVariation u).toReal)
    (henergy : (∫⁻ u in Ioo u₀ 0, ∫⁻ v in Ioc u 0,
      ENNReal.ofReal (weightedRemainderDensity S (u, v) *
        |S.renormalizedRemainder S.radialDatumDerivative ui u v| ^ 2)) < ⊤) :
    ∃ u : ℕ → ℝ, (∀ n, u n ∈ Ioo ui 0) ∧ Tendsto u atTop (𝓝 0) ∧
      Tendsto (fun n => eVariationOn
        (fun v => S.dvpsi (u n) v / S.lam (u n) v) (Icc (u n) 0)) atTop (𝓝 0) := by
  have hlog : (∫⁻ u in Ioo u₀ 0, ENNReal.ofReal ((∫ v in u..0,
      |S.renormalizedRemainder S.radialDatumDerivative ui u v|) ^ 2 / (-u))) < ⊤ := by
    calc
      _ ≤ ∫⁻ u in Ioo u₀ 0, ENNReal.ofReal (Real.exp (-Bstar ui S))⁻¹ *
          ∫⁻ v in Ioc u 0, ENNReal.ofReal (weightedRemainderDensity S (u, v) *
            |S.renormalizedRemainder S.radialDatumDerivative ui u v| ^ 2) := by
        apply setLIntegral_mono' measurableSet_Ioo
        intro u hu
        exact h.renormalized_remainder_cone_log_bound (hi.trans hu.1.le) hu.2 (hR u hu)
      _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top henergy
  refine small_outgoing_cones_of_logarithmic_remainder
    (C := (weightedGapConstant ui S)⁻¹ * ((weightedGapConstant ui S)⁻¹ + 1) /
      (1 - ε ^ 2)) hi hu₀
    (initial_l1_tail_tendsto_zero h.initial_negative.le hi hinitial) hlog ?_
  intro u hu
  have hiu : ui ≤ u := hi.trans hu.1.le
  have htail : IntervalIntegrable
      (S.renormalizedDerivative S.radialDatumDerivative ui) volume u 0 := by
    apply hinitial.mono_set
    rw [uIcc_of_le h.initial_negative.le, uIcc_of_le hu.2.le]
    exact Icc_subset_Icc hiu le_rfl
  exact h.outgoingVariation_le_initial_and_remainder_of_hardy hiu hu.2 hu.1.le hε hsmall
    htail ((intervalIntegrable_iff_integrableOn_Ioc_of_le hu.2.le).mpr (hR u hu))
    (hg u hu) (hHardy u hu)

/-- The exact small outgoing cone conclusion with only late smallness and
Proposition 3.4's energy finiteness left as inputs. All cone L¹ and Hardy
premises follow from the standing class. Paper `e1a0fd5`,
`prop:small-outgoing-bv-cones`, lines 1324–1356. -/
theorem small_outgoing_cones_of_coercive_energy
    {u₀ δ ε : ℝ} (hi : ui ≤ u₀) (hu₀ : u₀ < 0) (hε : ε ^ 2 < 1)
    (hsmall : WeightedLateSmallness ui S u₀ δ ε)
    (henergy : (∫⁻ u in Ioo u₀ 0, ∫⁻ v in Ioc u 0,
      ENNReal.ofReal (weightedRemainderDensity S (u, v) *
        |S.renormalizedRemainder S.radialDatumDerivative ui u v| ^ 2)) < ⊤) :
    ∃ u : ℕ → ℝ, (∀ n, u n ∈ Ioo ui 0) ∧ Tendsto u atTop (𝓝 0) ∧
      Tendsto (fun n => eVariationOn
        (fun v => S.dvpsi (u n) v / S.lam (u n) v) (Icc (u n) 0)) atTop (𝓝 0) := by
  apply h.small_outgoing_cones_of_coercive_energy_and_hardy hi hu₀ hε hsmall
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le h.initial_negative.le).mpr
      (h.small_cone_renormalized_integrable le_rfl h.initial_negative))
    (fun u hu => h.small_cone_remainder_integrable (hi.trans hu.1.le) hu.2)
    (fun u hu => (h.small_cone_hardy_inputs (hi.trans hu.1.le) hu.2).1)
    (fun u hu => (h.small_cone_hardy_inputs (hi.trans hu.1.le) hu.2).2) henergy

end StandingFull

end AcExtensionPrinciple

end
