module

public import AcExtensionPrinciple.Weighted.Prop34TransportedSource

/-!
# Joint representatives of the actual incoming renormalized fields

Paper `e1a0fd5`, lines 572–574, 1090–1093 and 1292–1302.
Use the literal transported datum, including the exceptional initial labels.
-/

public section

namespace AcExtensionPrinciple.StandingFull

open Set Filter MeasureTheory
open scoped ENNReal

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The literal source in the incoming datum formula is jointly continuous
on every off-axis rectangle. Paper `e1a0fd5`, lines 572–574 and 1292–1302. -/
theorem prop34_radialDatumSource_continuous_rectangle {b c : ℝ}
    (hib : ui ≤ b) (hbc : b < c) (hc0 : c ≤ 0) :
    ContinuousOn (fun p : ℝ × ℝ => radialDatumSource S p.1 p.2)
      (Icc ui b ×ˢ Icc c 0) := by
  let D := Icc ui b ×ˢ Icc c 0
  have hb0 := hbc.trans_le hc0
  have hsub : D ⊆ pastTriangle ui := fun p hp =>
    ⟨hp.1.1, hp.1.2.trans_lt hb0, (hp.1.2.trans_lt (hbc.trans_le hp.2.1)).le, hp.2.2⟩
  have hr := h.regularCenter.continuous_r.mono hsub
  have hm := h.regularCenter.continuous_m.mono hsub
  have hn := h.regularCenter.continuous_nu.mono hsub
  have hl := h.regularCenter.continuous_lam.mono hsub
  have hp := h.regularCenter.continuous_phi.mono hsub
  have hv := h.dvpsi_continuous_rectangle hib hc0 hb0 hbc le_rfl
  have hrne (p : ℝ × ℝ) (hp : p ∈ D) : S.r p.1 p.2 ≠ 0 :=
    (h.r_pos (hsub hp) (hp.1.2.trans_lt (hbc.trans_le hp.2.1))).ne'
  have hmu := (hm.const_mul 2).div hr hrne
  have hg := hn.div (continuousOn_const.sub hmu)
    (fun p hp => (sub_pos.mpr (h.mu_bounds (hsub hp)).2).ne')
  have ht := hv.sub (hl.mul hp)
  have hA := ht.div hl (fun p hp => (h.lam_pos (hsub hp)).ne')
  convert
    ((hg.neg.div (hr.pow 2) (fun p hp => pow_ne_zero 2 (hrne p hp))).mul hA).mul
      ((hA.pow 2).sub (hmu.const_mul 3)) using 1
  rfl

/-- The chosen incoming datum is jointly measurable on each proper
rectangle, directly from its incoming integral. Paper `e1a0fd5`,
lines 572–574 and 1292–1302. -/
theorem prop34_transportedDatum_measurable_rectangle {u₀ U b c : ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hab : u₀ ≤ b) (hbU : b ≤ U)
    (hbc : b < c) (hc0 : c ≤ 0) :
    ∃ Q : ℝ × ℝ → ℝ, Measurable Q ∧
      EqOn (fun p => transportedRadialDatum ui S p.1 p.2) Q (Icc u₀ b ×ˢ Icc c 0) := by
  classical
  have hib := hi.trans hab
  have hc := h.prop34_radialDatumSource_continuous_rectangle hib hbc hc0
  let D := Icc ui b ×ˢ Icc c 0
  let H := D.piecewise (fun p => radialDatumSource S p.1 p.2) (fun _ => 0)
  have hH : Measurable H := hc.measurable_piecewise continuousOn_const
    (measurableSet_Icc.prod measurableSet_Icc)
  obtain ⟨L, hL, heL⟩ := weighted_exists_measurable_geometry le_rfl hU
    h.regularCenter.continuous_lam
  let G := fun q : (ℝ × ℝ) × ℝ => L (q.2, q.1.2) ^ 2 * H (q.2, q.1.2)
  have hG : Measurable G := ((hL.pow_const 2).mul hH).comp
    (measurable_snd.prodMk measurable_fst.snd)
  let I := fun p : ℝ × ℝ => ∫ s in Ioc ui p.1, G (p, s)
  have hI : Measurable I := measurable_setIntegral_between measurable_const measurable_fst hG
  refine ⟨fun p => (deriv (S.dvpsi ui) p.2 + I p) / L p ^ 2,
    ((measurable_deriv _).comp measurable_snd |>.add hI).div (hL.pow_const 2), ?_⟩
  intro p hp
  have hpD : p ∈ weightedTruncatedDomain ui U :=
    ⟨hi.trans hp.1.1, hp.1.2.trans hbU,
      (hp.1.2.trans_lt (hbc.trans_le hp.2.1)).le, hp.2.2⟩
  have heI : (∫ s in ui..p.1, S.lam s p.2 ^ 2 * radialDatumSource S s p.2) = I p := by
    rw [intervalIntegral.integral_of_le (hi.trans hp.1.1)]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    have hsD : (s, p.2) ∈ weightedTruncatedDomain ui U :=
      ⟨hs.1.le, hs.2.trans (hp.1.2.trans hbU),
        (hs.2.trans (hp.1.2.trans_lt (hbc.trans_le hp.2.1)).le), hp.2.2⟩
    have hsK : (s, p.2) ∈ D := ⟨⟨hs.1.le, hs.2.trans hp.1.2⟩, hp.2⟩
    dsimp only [G]
    rw [← heL hsD]
    simp only [H, piecewise_eq_of_mem D _ _ hsK]
  dsimp only [transportedRadialDatum]
  rw [heI, ← heL hpD]

/-- The actual transported renormalized derivative has a measurable
extension on the off-axis strip. Paper `e1a0fd5`, lines 1020–1021, 1292–1302. -/
theorem prop34_renormalizedDerivative_measurable_strip {u₀ U : ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) :
    ∃ J : ℝ × ℝ → ℝ, Measurable J ∧
      EqOn (fun p => S.renormalizedDerivative (transportedRadialDatum ui S) p.1 p.2)
        J (weightedOffAxisStrip u₀ U) := by
  rw [weightedOffAxisStrip_eq_iUnion]
  apply measurable_piecewise_of_countable_extensions
    (fun _ => measurableSet_Icc.prod measurableSet_Icc)
  intro q
  let b := min U (q.1.1 : ℝ)
  let c := (q.1.2 : ℝ)
  obtain ⟨Q, hQ, heQ⟩ := h.prop34_transportedDatum_measurable_rectangle hi hU q.2.1
    (min_le_left _ _) q.2.2.1 q.2.2.2
  let D := Icc u₀ b ×ˢ Icc c 0
  obtain ⟨R, hR, heR⟩ := weighted_exists_measurable_geometry hi hU h.regularCenter.continuous_r
  obtain ⟨M, hM, heM⟩ := weighted_exists_measurable_geometry hi hU h.regularCenter.continuous_m
  obtain ⟨L, hL, heL⟩ := weighted_exists_measurable_geometry hi hU h.regularCenter.continuous_lam
  have hv := (h.dvphi_continuous_rectangle (hi.trans q.2.1) q.2.2.2
    (q.2.2.1.trans_le q.2.2.2) q.2.2.1 le_rfl).mono
      (show D ⊆ Icc ui b ×ˢ Icc c 0 from fun p hp => ⟨⟨hi.trans hp.1.1, hp.1.2⟩, hp.2⟩)
  let V := D.piecewise (fun p => S.dvphi p.1 p.2) (fun _ => 0)
  have hV : Measurable V := hv.measurable_piecewise continuousOn_const
    (measurableSet_Icc.prod measurableSet_Icc)
  refine ⟨fun p => (1 - 2 * M p / R p) * L p *
    (Q p - (R p / L p * V p) ^ 3 / R p),
    ((measurable_const.sub ((hM.const_mul 2).div hR)).mul hL).mul
      (hQ.sub ((((hR.div hL).mul hV).pow_const 3).div hR)), ?_⟩
  intro p hp
  have hpD : p ∈ weightedTruncatedDomain u₀ U :=
    ⟨hp.1.1, hp.1.2.trans (min_le_left _ _),
      (hp.1.2.trans_lt (q.2.2.1.trans_le hp.2.1)).le, hp.2.2⟩
  simp only [SSFields.renormalizedDerivative, Renormalized.renormalizedDerivativeOf,
    massRatio, ← heR hpD, ← heM hpD, ← heL hpD, ← heQ hp,
    V, piecewise_eq_of_mem D _ _ hp]

/-- The actual incoming remainder has a joint measurable representative,
agreeing at every off-axis point. Paper `e1a0fd5`,
`eq:renormalized-splitting`, lines 1090–1093 and 1292–1302. -/
theorem prop34_actualRemainder_measurable_strip {u₀ U : ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) :
    ∃ R : ℝ × ℝ → ℝ, Measurable R ∧
      EqOn (fun p => S.renormalizedRemainder (transportedRadialDatum ui S) ui p.1 p.2)
        R (weightedOffAxisStrip u₀ U) := by
  obtain ⟨J, hJ, heJ⟩ := h.prop34_renormalizedDerivative_measurable_strip hi hU
  obtain ⟨Ji, hJi, heJi⟩ := h.prop34_renormalizedDerivative_measurable_strip le_rfl
    h.initial_negative
  let f := fun v => Ji (ui, v)
  have hf : Measurable f := hJi.comp (measurable_const.prodMk measurable_id)
  obtain ⟨T, hT, heT⟩ := h.weightedTransportedDatum_exists_measurable hi hU hf
  refine ⟨fun p => J p - T p, hJ.sub hT, ?_⟩
  intro p hp
  have hpD : p ∈ weightedTruncatedDomain u₀ U := ⟨hp.1, hp.2.1, hp.2.2.1.le, hp.2.2.2⟩
  have hpi : (ui, p.2) ∈ weightedOffAxisStrip ui ui :=
    ⟨le_rfl, le_rfl, (hi.trans hp.1).trans_lt hp.2.2.1, hp.2.2.2⟩
  dsimp only [SSFields.renormalizedRemainder, SSFields.renormalizedInitial]
  have hj := heJ hp
  have hji := heJi hpi
  dsimp only at hj hji
  rw [hj, ← heT hpD]
  simp only [weightedTransportedDatum, f, ← hji]

end AcExtensionPrinciple.StandingFull

end
