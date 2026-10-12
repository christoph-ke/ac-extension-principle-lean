module

public import AcExtensionPrinciple.Redundancy.LambdaAxisTrace

/-!
# Joint λ continuity from the remaining standing hypotheses
Paper commit `e1a0fd5`, `equations.tex` lines 220–275,
`eq:regular-axis`, `eq:regular-axis-scalar-traces`, `eq:raychaudhuri`.
Scalar variation controls the incoming log κ trace at the axis.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- Bounds for scalar amplitude and variation extend incoming log κ transport to its stored
axis value. The core scalar bounds discharge these premises near each regular axis point.
Paper `e1a0fd5`, lines 220–275, `eq:regular-axis-scalar-traces`, `eq:raychaudhuri`. -/
theorem q1_log_kappa_axis_compare {ui u v V B C : ℝ} {S : SSFields}
    (h : StandingWithout_continuous_lam ui S) (hu : ui ≤ u) (huv : u < v)
    (hvV : v < V) (hV : V < 0) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hamp : ∀ w ∈ Ioc v V, ∀ s ∈ Ioo u v,
      |S.dupsi s w / S.nu s w - S.phi s w| ≤ B)
    (hvar : ∀ w ∈ Ioc v V,
      eVariationOn (fun s => S.phi s w) (Icc u v) ≤ ENNReal.ofReal C) :
    |Real.log (S.kappa u v) - Real.log (S.kappa v v)| ≤ B * C := by
  have hv0 := hvV.trans hV
  have hu0 := huv.trans hv0
  have hc1 := q1_log_kappa_out_continuous h hu hu0 v ⟨huv.le, hv0.le⟩
  have hc2 := q1_log_kappa_out_continuous h (hu.trans huv.le) hv0 v ⟨le_rfl, hv0.le⟩
  have ht1 := (hc1.mono (show Ioc v V ⊆ Icc u 0 from
    fun w hw => ⟨huv.le.trans hw.1.le, hw.2.trans hV.le⟩)).tendsto
  have ht2 := (hc2.mono (show Ioc v V ⊆ Icc v 0 from
    fun w hw => ⟨hw.1.le, hw.2.trans hV.le⟩)).tendsto
  have : NeBot (𝓝[Ioc v V] v) := left_nhdsWithin_Ioc_neBot hvV
  apply le_of_tendsto (ht1.sub ht2).abs
  filter_upwards [self_mem_nhdsWithin] with w hw
  have hb := h.toQ1StandingCore.log_kappa_sub_le_variation huv.le hu hv0 hw.1
    (hw.2.trans hV.le) hB (hamp w hw)
  rw [abs_sub_comm] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left
    ((ENNReal.toReal_mono ENNReal.ofReal_ne_top (hvar w hw)).trans_eq
      (ENNReal.toReal_ofReal hC)) hB)

/-- The diagonal κ value agrees with minus ν, without joint λ continuity.
Paper `e1a0fd5`, `eq:regular-axis`, lines 243–275. -/
theorem q1_kappa_axis_eq_neg_nu {ui a : ℝ} {S : SSFields}
    (h : Q1StandingCore ui S) (ha : (a, a) ∈ axis ui) : S.kappa a a = -S.nu a a := by
  have hr := (h.regularCenter.localBV.axis_values a (axis_subset_pastTriangle ui ha)).1
  have hn := h.regularCenter.axis_expansions a ha
  simp [SSFields.kappa, kappaOf, SSFields.mu, massRatio, hr, hn]

/-- Incoming scalar variation makes log κ jointly continuous at each regular axis point.
Paper `e1a0fd5`, `eq:regular-axis-scalar-traces`, `eq:raychaudhuri`, lines 220–275. -/
theorem q1_log_kappa_axis_continuous {ui a : ℝ} {S : SSFields}
    (h : StandingWithout_continuous_lam ui S) (ha : (a, a) ∈ axis ui) :
    ContinuousWithinAt (fun p : ℝ × ℝ => Real.log (S.kappa p.1 p.2))
      (pastTriangle ui) (a, a) := by
  let U := a / 2
  have haU : a < U := by dsimp [U]; linarith [ha.2.1]
  have hU0 : U < 0 := by dsimp [U]; linarith [ha.2.1]
  let K := (Icc ui U ×ˢ Icc ui U) ∩ {p : ℝ × ℝ | p.1 ≤ p.2}
  have hK : IsCompact K :=
    (isCompact_Icc.prod isCompact_Icc).inter_right
      (isClosed_le continuous_fst continuous_snd)
  have hKQ : K ⊆ pastTriangle ui := by
    intro p hp
    exact ⟨hp.1.1.1, hp.1.1.2.trans_lt hU0, hp.2, hp.1.2.2.trans hU0.le⟩
  obtain ⟨M, _, hM⟩ := h.regularCenter.localBV.scalar_ac_variation K hK hKQ
  let C := |M| + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hMC : M ≤ C := by dsimp [C]; linarith [le_abs_self M]
  have hD : ContinuousOn (fun x => Real.log (-S.nu x x)) (Icc ui U) := by
    have hn : ContinuousOn (fun x => S.nu x x) (Icc ui U) :=
      h.continuous_nu.comp (continuous_id.prodMk continuous_id).continuousOn
      (fun x hx => show (x, x) ∈ pastTriangle ui from
        ⟨hx.1, hx.2.trans_lt hU0, le_rfl, (hx.2.trans_lt hU0).le⟩)
    intro x hx
    have hn' : ContinuousWithinAt (fun t : ℝ => -S.nu t t) (Icc ui U) x := (hn x hx).neg
    exact (Real.continuousAt_log (neg_pos.mpr
      (h.toQ1StandingCore.nu_neg (p := (x, x))
        ⟨hx.1, hx.2.trans_lt hU0, le_rfl, (hx.2.trans_lt hU0).le⟩)).ne').comp_continuousWithinAt
          (f := fun t : ℝ => -S.nu t t) hn'
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  let B := ε / (3 * C)
  have hB : 0 < B := by dsimp [B]; positivity
  have ht := (h.regularCenter.axis_dupsi_trace a ha).sub
    (q1_phi_axis_trace h.toQ1StandingCore ha)
  simp only [sub_self] at ht
  obtain ⟨δe, hδe, he⟩ := Metric.tendsto_nhdsWithin_nhds.mp ht B hB
  obtain ⟨δd, hδd, hd⟩ := Metric.continuousWithinAt_iff.mp
    (hD a ⟨ha.1, haU.le⟩) (ε / 3) (by positivity)
  refine ⟨min (δe / 2) (min δd ((U - a) / 2)), by positivity, ?_⟩
  intro p hp hpd
  have hpe := hpd.trans_le (min_le_left _ _)
  have hpd' := hpd.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hpU := hpd.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hvU : p.2 < U := by
    have hv := (show dist p.2 a ≤ dist p (a, a) from le_max_right _ _).trans_lt hpU
    rw [Real.dist_eq, abs_lt] at hv
    linarith
  have hvui : ui ≤ p.2 := hp.1.trans hp.2.2.1
  have hv0 := hvU.trans hU0
  have hav : (p.2, p.2) ∈ axis ui := ⟨hvui, hv0, rfl⟩
  have hdiag : |Real.log (S.kappa p.2 p.2) - Real.log (S.kappa a a)| < ε / 3 := by
    rw [q1_kappa_axis_eq_neg_nu h.toQ1StandingCore hav,
      q1_kappa_axis_eq_neg_nu h.toQ1StandingCore ha]
    exact hd ⟨hvui, hvU.le⟩
      ((show dist p.2 a ≤ dist p (a, a) from le_max_right _ _).trans_lt hpd')
  have hcompare : |Real.log (S.kappa p.1 p.2) - Real.log (S.kappa p.2 p.2)| ≤ B * C := by
    rcases hp.2.2.1.eq_or_lt with hpv | hpv
    · rw [hpv, sub_self, abs_zero]
      positivity
    · let V := p.2 + min (δe / 4) ((U - p.2) / 2)
      have hvV : p.2 < V := by
        dsimp [V]
        have hm : 0 < min (δe / 4) ((U - p.2) / 2) := by positivity
        linarith
      have hVU : V < U := by
        dsimp [V]
        linarith [min_le_right (δe / 4) ((U - p.2) / 2)]
      have hVδ : V - p.2 ≤ δe / 4 := by
        dsimp [V]
        linarith [min_le_left (δe / 4) ((U - p.2) / 2)]
      apply q1_log_kappa_axis_compare h hp.1 hpv hvV (hVU.trans hU0) hB.le hC.le
      · intro w hw s hs
        have hsQ : (s, w) ∈ pastTriangle ui \ axis ui := by
          rw [← cylinderScalarRegion_eq_axisComplement]
          exact ⟨hp.1.trans hs.1.le, hs.2.trans hw.1, hw.2.trans (hVU.trans hU0).le⟩
        have hnear : dist (s, w) (a, a) < δe := by
          rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq, abs_lt, abs_lt] at hpe ⊢
          constructor <;> constructor <;> dsimp only at * <;> linarith [hs.1, hs.2, hw.1, hw.2]
        have hb := he hsQ hnear
        rw [Real.dist_eq, sub_zero] at hb
        exact hb.le
      · intro w hw
        have hsK : inSeg w p.1 p.2 ⊆ K := by
          intro q hq
          have hqw : q.2 = w := mem_singleton_iff.mp hq.2
          change (q.1 ∈ Icc ui U ∧ q.2 ∈ Icc ui U) ∧ q.1 ≤ q.2
          rw [hqw]
          exact ⟨⟨⟨hp.1.trans hq.1.1, hq.1.2.trans hvU.le⟩,
            ⟨hvui.trans hw.1.le, hw.2.trans hVU.le⟩⟩,
            hq.1.2.trans hw.1.le⟩
        exact (hM w p.1 p.2 hpv.le hsK).2.trans (ENNReal.ofReal_le_ofReal hMC)
  rw [Real.dist_eq]
  calc
    _ ≤ |Real.log (S.kappa p.1 p.2) - Real.log (S.kappa p.2 p.2)| +
        |Real.log (S.kappa p.2 p.2) - Real.log (S.kappa a a)| := abs_sub_le _ _ _
    _ ≤ B * C + |Real.log (S.kappa p.2 p.2) - Real.log (S.kappa a a)| :=
      add_le_add hcompare le_rfl
    _ < ε := by
      have hBC : B * C = ε / 3 := by dsimp [B]; field_simp
      rw [hBC]
      linarith

/-- Joint λ continuity at every regular axis point follows from scalar transport and the
retained ν continuity. Paper `e1a0fd5`, `eq:regular-axis`, lines 220–275. -/
theorem q1_lam_axis_continuous {ui a : ℝ} {S : SSFields}
    (h : StandingWithout_continuous_lam ui S) (ha : (a, a) ∈ axis ui) :
    ContinuousWithinAt (fun p : ℝ × ℝ => S.lam p.1 p.2) (pastTriangle ui) (a, a) := by
  have haQ := axis_subset_pastTriangle ui ha
  have he := Real.continuous_exp.continuousAt.comp_continuousWithinAt
    (q1_log_kappa_axis_continuous h ha)
  have hκ : ContinuousWithinAt (fun p : ℝ × ℝ => S.kappa p.1 p.2)
      (pastTriangle ui) (a, a) := by
    apply he.congr_of_eventuallyEq_of_mem ?_ haQ
    filter_upwards [self_mem_nhdsWithin] with p hp
    exact (Real.exp_log (h.toQ1StandingCore.kappa_pos hp)).symm
  have hc : ContinuousWithinAt (fun p : ℝ × ℝ =>
      S.kappa p.1 p.2 * (1 - S.mu p.1 p.2)) (pastTriangle ui) (a, a) :=
    hκ.mul (continuousWithinAt_const.sub (q1_mu_axis_continuous h.toQ1StandingCore ha))
  apply hc.congr_of_eventuallyEq_of_mem ?_ haQ
  filter_upwards [self_mem_nhdsWithin] with p hp
  exact (div_mul_cancel₀ (S.lam p.1 p.2)
    (sub_pos.mpr (h.toQ1StandingCore.mu_bounds hp).2).ne').symm

/-- Proper rectangles give continuity everywhere off-axis, including the initial side and v = 0.
Paper `e1a0fd5`, `eq:radius`, lines 220–275. -/
theorem continuous_lam_offAxis_of_rest {ui : ℝ} {S : SSFields}
    (h : StandingWithout_continuous_lam ui S) :
    ContinuousOn (fun p => S.lam p.1 p.2) (pastTriangle ui \ axis ui) := by
  intro p hp
  have hpa : p.1 < p.2 := by
    exact lt_of_le_of_ne hp.1.2.2.1 (fun he => hp.2 ⟨hp.1.1, hp.1.2.1, he.symm⟩)
  let U := (p.1 + p.2) / 2
  let a := (U + p.2) / 2
  have hpU : p.1 < U := by dsimp [U]; linarith
  have hUa : U < a := by dsimp [a, U]; linarith
  have hap : a < p.2 := by dsimp [a, U]; linarith
  have hU : U < 0 := by dsimp [U]; linarith [hp.1.2.1, hp.1.2.2.2]
  have hc := continuous_lam_rectangle_of_rest h (hp.1.1.trans hpU.le)
    (hap.le.trans hp.1.2.2.2) hU hUa le_rfl
  apply (hc p ⟨⟨hp.1.1, hpU.le⟩, ⟨hap.le, hp.1.2.2.2⟩⟩).mono_of_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin,
    ((continuous_fst.tendsto p).eventually (Iio_mem_nhds hpU)).filter_mono
      nhdsWithin_le_nhds,
    ((continuous_snd.tendsto p).eventually (Ioi_mem_nhds hap)).filter_mono
      nhdsWithin_le_nhds] with q hq hqU hqa
  exact ⟨⟨hq.1.1, hqU.le⟩, ⟨hqa.le, hq.1.2.2.2⟩⟩

/-- The joint λ continuity field is redundant, including the regular axis and terminal ray
v = 0. Every other additional field is retained explicitly in the deletion class.
Paper `e1a0fd5`, lines 220–275, `eq:regular-axis`, `eq:regular-axis-scalar-traces`. -/
theorem continuous_lam_of_rest {ui : ℝ} {S : SSFields}
    (h : StandingWithout_continuous_lam ui S) :
    ContinuousOn (fun p => S.lam p.1 p.2) (pastTriangle ui) := by
  intro p hp
  rcases hp.2.2.1.eq_or_lt with he | he
  · have heq : p = (p.1, p.1) := Prod.ext rfl he.symm
    rw [heq]
    exact q1_lam_axis_continuous h ⟨hp.1, hp.2.1, rfl⟩
  · apply (continuous_lam_offAxis_of_rest h p ⟨hp, ?_⟩).mono_of_mem_nhdsWithin
    · filter_upwards [self_mem_nhdsWithin,
        (Filter.Eventually.filter_mono nhdsWithin_le_nhds
          (isOpen_lt continuous_fst continuous_snd |>.mem_nhds he))] with q hq hqa
      exact ⟨hq, fun ha => hqa.ne ha.2.2.symm⟩
    · intro ha
      exact he.ne ha.2.2.symm

end AcExtensionPrinciple

end
