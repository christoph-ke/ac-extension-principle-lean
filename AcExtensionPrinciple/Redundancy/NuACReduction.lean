module

public import AcExtensionPrinciple.Redundancy.LambdaContinuity
public import AcExtensionPrinciple.Redundancy.ExpansionAC
public import AcExtensionPrinciple.Reduced.OutgoingRay

/-!
# An optional transport criterion for incoming ν absolute continuity
Paper commit `e1a0fd5`, `equations.tex` lines 87–89 and 220–275,
`eq:logarithmic-expansions`, `eq:regular-axis`.
This optional side result identifies incoming ν AC with AC of a moving-axis residual.
It is independent of the proof of `mainTheorem`: the standing class supplies the
incoming continuity and primitive identities used by that proof, without this criterion.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- Retained ν continuity extends its outgoing antitonicity to the axis endpoint.
Paper `e1a0fd5`, `eq:radius`, `eq:regular-axis`, lines 220–275. -/
theorem q1_nu_out_antitone_without_incoming_ac {ui u : ℝ} {S : SSFields}
    (h : StandingWithout_ac_nu_in ui S) (hu : ui ≤ u) (hu0 : u < 0) :
    AntitoneOn (S.nu u) (Icc u 0) := by
  have hc : ContinuousOn (S.nu u) (Icc u 0) := h.continuous_nu.comp
    (continuous_const.prodMk continuous_id).continuousOn
    (fun w hw => show (u, w) ∈ pastTriangle ui from ⟨hu, hu0, hw⟩)
  have haxis (v : ℝ) (hv : v ∈ Icc u 0) : S.nu u v ≤ S.nu u u := by
    rcases hv.1.eq_or_lt with he | he
    · rw [← he]
    have ht : Tendsto (S.nu u) (𝓝[>] u) (𝓝 (S.nu u u)) := by
      have hcu := hc u ⟨le_rfl, hu0.le⟩
      rw [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsGE hu0] at hcu
      exact hcu.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
    exact ge_of_tendsto ht (by
      filter_upwards [self_mem_nhdsWithin,
        ((continuous_id.tendsto u).mono_left nhdsWithin_le_nhds).eventually
          (Iio_mem_nhds he)] with w hw hwv
      exact h.toQ1StandingCore.nu_out_antitone
        (outSeg_subset_offAxis hu hu0 hw hv.2)
        ⟨le_rfl, hwv.le⟩ ⟨hwv.le, le_rfl⟩ hwv.le)
  intro x hx y hy hxy
  by_cases he : u = x
  · rw [← he]
    exact haxis y hy
  · exact h.toQ1StandingCore.nu_out_antitone
      (outSeg_subset_offAxis hu hu0 (lt_of_le_of_ne hx.1 he) hy.2)
      ⟨le_rfl, hxy⟩ ⟨hxy, le_rfl⟩ hxy

/-- Outgoing log(−ν) is AC through the axis, without incoming ν AC. Monotonicity gives BV;
continuity removes an endpoint jump. Paper `e1a0fd5`, lines 87–89, 220–275. -/
theorem q1_log_neg_nu_out_ac {ui u v : ℝ} {S : SSFields}
    (h : StandingWithout_ac_nu_in ui S) (hp : (u, v) ∈ pastTriangle ui) :
    AbsolutelyContinuousOnInterval (fun w => Real.log (-S.nu u w)) u v := by
  rcases hp.2.2.1.eq_or_lt with he | he
  · change u = v at he
    rw [← he]
  have hν := h.continuous_nu.comp (continuous_const.prodMk continuous_id).continuousOn
    (fun w (hw : w ∈ Icc u v) => show (u, w) ∈ pastTriangle ui from
      ⟨hp.1, hp.2.1, hw.1, hw.2.trans hp.2.2.2⟩)
  have hpos : ∀ w ∈ Icc u v, 0 < -S.nu u w := fun w hw =>
    neg_pos.mpr (h.toQ1StandingCore.nu_neg (p := (u, w))
      ⟨hp.1, hp.2.1, hw.1, hw.2.trans hp.2.2.2⟩)
  have hc : ContinuousOn (fun w => Real.log (-S.nu u w)) (Icc u v) :=
    hν.neg.log (fun w hw => (hpos w hw).ne')
  have hm : MonotoneOn (fun w => Real.log (-S.nu u w)) (Icc u v) := by
    intro x hx y hy hxy
    exact (Real.log_le_log_iff (hpos x hx) (hpos y hy)).mpr
      (neg_le_neg (q1_nu_out_antitone_without_incoming_ac h hp.1 hp.2.1
        ⟨hx.1, hx.2.trans hp.2.2.2⟩ ⟨hy.1, hy.2.trans hp.2.2.2⟩ hxy))
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  have hbv : BoundedVariationOn (fun w => Real.log (-S.nu u w)) (Icc u v) :=
    hm.boundedVariationOn (fun w hw => by simpa only [Real.norm_eq_abs] using hB w hw)
  apply q1_ac_extend_left he hc hbv
  intro c hc
  have hνac := intervalPrimitive_ac hc.2 (fun x hx =>
    h.regularCenter.localBV.nu_out u c x hx.1
      (outSeg_subset_offAxis hp.1 hp.2.1 hc.1 (hx.2.trans hp.2.2.2)))
  apply positive_ac_log hνac.fun_neg
  intro w hw
  rw [uIcc_of_le hc.2] at hw
  exact hpos w ⟨hc.1.le.trans hw.1, hw.2⟩

/-- The logarithmic ν transport primitive reaches the regular axis. No incoming ν AC is used.
Paper `e1a0fd5`, `eq:logarithmic-expansions`, `eq:regular-axis`, lines 87–89, 220–275. -/
theorem q1_log_neg_nu_primitive_from_axis {ui u v : ℝ} {S : SSFields}
    (h : StandingWithout_ac_nu_in ui S) (hp : (u, v) ∈ pastTriangle ui) :
    IntervalPrimitive (fun w => Real.log (-S.nu u w))
      (fun w => S.kappa u w * S.varkappa u w) u v := by
  apply ac_integral_eq_sub hp.2.2.1 (q1_log_neg_nu_out_ac h hp)
  apply Filter.Eventually.of_forall
  intro w hw
  let c := (u + w) / 2
  have huc : u < c := by dsimp [c]; linarith [hw.1]
  have hcw : c < w := by dsimp [c]; linarith [hw.1]
  have hcv : c ≤ v := hcw.le.trans hw.2.le
  have hs : MapsTo (fun x : ℝ => (u, x)) (Icc c v) (pastTriangle ui) := by
    intro x hx
    exact ⟨hp.1, hp.2.1, huc.le.trans hx.1, hx.2.trans hp.2.2.2⟩
  have hr := h.continuous_r.comp (continuous_const.prodMk continuous_id).continuousOn hs
  have hm := h.continuous_m.comp (continuous_const.prodMk continuous_id).continuousOn hs
  have hl := h.continuous_lam.comp (continuous_const.prodMk continuous_id).continuousOn hs
  have hn := h.continuous_nu.comp (continuous_const.prodMk continuous_id).continuousOn hs
  have hμ : ContinuousOn (S.mu u) (Icc c v) :=
    (continuousOn_const.mul hm).div hr (fun x hx =>
      (h.toQ1StandingCore.r_pos (hs hx) (huc.trans_le hx.1)).ne')
  have hcoeff : ContinuousOn (S.radiusCoeff u) (Icc c v) :=
    ((hμ.mul hl).mul hn).div ((continuousOn_const.sub hμ).mul hr) (fun x hx =>
      mul_ne_zero (sub_pos.mpr (h.toQ1StandingCore.mu_bounds (hs hx)).2).ne'
        (h.toQ1StandingCore.r_pos (hs hx) (huc.trans_le hx.1)).ne')
  have hd := intervalPrimitive_hasDerivAt ⟨hcw, hw.2⟩ hcoeff (fun x hx =>
    h.regularCenter.localBV.nu_out u c x hx.1
      (outSeg_subset_offAxis hp.1 hp.2.1 huc (hx.2.trans hp.2.2.2)))
  exact OutgoingRay.log_neg_nu ((hd).congr_deriv (S.radiusCoeff_eq u w))
    (h.toQ1StandingCore.nu_neg (p := (u, w))
      ⟨hp.1, hp.2.1, hw.1.le, hw.2.le.trans hp.2.2.2⟩)

/-- The explicit diagonal datum plus moving-axis outgoing transport, used by
`ac_nu_in_iff_transport_residual_ac` below. This optional criterion is independent
of the proof of `mainTheorem`. Paper `e1a0fd5`, lines 87–89, 220–275. -/
@[expose] noncomputable def q1_nu_transport_residual (S : SSFields) (v u : ℝ) : ℝ :=
  Real.log (S.lam u u) + ∫ w in u..v, S.kappa u w * S.varkappa u w

/-- The residual equals log(−ν) exactly, without incoming ν AC.
Paper `e1a0fd5`, `eq:logarithmic-expansions`, `eq:regular-axis`, lines 87–89, 220–275. -/
theorem q1_nu_transport_residual_eq {ui u v : ℝ} {S : SSFields}
    (h : StandingWithout_ac_nu_in ui S) (hp : (u, v) ∈ pastTriangle ui) :
    q1_nu_transport_residual S v u = Real.log (-S.nu u v) := by
  have hi := (q1_log_neg_nu_primitive_from_axis h hp).2
  have ha := h.regularCenter.axis_expansions u ⟨hp.1, hp.2.1, rfl⟩
  dsimp only at hi
  rw [ha, neg_neg] at hi
  dsimp [q1_nu_transport_residual]
  linarith

/-- Incoming ν AC is equivalent to incoming AC of the explicit moving-axis residual. Neither
side is assumed here. This optional equivalence does not assert either AC property
and is independent of the proof of `mainTheorem`.
Paper `e1a0fd5`, `eq:logarithmic-expansions`, `eq:regular-axis`, lines 87–89, 220–275. -/
theorem ac_nu_in_iff_transport_residual_ac {ui v a b : ℝ} {S : SSFields}
    (h : StandingWithout_ac_nu_in ui S) (hab : a ≤ b)
    (hs : inSeg v a b ⊆ pastTriangle ui) :
    AbsolutelyContinuousOnInterval (fun u => S.nu u v) a b ↔
      AbsolutelyContinuousOnInterval (q1_nu_transport_residual S v) a b := by
  have hp : ∀ u ∈ uIcc a b, (u, v) ∈ pastTriangle ui := by
    intro u hu
    rw [uIcc_of_le hab] at hu
    exact hs ⟨hu, mem_singleton v⟩
  constructor
  · intro hac
    have hlog := positive_ac_log hac.fun_neg (fun u hu =>
      neg_pos.mpr (h.toQ1StandingCore.nu_neg (hp u hu)))
    exact hlog.congr (fun u hu => (q1_nu_transport_residual_eq h (hp u hu)).symm)
  · intro hac
    have hlog : AbsolutelyContinuousOnInterval (fun u => Real.log (-S.nu u v)) a b :=
      hac.congr (fun u hu => q1_nu_transport_residual_eq h (hp u hu))
    apply (q1_ac_exp hlog).fun_neg.congr
    intro u hu
    simp only [Real.exp_log (neg_pos.mpr (h.toQ1StandingCore.nu_neg (hp u hu))), neg_neg]

end AcExtensionPrinciple

end
