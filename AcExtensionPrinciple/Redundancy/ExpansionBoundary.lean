module

public import AcExtensionPrinciple.Redundancy.ExpansionInterior

/-!
# Expansion continuity at the regular boundary
Paper commit `e1a0fd5`, `equations.tex` lines 66–84 and 220–275,
`eq:radius`, `eq:regular-axis`. The outgoing expansion limit and retained
λ continuity extend ν antitonicity to the axis and give joint ν continuity.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- The one-sided expansion sum and retained λ continuity fix the outgoing ν trace.
Paper `e1a0fd5`, line 222 and `eq:regular-axis`. -/
theorem q1_nu_axis_out_continuous {ui u : ℝ} {S : SSFields}
    (h : StandingWithout_continuous_nu ui S) (hu : ui ≤ u) (hu0 : u < 0) :
    ContinuousWithinAt (S.nu u) (Icc u 0) u := by
  have hp : (u, u) ∈ pastTriangle ui := ⟨hu, hu0, le_rfl, hu0.le⟩
  have hl : ContinuousWithinAt (S.lam u) (Icc u 0) u :=
    (h.continuous_lam (u, u) hp).comp_of_eq
      (continuous_const.prodMk continuous_id).continuousWithinAt
      (fun w hw => ⟨hu, hu0, hw⟩) rfl
  have ht : Tendsto (fun w : ℝ => w - u) (𝓝[Icc u 0 \ {u}] u) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa using ((continuous_id.tendsto u).mono_left
        (nhdsWithin_le_nhds : 𝓝[Icc u 0 \ {u}] u ≤ 𝓝 u)).sub_const u
    · filter_upwards [self_mem_nhdsWithin] with w hw
      exact sub_pos.mpr (lt_of_le_of_ne hw.1.1 (by simpa [eq_comm] using hw.2))
  have hs := (h.regularCenter.localBV.expansion_axis_limit u hp).comp ht
  have hn := hs.sub (hl.mono sdiff_subset).tendsto
  have ha := h.regularCenter.axis_expansions u (show (u, u) ∈ axis ui from
    ⟨hu, hu0, rfl⟩)
  apply continuousWithinAt_sdiff_self.mp
  simpa only [ContinuousWithinAt, Function.comp_apply, add_sub_cancel_left,
    add_sub_cancel, add_sub_cancel_right, sub_add_cancel, zero_sub, ha] using hn

/-- Outgoing ν antitonicity also compares an off-axis value with its stored axis value.
Paper `e1a0fd5`, `eq:radius`, `eq:regular-axis`, lines 220–275. -/
theorem q1_nu_out_le_axis {ui u v : ℝ} {S : SSFields}
    (h : StandingWithout_continuous_nu ui S) (hp : (u, v) ∈ pastTriangle ui) :
    S.nu u v ≤ S.nu u u := by
  rcases hp.2.2.1.eq_or_lt with he | he
  · change u = v at he
    rw [← he]
  have hc := q1_nu_axis_out_continuous h hp.1 hp.2.1
  have hlim : Tendsto (S.nu u) (𝓝[>] u) (𝓝 (S.nu u u)) := by
    rw [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsGE hp.2.1] at hc
    exact hc.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
  exact ge_of_tendsto hlim (by
    filter_upwards [self_mem_nhdsWithin,
      ((continuous_id.tendsto u).mono_left nhdsWithin_le_nhds).eventually
        (Iio_mem_nhds he)]
      with w hw hwv
    exact h.toQ1StandingCore.nu_out_antitone
      (outSeg_subset_offAxis hp.1 hp.2.1 hw hp.2.2.2)
      ⟨le_rfl, hwv.le⟩ ⟨hwv.le, le_rfl⟩ hwv.le)

/-- ν is antitone on the whole outgoing segment, including its regular axis endpoint.
Paper `e1a0fd5`, `eq:radius`, `eq:regular-axis`, lines 220–275. -/
theorem q1_nu_out_antitone_closed {ui u : ℝ} {S : SSFields}
    (h : StandingWithout_continuous_nu ui S) (hu : ui ≤ u) (hu0 : u < 0) :
    AntitoneOn (S.nu u) (Icc u 0) := by
  intro x hx y hy hxy
  by_cases he : u = x
  · rw [← he]
    exact q1_nu_out_le_axis h ⟨hu, hu0, hy⟩
  · exact h.toQ1StandingCore.nu_out_antitone
      (outSeg_subset_offAxis hu hu0 (lt_of_le_of_ne hx.1 he) hy.2)
      ⟨le_rfl, hxy⟩ ⟨hxy, le_rfl⟩ hxy

/-- Proper rectangles give continuity everywhere off-axis, including the initial side and v = 0.
Paper `e1a0fd5`, `eq:radius`, lines 220–275. -/
theorem continuous_nu_offAxis_of_rest {ui : ℝ} {S : SSFields}
    (h : StandingWithout_continuous_nu ui S)
    (hin : ∀ v a b, a ≤ b → inSeg v a b ⊆ pastTriangle ui →
      ContinuousOn (fun u => S.nu u v) (Icc a b)) :
    ContinuousOn (fun p => S.nu p.1 p.2) (pastTriangle ui \ axis ui) := by
  intro p hp
  have hpa : p.1 < p.2 := by
    exact lt_of_le_of_ne hp.1.2.2.1 (fun he => hp.2 ⟨hp.1.1, hp.1.2.1, he.symm⟩)
  let U := (p.1 + p.2) / 2
  let a := (U + p.2) / 2
  have hpU : p.1 < U := by dsimp [U]; linarith
  have hUa : U < a := by dsimp [a, U]; linarith
  have hap : a < p.2 := by dsimp [a, U]; linarith
  have hU : U < 0 := by dsimp [U]; linarith [hp.1.2.1, hp.1.2.2.2]
  have hc := continuous_nu_rectangle_of_rest h hin (hp.1.1.trans hpU.le)
    (hap.le.trans hp.1.2.2.2) hU hUa le_rfl
  apply (hc p ⟨⟨hp.1.1, hpU.le⟩, ⟨hap.le, hp.1.2.2.2⟩⟩).mono_of_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin,
    ((continuous_fst.tendsto p).eventually (Iio_mem_nhds hpU)).filter_mono
      nhdsWithin_le_nhds,
    ((continuous_snd.tendsto p).eventually (Ioi_mem_nhds hap)).filter_mono
      nhdsWithin_le_nhds] with q hq hqU hqa
  exact ⟨⟨hq.1.1, hqU.le⟩, ⟨hqa.le, hq.1.2.2.2⟩⟩

/-- The joint ν continuity field is redundant given incoming continuity of ν (`hin`). At the axis, outgoing antitonicity squeezes ν
between a fixed off-axis outgoing value and its continuous diagonal value −λ.
Paper `e1a0fd5`, `eq:radius`, `eq:regular-axis`, lines 220–275. -/
theorem continuous_nu_of_rest {ui : ℝ} {S : SSFields}
    (h : StandingWithout_continuous_nu ui S)
    (hin : ∀ v a b, a ≤ b → inSeg v a b ⊆ pastTriangle ui →
      ContinuousOn (fun u => S.nu u v) (Icc a b)) :
    ContinuousOn (fun p => S.nu p.1 p.2) (pastTriangle ui) := by
  intro p hp
  rcases hp.2.2.1.eq_or_lt with he | he
  · change p.1 = p.2 at he
    have ha : (p.1, p.1) ∈ axis ui := ⟨hp.1, hp.2.1, rfl⟩
    have hp0 := hp.2.1
    have hdiag : ContinuousWithinAt (fun q : ℝ × ℝ => S.nu q.1 q.1)
        (pastTriangle ui) p := by
      have hc := (h.continuous_lam (p.1, p.1) (axis_subset_pastTriangle ui ha)).neg
      have ht : ContinuousWithinAt (fun q : ℝ × ℝ => (q.1, q.1))
          (pastTriangle ui) p := (continuous_fst.prodMk continuous_fst).continuousWithinAt
      have hc' := hc.comp_of_eq ht
        (fun q hq => ⟨hq.1, hq.2.1, le_rfl, hq.2.1.le⟩) rfl
      apply hc'.congr_of_eventuallyEq_of_mem ?_ hp
      filter_upwards [self_mem_nhdsWithin] with q hq
      exact h.regularCenter.axis_expansions q.1 ⟨hq.1, hq.2.1, rfl⟩
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    obtain ⟨δd, hδd, hd⟩ := Metric.continuousWithinAt_iff.mp hdiag (ε / 3)
      (by positivity)
    have hout := q1_nu_axis_out_continuous h hp.1 hp.2.1
    obtain ⟨δo, hδo, ho⟩ := Metric.continuousWithinAt_iff.mp hout (ε / 3)
      (by positivity)
    let V := p.1 + min (-p.1 / 2) (δo / 2)
    have hpV : p.1 < V := by
      dsimp [V]
      have hm : 0 < min (-p.1 / 2) (δo / 2) :=
        lt_min (div_pos (neg_pos.mpr hp0) (by norm_num)) (by positivity)
      linarith
    have hV0 : V ≤ 0 := by dsimp [V]; linarith [min_le_left (-p.1 / 2) (δo / 2)]
    have hVo : dist V p.1 < δo := by
      rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hpV)]
      dsimp [V]
      linarith [min_le_right (-p.1 / 2) (δo / 2)]
    have hoV := ho ⟨hpV.le, hV0⟩ hVo
    let U := (p.1 + V) / 2
    have hpU : p.1 < U := by dsimp [U]; linarith
    have hUV : U < V := by dsimp [U]; linarith
    have hU0 : U < 0 := hUV.trans_le hV0
    have hc := continuous_nu_rectangle_of_rest h hin (hp.1.trans hpU.le)
      (show V ≤ V from le_rfl) hU0 hUV hV0
    have hslice : ContinuousWithinAt (fun q : ℝ × ℝ => S.nu q.1 V)
        {q | q.1 ∈ Icc ui U} p :=
      (hc (p.1, V) ⟨⟨hp.1, hpU.le⟩, le_rfl, le_rfl⟩).comp_of_eq
        (continuous_fst.prodMk continuous_const).continuousWithinAt
        (fun q hq => ⟨hq, le_rfl, le_rfl⟩) rfl
    obtain ⟨δs, hδs, hs⟩ := Metric.continuousWithinAt_iff.mp hslice (ε / 3)
      (by positivity)
    refine ⟨min δd (min δs (U - p.1)), by positivity, ?_⟩
    intro q hq hqp
    have hqd := lt_of_lt_of_le hqp (min_le_left _ _)
    have hqs := lt_of_lt_of_le hqp ((min_le_right _ _).trans (min_le_left _ _))
    have hqUdist := lt_of_lt_of_le hqp ((min_le_right _ _).trans (min_le_right _ _))
    have hqU : q.1 < U := by
      have hf := (show dist q.1 p.1 ≤ dist q p from le_max_left _ _).trans_lt hqUdist
      rw [Real.dist_eq, abs_lt] at hf
      linarith
    have hqV : q.2 < V := by
      have hf := (show dist q.2 p.2 ≤ dist q p from le_max_right _ _).trans_lt hqUdist
      rw [Real.dist_eq, abs_lt, ← he] at hf
      linarith
    have hlo := q1_nu_out_antitone_closed h hq.1 hq.2.1 hq.2.2
      ⟨(hq.2.2.1.trans hqV.le), hV0⟩ hqV.le
    have hhi := q1_nu_out_le_axis h hq
    have hdq := hd hq hqd
    have hsq := hs (show q ∈ {q | q.1 ∈ Icc ui U} from ⟨hq.1, hqU.le⟩) hqs
    rw [Real.dist_eq, abs_lt] at hdq hsq hoV ⊢
    rw [← he] at ⊢
    constructor <;> linarith
  · apply (continuous_nu_offAxis_of_rest h hin p ⟨hp, ?_⟩).mono_of_mem_nhdsWithin
    · filter_upwards [self_mem_nhdsWithin,
        (Filter.Eventually.filter_mono nhdsWithin_le_nhds
          (isOpen_lt continuous_fst continuous_snd |>.mem_nhds he))] with q hq hqa
      exact ⟨hq, fun ha => hqa.ne ha.2.2.symm⟩
    · intro ha
      exact he.ne ha.2.2.symm

end AcExtensionPrinciple

end
