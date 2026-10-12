module

public import AcExtensionPrinciple.Minimal.OneSidedMixed

/-!
# Joint scalar axis traces from characteristic traces

Paper `e1a0fd5`, `equations.tex` lines 220–261,
`eq:axis-vanishing-variation`, `eq:regular-axis-scalar-traces`.
Past outgoing and future incoming variation control the two unmixed wedges.
The characteristic primitive equations and retained ν continuity control the
mixed rectangle. No joint normalized trace or λ continuity is an input.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- The one-sided normalized traces and vanishing scalar variation give the joint
off-axis scalar trace. Paper `e1a0fd5`, lines 220–261,
`eq:axis-vanishing-variation`, `eq:regular-axis-scalar-traces`. -/
theorem StandingAssumptions.oneSided_phi_axis_trace {ui a : ℝ} {S : SSFields}
    (h : StandingAssumptions ui S) (ha : (a, a) ∈ axis ui) :
    Tendsto (fun p : ℝ × ℝ => S.phi p.1 p.2)
      (𝓝[pastTriangle ui \ axis ui] (a, a)) (𝓝 (S.phi a a)) := by
  let V := a / 2
  let W := (a + V) / 2
  have haV : a < V := by dsimp [V]; linarith [ha.2.1]
  have hV : V < 0 := by dsimp [V]; linarith [ha.2.1]
  have haW : a < W := by dsimp [W]; linarith
  have hWV : W < V := by dsimp [W]; linarith
  obtain ⟨M, hM, hbound⟩ := h.oneSided_phi_local_bound (ha.1.trans haW.le) hWV hV
  let K := (Icc ui V ×ˢ Icc ui V) ∩ {p : ℝ × ℝ | p.1 ≤ p.2}
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc).inter_right
    (isClosed_le continuous_fst continuous_snd)
  have hKQ : K ⊆ pastTriangle ui := fun p hp =>
    ⟨hp.1.1.1, hp.1.1.2.trans_lt hV, hp.2, hp.1.2.2.trans hV.le⟩
  obtain ⟨c, hc, hcb⟩ := h.regularCenter.localBV.expansion_bounds K hK hKQ
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  let β := ε / 4
  have hβ : 0 < β := by dsimp [β]; positivity
  let B := M + |S.phi a a| + 1
  have hB : 0 < B := by dsimp [B]; positivity
  let η := β * c / B
  have hη : 0 < η := by dsimp [η]; positivity
  have hsmall : B * η ≤ β * c := le_of_eq (by dsimp [η]; field_simp)
  obtain ⟨δi, hδi, hi⟩ : ∃ δi : ℝ, 0 < δi ∧ ∀ u, ui ≤ u → u < a →
      dist u a < δi → dist (S.phi u a) (S.phi a a) < β := by
    by_cases hia : ui < a
    · obtain ⟨d, hd, hb⟩ := Metric.tendsto_nhdsWithin_nhds.mp
        (h.oneSided_phi_in ha hia) β hβ
      exact ⟨d, hd, fun u _ hua hdist => hb hua hdist⟩
    · exact ⟨1, zero_lt_one, fun u hui hua _ => False.elim (by linarith)⟩
  obtain ⟨δo, hδo, ho⟩ := Metric.tendsto_nhdsWithin_nhds.mp (h.oneSided_phi_out ha) β hβ
  have hvar := h.regularCenter.localBV.scalar_axis_variation a (axis_subset_pastTriangle ui ha)
  obtain ⟨δp, hδp, hpast⟩ := oneSided_variation_small hβ hvar.past_outgoing
  obtain ⟨δf, hδf, hfuture⟩ := oneSided_variation_small hβ hvar.future_incoming
  obtain ⟨δn, hδn, hn⟩ := Metric.continuousWithinAt_iff.mp
    (h.regularCenter.continuous_nu (a, a) (axis_subset_pastTriangle ui ha))
    (η / 2) (by positivity)
  refine ⟨min (min δi δo) (min (min δp δf) (min δn (min (W - a) (V - a)))),
    by positivity, ?_⟩
  intro p hp hpd
  have huv : p.1 < p.2 := by
    apply lt_of_le_of_ne hp.1.2.2.1
    intro he
    exact hp.2 ⟨hp.1.1, hp.1.2.1, he.symm⟩
  simp only [lt_min_iff] at hpd
  have hdu : ∀ d : ℝ, dist p (a, a) < d → dist p.1 a < d :=
    fun _ hd => (le_max_left _ _).trans_lt hd
  have hdv : ∀ d : ℝ, dist p (a, a) < d → dist p.2 a < d :=
    fun _ hd => (le_max_right _ _).trans_lt hd
  have huW : p.1 < W := by
    have hh := hdu _ hpd.2.2.2.1
    rw [Real.dist_eq, abs_lt] at hh
    linarith
  have hvV : p.2 < V := by
    have hh := hdv _ hpd.2.2.2.2
    rw [Real.dist_eq, abs_lt] at hh
    linarith
  by_cases hva : p.2 ≤ a
  · have hua : p.1 < a := huv.trans_le hva
    have hleft := hi p.1 hp.1.1 hua (hdu _ hpd.1.1)
    rcases hva.eq_or_lt with he | he
    · simpa only [he] using hleft.trans (by dsimp [β]; linarith)
    · have hs : {w | w ∈ Ioo p.1 a ∧ (p.1, w) ∈ pastTriangle ui} = Ioo p.1 a := by
        ext w
        constructor
        · exact fun hw => hw.1
        · intro hw
          exact ⟨hw, hp.1.1, hp.1.2.1, hw.1.le, hw.2.le.trans ha.2.1.le⟩
      have hsup : eVariationOn (S.phi p.1) (Ioo p.1 a) ≤ ENNReal.ofReal β := by
        have hb := hpast (a - p.1) ⟨sub_pos.mpr hua, by
          simpa only [Real.dist_eq, abs_of_neg (sub_neg.mpr hua), neg_sub] using hdu _ hpd.2.1.1⟩
        have hh : eVariationOn (S.phi (a - (a - p.1)))
            {w | w ∈ Ioo (a - (a - p.1)) a ∧ (a - (a - p.1), w) ∈ pastTriangle ui} ≤
            ENNReal.ofReal β := by
          apply le_trans ?_ hb
          exact le_iSup_of_le (a - p.1)
            (le_iSup_of_le (show a - p.1 ∈ Ioc 0 (a - p.1) from
              ⟨sub_pos.mpr hua, le_rfl⟩) le_rfl)
        simpa only [sub_sub_cancel, hs] using hh
      have hendpoint : Tendsto (S.phi p.1) (𝓝[<] a) (𝓝 (S.phi p.1 a)) := by
        have hcφ := h.oneSided_phi_out_interior hp.1.1 a ⟨hua, ha.2.1.le⟩
        exact hcφ.tendsto.mono_left (nhdsWithin_le_of_mem (by
          filter_upwards [Ioo_mem_nhdsLT hua] with w hw
          exact ⟨hw.1, hw.2.le.trans ha.2.1.le⟩))
      have hd := oneSided_variation_right_endpoint huv he hβ.le hsup hendpoint
      exact (dist_triangle (S.phi p.1 p.2) (S.phi p.1 a) (S.phi a a)).trans_lt
        (by dsimp [β] at *; linarith)
  · have hav : a < p.2 := lt_of_not_ge hva
    have hright := ho hav (hdv _ hpd.1.2)
    by_cases hau : a ≤ p.1
    · rcases hau.eq_or_lt with he | he
      · simpa only [← he] using hright.trans (by dsimp [β]; linarith)
      · have hs : {s | s ∈ Ioo a p.2 ∧ (s, p.2) ∈ pastTriangle ui} = Ioo a p.2 := by
          ext s
          constructor
          · exact fun hs => hs.1
          · intro hs
            exact ⟨hs, ha.1.trans hs.1.le, hs.2.trans_le hp.1.2.2.2,
              hs.2.le, hp.1.2.2.2⟩
        have hsup : eVariationOn (fun s => S.phi s p.2) (Ioo a p.2) ≤ ENNReal.ofReal β := by
          have hb := hfuture (p.2 - a) ⟨sub_pos.mpr hav, by
            simpa only [Real.dist_eq, abs_of_pos (sub_pos.mpr hav)] using hdv _ hpd.2.1.2⟩
          have hh : eVariationOn (fun s => S.phi s (a + (p.2 - a)))
              {s | s ∈ Ioo a (a + (p.2 - a)) ∧ (s, a + (p.2 - a)) ∈ pastTriangle ui} ≤
              ENNReal.ofReal β := by
            apply le_trans ?_ hb
            exact le_iSup_of_le (p.2 - a)
              (le_iSup_of_le (show p.2 - a ∈ Ioc 0 (p.2 - a) from
                ⟨sub_pos.mpr hav, le_rfl⟩) le_rfl)
          simpa only [add_sub_cancel, hs] using hh
        have hendpoint : Tendsto (fun s => S.phi s p.2) (𝓝[>] a) (𝓝 (S.phi a p.2)) := by
          have hcφ := h.oneSided_phi_in_interior hp.1.2.2.2 a ⟨ha.1, hav⟩
          exact hcφ.tendsto.mono_left (nhdsWithin_le_of_mem (by
            filter_upwards [Ioo_mem_nhdsGT hav] with s hs
            exact ⟨ha.1.trans hs.1.le, hs.2⟩))
        have hd := oneSided_variation_left_endpoint he huv hβ.le hsup hendpoint
        exact (dist_triangle (S.phi p.1 p.2) (S.phi a p.2) (S.phi a a)).trans_lt
          (by dsimp [β] at *; linarith)
    · have hua : p.1 < a := lt_of_not_ge hau
      have hleft := hi p.1 hp.1.1 hua (hdu _ hpd.1.1)
      have hb := h.oneSided_mixed_scalar_bound hp.1.1 hua hav hp.1.2.2.2 hB.le hη.le hβ.le
        (h.oneSided_radius_lower hp.1 huv.le (by
          intro t ht
          exact (hcb (p.1, t) ⟨⟨⟨hp.1.1, huW.le.trans hWV.le⟩,
            ⟨hp.1.1.trans ht.1, ht.2.trans hvV.le⟩⟩, ht.1⟩).1)) hsmall
        (by
          intro s hs t ht
          have hst : (s, t) ∈ pastTriangle ui :=
            ⟨hp.1.1.trans hs.1.le, hs.2.trans ha.2.1, hs.2.le.trans ht.1, ht.2.trans hp.1.2.2.2⟩
          have hh := hbound (s, t) hst (hs.2.le.trans haW.le) (ht.2.trans hvV.le)
          exact (abs_sub _ _).trans (by dsimp [B]; linarith))
        (by
          intro s hs
          have hna := hn (show (s, a) ∈ pastTriangle ui from
            ⟨hp.1.1.trans hs.1.le, hs.2.trans ha.2.1, hs.2.le, ha.2.1.le⟩)
            (oneSided_box_near hpd.2.2.1 ⟨hs.1.le, hs.2.le.trans hav.le⟩ ⟨hua.le, hav.le⟩)
          have hnv := hn (show (s, p.2) ∈ pastTriangle ui from
            ⟨hp.1.1.trans hs.1.le, hs.2.trans ha.2.1, hs.2.le.trans hav.le, hp.1.2.2.2⟩)
            (oneSided_box_near hpd.2.2.1 ⟨hs.1.le, hs.2.le.trans hav.le⟩ ⟨huv.le, le_rfl⟩)
          rw [Real.dist_eq, abs_lt] at hna hnv
          linarith)
        (by simpa only [Real.dist_eq] using hleft.le)
        (by simpa only [Real.dist_eq] using hright.le)
      rw [Real.dist_eq]
      exact hb.trans_lt (by dsimp [β]; linarith)

end AcExtensionPrinciple

end
