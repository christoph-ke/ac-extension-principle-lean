module

public import AcExtensionPrinciple.Continuation.InverseCalculus
public import AcExtensionPrinciple.Continuation.GaugeCore
public import AcExtensionPrinciple.Continuation.GaugeBounds

/-!
# The transformed original solution satisfies the uniqueness class

Paper `e1a0fd5`, `equations.tex` lines 1390–1411, original class membership in the continuation
chart. All analytic component premises are discharged from StandingFull. The total chart uses the
auxiliary left extension in RadialChart.
-/

public section

namespace AcExtensionPrinciple

open Set Filter
open scoped Topology ENNReal

/-- Selected-cone Jacobian, extended constantly beyond both endpoints.
Paper `e1a0fd5`, `eq:continuation-null-gauge`, lines 1393–1400 and 1422. -/
@[expose] noncomputable def selectedJacobian (S : SSFields) (ū : ℝ) : ℝ → ℝ :=
  radialChartDerivative (S.lam ū) ū

/-- The standing class supplies the full chart construction, including BV of
its Jacobian on the selected cone. Paper `e1a0fd5`, lines 1390–1422. -/
theorem StandingFull.selected_chart {ui ū : ℝ} {S : SSFields}
    (h : StandingFull ui S) (hū : ū ∈ Ioo ui 0) :
    ∃ T : ℝ ≃o ℝ,
      (T : ℝ → ℝ) = radialChartMap (S.r ū) (S.lam ū) ū ∧
      T ū = 0 ∧ T 0 = 2 * S.r ū 0 ∧
      (∀ x, HasDerivAt (T : ℝ → ℝ) (selectedJacobian S ū x) x) ∧
      Continuous (selectedJacobian S ū) ∧
      (∃ c : ℝ, 0 < c ∧ ∀ x, c ≤ selectedJacobian S ū x) ∧
      BoundedVariationOn (selectedJacobian S ū) (Icc ū 0) := by
  have hs := outSeg_subset_triangle hū.1.le hū.2 le_rfl le_rfl
  have hlam := StandingFull.continuous_out h.regularCenter.continuous_lam hs
  have hg : ∀ x ∈ Icc ū 0, HasDerivWithinAt (S.r ū) (S.lam ū x) (Icc ū 0) x := by
    intro x hx
    apply hasDerivWithinAt_of_intervalPrimitives (fun y hy =>
      h.regularCenter.localBV.radius_out ū ū y hy.1
        ((prod_mono_right (Icc_subset_Icc le_rfl hy.2)).trans hs)) hlam hx
  have hg0 := (h.regularCenter.localBV.axis_values ū
    (axis_subset_pastTriangle ui ⟨hū.1.le, hū.2, rfl⟩)).1
  rcases h.regularCenter.localBV.expansion_bounds (outSeg ū ū 0)
    (isCompact_singleton.prod isCompact_Icc) hs with ⟨c, hc, hb⟩
  have hl : ∀ x ∈ Icc ū 0, c ≤ S.lam ū x := fun x hx => (hb (ū, x) ⟨by simp, hx⟩).1
  obtain ⟨T, hT⟩ := radialChartMap_orderIso hū.2 hc hg0 hg hlam hl
  have hD := radialChartDerivative_properties hū.2.le hlam hl
  have hdBV : BoundedVariationOn (S.lam ū) (Icc ū 0) := by
    simpa only [uIcc_of_le hū.2.le]
      using (h.regularCenter.ac_lam_out ū ū 0 hū.2.le hs).boundedVariationOn
  have hBV : BoundedVariationOn (selectedJacobian S ū) (Icc ū 0) := by
    change eVariationOn (selectedJacobian S ū) (Icc ū 0) ≠ ⊤
    have he : EqOn (selectedJacobian S ū) (continuationDerivative (S.lam ū)) (Icc ū 0) := by
      intro x hx
      rw [selectedJacobian, radialChartDerivative_on_interval hx,
        continuationDerivative_of_nonpos _ hx.2]
    rw [eVariationOn.congr he]
    exact boundedVariation_continuationDerivative hū.2.le hdBV
  refine ⟨T, hT, ?_, ?_, ?_, hD.1, ⟨2 * c, by positivity, hD.2⟩, hBV⟩
  · rw [hT]
    simp [radialChartMap]
  · rw [hT]
    exact radialChartMap_on_interval hū.2.le hg0 0 ⟨hū.2.le, le_rfl⟩
  · intro x
    rw [hT]
    exact radialChartMap_hasDerivAt hū.2.le hg0 hg x

/-- Raw variations decrease on an off-axis restriction. Paper `e1a0fd5`, lines 220–275 and 1411,
class-membership component. -/
theorem RawRayVariation.restrict {D E : Set (ℝ × ℝ)} {S : SSFields} {C : ℝ≥0∞}
    (h : RawRayVariation D S C) (hED : E ⊆ D) : RawRayVariation E S C := by
  constructor
  · intro u
    have hs : {v | (u, v) ∈ E} ⊆ {v | (u, v) ∈ D} := fun _ hv => hED hv
    exact ⟨(eVariationOn.mono _ hs).trans (h.outgoing u).1,
      (eVariationOn.mono _ hs).trans (h.outgoing u).2.1,
      (eVariationOn.mono _ hs).trans (h.outgoing u).2.2⟩
  · intro v
    have hs : {u | (u, v) ∈ E} ⊆ {u | (u, v) ∈ D} := fun _ hu => hED hu
    exact ⟨(eVariationOn.mono _ hs).trans (h.incoming v).1,
      (eVariationOn.mono _ hs).trans (h.incoming v).2.1,
      (eVariationOn.mono _ hs).trans (h.incoming v).2.2⟩

/-- Every adjacent axis parameter of pastSet a b is at most a.
Paper `e1a0fd5`, line 1411. -/
theorem pastSet_adjacentAxis_le (a b : ℝ) : adjacentAxis (pastSet a b) ⊆ Iic a := by
  intro t ht
  exact (closure_minimal (fun p hp => hp.1.2)
    (isClosed_le continuous_fst continuous_const)) ht

/-- In a constructed selected chart: every proper causal past of the transformed original solution
satisfies the exact E2 class, including v = ṽ₀. Paper `e1a0fd5`, lines 1390–1411. The chart premises
here are supplied in `selected_chart`; none is an additional hypothesis on the source solution. -/
theorem StandingFull.chr_in_selected_chart {ui ū : ℝ} {S : SSFields}
    (h : StandingFull ui S) (hū : ū ∈ Ioo ui 0)
    {T : ℝ ≃o ℝ} (hvertex : T ū = 0) (hterminal : T 0 = 2 * S.r ū 0)
    (hder : ∀ x, HasDerivAt (T : ℝ → ℝ) (selectedJacobian S ū x) x)
    (hdc : Continuous (selectedJacobian S ū))
    (hpos : ∃ c : ℝ, 0 < c ∧ ∀ x, c ≤ selectedJacobian S ū x)
    (hBV : BoundedVariationOn (selectedJacobian S ū) (Icc ū 0)) :
    ∀ a ∈ Ico 0 (2 * S.r ū 0),
      ChristodoulouBV (pastSet a (2 * S.r ū 0))
        (adjacentAxis (pastSet a (2 * S.r ū 0)))
        (S.pullback T.symm (inverseJacobian T (selectedJacobian S ū))) := by
  let b := 2 * S.r ū 0
  let dU := inverseJacobian T (selectedJacobian S ū)
  have hb : 0 < b := mul_pos (by norm_num) (h.r_pos ⟨hū.1.le, hū.2, hū.2.le, le_rfl⟩ hū.2)
  rcases hpos with ⟨cl, hcl, hl⟩
  have hdp := inverseJacobian_continuous_pos (T := T) hdc (fun x => hcl.trans_le (hl x))
  have hdi := inverseJacobian_hasDerivAt (T := T) hder (fun x => ne_of_gt (hcl.trans_le (hl x)))
  rcases inverseJacobian_compact_bounds hū.2.le hb.le hvertex hterminal hdc hcl hl hBV
    with ⟨hduBV, q, J, hq, hJ, hduBounds⟩
  have hUa : T.symm 0 = ū := by rw [← hvertex, T.symm_apply_apply]
  have hUb : T.symm b = 0 := by
    change T.symm (2 * S.r ū 0) = 0
    rw [← hterminal, T.symm_apply_apply]
  intro a ha
  let c := T.symm a
  have hc : c < 0 := by
    change T.symm a < 0
    rw [← hUb]
    exact T.symm.strictMono ha.2
  have hūc : ū ≤ c := by
    change ū ≤ T.symm a
    rw [← hUa]
    exact T.symm.monotone ha.1
  let D := offAxis (properOriginalTriangle ū c)
  let E := pastSet a b
  let A := adjacentAxis E
  have hmap : ∀ p ∈ E, (T.symm p.1, T.symm p.2) ∈ D := by
    intro p hp
    refine ⟨⟨⟨?_, T.symm.monotone hp.1.2⟩, (T.symm.strictMono hp.2.1).le, ?_⟩, ?_⟩
    · simpa only [hUa] using T.symm.monotone hp.1.1
    · simpa only [hUb] using T.symm.monotone hp.2.2
    · exact ne_of_lt (T.symm.strictMono hp.2.1)
  have hI : ∀ p ∈ E, p.1 ∈ Icc 0 b ∧ p.2 ∈ Icc 0 b :=
    fun p hp => ⟨⟨hp.1.1, hp.1.2.trans ha.2.le⟩,
      hp.1.1.trans hp.2.1.le, hp.2.2⟩
  have hA : ∀ t ∈ A, T.symm t ∈ Icc ū c := by
    intro t ht
    exact ⟨(by simpa only [hUa] using T.symm.monotone (pastSet_adjacentAxis_nonneg a b ht)),
      T.symm.monotone (pastSet_adjacentAxis_le a b ht)⟩
  have hAI : A ⊆ Icc 0 b := fun t ht =>
    ⟨pastSet_adjacentAxis_nonneg a b ht, (pastSet_adjacentAxis_le a b ht).trans ha.2.le⟩
  have hsource := h.chr_on_proper_triangle hū.1.le hc
  rcases h.proper_triangle_raw_bounds ⟨hū.1.le, hū.2⟩ hc with ⟨M, hM⟩
  have hraw : ∀ p ∈ D, |S.lam p.1 p.2| ≤ |M| ∧ |S.nu p.1 p.2| ≤ |M| ∧
      |S.phi p.1 p.2| ≤ |M| ∧ |S.dvpsi p.1 p.2| ≤ |M| ∧ |S.dupsi p.1 p.2| ≤ |M| := by
    intro p hp
    rcases hM p hp with ⟨hl, hn, hp, hv, hu⟩
    exact ⟨hl.trans (le_abs_self M), hn.trans (le_abs_self M), hp.trans (le_abs_self M),
      hv.trans (le_abs_self M), hu.trans (le_abs_self M)⟩
  rcases h.proper_triangle_raw_variation hū.1.le hc with ⟨C, hC, hTV⟩
  rcases hsource.2.expansion_bounds with ⟨k, N, hk, hbounds⟩
  refine ⟨hsource.1.pullback T.symm.strictMono T.symm.continuous hmap hA hAI hI
    (fun x y _ _ t _ => (hdi t).hasDerivWithinAt)
    (fun x _ => hdp.2 x) hdp.1.continuousOn ?_, ?_⟩
  · intro t ht
    refine ⟨|M|, ?_⟩
    have hev : ∀ᶠ v in 𝓝[>] t ⊓ 𝓟 {v | (t, v) ∈ E}, (t, v) ∈ E :=
      Filter.Eventually.filter_mono inf_le_right (by simp)
    exact hev.mono (fun v hv => ⟨(hraw _ (hmap (t, v) hv)).1,
      (hraw _ (hmap (t, v) hv)).2.2.2.1⟩)
  · exact chr_pullback_bounds_of_raw hk hq (abs_nonneg M) hJ hC hduBV T.symm.monotone
      hmap hI (fun p hp => (hbounds p ⟨mem_univ _, hp⟩).1) hraw
      (hTV.restrict sdiff_subset) hduBounds le_rfl

/-- Under the standing assumptions there is the exact radial chart and all transformed proper pasts
satisfy ChristodoulouBV. Paper `e1a0fd5`, `eq:continuation-null-gauge`, lines 1390–1411. -/
theorem StandingFull.exists_selected_chart_bv {ui ū : ℝ} {S : SSFields}
    (h : StandingFull ui S) (hū : ū ∈ Ioo ui 0) :
    ∃ T : ℝ ≃o ℝ, (∀ t ∈ Icc ū 0, T t = 2 * S.r ū t) ∧
      ∀ a ∈ Ico 0 (2 * S.r ū 0),
        ChristodoulouBV (pastSet a (2 * S.r ū 0))
          (adjacentAxis (pastSet a (2 * S.r ū 0)))
          (S.pullback T.symm (inverseJacobian T (selectedJacobian S ū))) := by
  rcases h.selected_chart hū with ⟨T, hT, hv, ht, hd, hc, hp, hBV⟩
  have hg0 := (h.regularCenter.localBV.axis_values ū
    (axis_subset_pastTriangle ui ⟨hū.1.le, hū.2, rfl⟩)).1
  refine ⟨T, ?_, h.chr_in_selected_chart hū hv ht hd hc hp hBV⟩
  intro t ht
  rw [hT]
  exact radialChartMap_on_interval hū.2.le hg0 t ht

end AcExtensionPrinciple

end
