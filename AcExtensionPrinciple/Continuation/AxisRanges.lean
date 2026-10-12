module

public import AcExtensionPrinciple.Continuation.Domain

/-!
# Reconciling the δ-ranges in the two axis definitions

Paper `e1a0fd5`, `equations.tex` lines 220–275 and 1411, Q5.
Christodoulou's incoming-past and outgoing-future families include δ = 0.
Joint scalar continuity in the original regular-center class supplies these
extra members; the δ = ε members discarded by Christodoulou cause no problem.
-/

public section

namespace AcExtensionPrinciple

open Set Filter
open scoped Topology ENNReal

/-- Pointwise convergence and eventual membership of each sample preserve a
uniform variation bound, even when the sets vary. Paper `e1a0fd5`, line 1411,
component for Christodoulou's δ = 0 conditions. -/
theorem variation_le_of_sample_limits {ι : Type*} {L : Filter ι} [NeBot L]
    {F : ι → ℝ → ℝ} {f : ℝ → ℝ} {s : Set ℝ} {sI : ι → Set ℝ} {C : ℝ≥0∞}
    (ht : ∀ x ∈ s, Tendsto (fun i => F i x) L (𝓝 (f x)))
    (hm : ∀ x ∈ s, ∀ᶠ i in L, x ∈ sI i)
    (hb : ∀ᶠ i in L, eVariationOn (F i) (sI i) ≤ C) : eVariationOn f s ≤ C := by
  apply iSup_le
  rintro ⟨n, u, hu, hs⟩
  have hlim : Tendsto (fun j => ∑ i ∈ Finset.range n,
      edist (F j (u (i + 1))) (F j (u i))) L
      (𝓝 (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)))) :=
    tendsto_finsetSum _ (fun i _ => (ht _ (hs _)).edist (ht _ (hs _)))
  apply le_of_tendsto hlim
  have hfinite : ∀ᶠ j in L, ∀ i ∈ Finset.range (n + 1), u i ∈ sI j :=
    (eventually_all_finset _).mpr (fun i _ => hm _ (hs i))
  filter_upwards [hfinite, hb] with j hj hbj
  let w : ℕ → ℝ := fun k => u (min k n)
  have hw : Monotone w := hu.comp (monotone_id.min monotone_const)
  have hwm : ∀ k, w k ∈ sI j := fun k => hj _
    (Finset.mem_range.mpr (Nat.lt_succ_of_le (min_le_right _ _)))
  have he : (∑ i ∈ Finset.range n, edist (F j (u (i + 1))) (F j (u i))) =
      ∑ i ∈ Finset.range n, edist (F j (w (i + 1))) (F j (w i)) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    simp only [w, Nat.min_eq_left (by omega : i + 1 ≤ n),
      Nat.min_eq_left (by omega : i ≤ n)]
  rw [he]
  exact (eVariationOn.sum_le hw hwm).trans hbj

/-- The original scalar continuity supplies the δ = 0 past-incoming member.
Paper `e1a0fd5`, lines 220–275 and 1411, Q5, Christodoulou item 4. -/
theorem past_incoming_zero_le {ui a ε : ℝ} {S : SSFields} (hε : 0 < ε)
    (ha : (a, a) ∈ axis ui)
    (hc : ContinuousOn (fun p => S.phi p.1 p.2) (pastTriangle ui)) :
    eVariationOn (fun u => S.phi u a)
      {u | u ∈ Ioo (a - ε) a ∧ (u, a) ∈ pastTriangle ui} ≤
    ⨆ δ ∈ Ioc 0 ε, eVariationOn (fun u => S.phi u (a - δ))
      {u | u ∈ Ioo (a - ε) (a - δ) ∧ (u, a - δ) ∈ pastTriangle ui} := by
  apply variation_le_of_sample_limits (L := 𝓝[>] (0 : ℝ))
    (F := fun δ u => S.phi u (a - δ))
    (sI := fun δ => {u | u ∈ Ioo (a - ε) (a - δ) ∧
      (u, a - δ) ∈ pastTriangle ui})
  · intro u hu
    have hmem : ∀ᶠ δ in 𝓝[>] (0 : ℝ), (u, a - δ) ∈ pastTriangle ui := by
      filter_upwards [Ioo_mem_nhdsGT (sub_pos.mpr hu.1.2)] with δ hδ
      exact ⟨hu.2.1, hu.2.2.1, by linarith [hδ.2], by linarith [ha.2.1, hδ.1]⟩
    have ht : Tendsto (fun δ : ℝ => (u, a - δ)) (𝓝[>] 0) (𝓝 (u, a)) := by
      simpa using (continuous_const.prodMk (continuous_const.sub continuous_id)).tendsto
        (0 : ℝ) |>.mono_left nhdsWithin_le_nhds
    exact (hc (u, a) hu.2).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨ht, hmem⟩)
  · intro u hu
    filter_upwards [Ioo_mem_nhdsGT (sub_pos.mpr hu.1.2)] with δ hδ
    exact ⟨⟨hu.1.1, by linarith [hδ.2]⟩, hu.2.1, hu.2.2.1,
      by linarith [hδ.2], by linarith [ha.2.1, hδ.1]⟩
  · filter_upwards [Ioo_mem_nhdsGT hε] with δ hδ
    exact le_iSup_of_le δ (le_iSup_of_le ⟨hδ.1, hδ.2.le⟩ le_rfl)

/-- The original scalar continuity supplies the δ = 0 future-outgoing member.
Paper `e1a0fd5`, lines 220–275 and 1411, Q5, Christodoulou item 4. -/
theorem future_outgoing_zero_le {ui a ε : ℝ} {S : SSFields} (hε : 0 < ε)
    (ha : (a, a) ∈ axis ui)
    (hc : ContinuousOn (fun p => S.phi p.1 p.2) (pastTriangle ui)) :
    eVariationOn (S.phi a)
      {v | v ∈ Ioo a (a + ε) ∧ (a, v) ∈ pastTriangle ui} ≤
    ⨆ δ ∈ Ioc 0 ε, eVariationOn (S.phi (a + δ))
      {v | v ∈ Ioo (a + δ) (a + ε) ∧ (a + δ, v) ∈ pastTriangle ui} := by
  apply variation_le_of_sample_limits (L := 𝓝[>] (0 : ℝ))
    (F := fun δ v => S.phi (a + δ) v)
    (sI := fun δ => {v | v ∈ Ioo (a + δ) (a + ε) ∧
      (a + δ, v) ∈ pastTriangle ui})
  · intro v hv
    have hmem : ∀ᶠ δ in 𝓝[>] (0 : ℝ), (a + δ, v) ∈ pastTriangle ui := by
      filter_upwards [Ioo_mem_nhdsGT (sub_pos.mpr hv.1.1),
        Ioo_mem_nhdsGT (neg_pos.mpr ha.2.1)] with δ hδ hδ0
      exact ⟨by linarith [ha.1, hδ.1], by linarith [hδ0.2],
        by linarith [hδ.2], hv.2.2.2.2⟩
    have ht : Tendsto (fun δ : ℝ => (a + δ, v)) (𝓝[>] 0) (𝓝 (a, v)) := by
      simpa using ((continuous_const.add continuous_id).prodMk continuous_const).tendsto
        (0 : ℝ) |>.mono_left nhdsWithin_le_nhds
    exact (hc (a, v) hv.2).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨ht, hmem⟩)
  · intro v hv
    filter_upwards [Ioo_mem_nhdsGT (sub_pos.mpr hv.1.1),
      Ioo_mem_nhdsGT (neg_pos.mpr ha.2.1)] with δ hδ hδ0
    exact ⟨⟨by linarith [hδ.2], hv.1.2⟩, by linarith [ha.1, hδ.1],
      by linarith [hδ0.2], by linarith [hδ.2], hv.2.2.2.2⟩
  · filter_upwards [Ioo_mem_nhdsGT hε] with δ hδ
    exact le_iSup_of_le δ (le_iSup_of_le ⟨hδ.1, hδ.2.le⟩ le_rfl)

/-- Q5 with original scalar continuity implies precisely Christodoulou's
four original δ-ranges at every regular axis point. Paper `e1a0fd5`,
lines 220–275 and 1411. This is a proved conversion, not an extra hypothesis. -/
theorem RegularCenterFull.chr_axis_variation {ui a : ℝ} {S : SSFields}
    (h : RegularCenterFull ui S) (ha : (a, a) ∈ axis ui) :
    ChrAxisVanishingVariation (pastTriangle ui) S a := by
  have hv := h.localBV.scalar_axis_variation a (axis_subset_pastTriangle ui ha)
  constructor
  · exact hv.past_outgoing
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hv.past_incoming
    · exact Eventually.of_forall (fun _ => zero_le)
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      apply iSup_le
      intro δ
      apply iSup_le
      intro hδ
      rcases eq_or_lt_of_le hδ.1 with rfl | hδpos
      · simpa using past_incoming_zero_le hε ha h.continuous_phi
      · exact le_iSup_of_le δ (le_iSup_of_le ⟨hδpos, hδ.2.le⟩ le_rfl)
  · exact hv.future_incoming
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hv.future_outgoing
    · exact Eventually.of_forall (fun _ => zero_le)
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      apply iSup_le
      intro δ
      apply iSup_le
      intro hδ
      rcases eq_or_lt_of_le hδ.1 with rfl | hδpos
      · simpa using future_outgoing_zero_le hε ha h.continuous_phi
      · exact le_iSup_of_le δ (le_iSup_of_le ⟨hδpos, hδ.2.le⟩ le_rfl)

end AcExtensionPrinciple

end
