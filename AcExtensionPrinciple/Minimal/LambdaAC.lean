module

public import AcExtensionPrinciple.Minimal.ExpansionParameter
public import AcExtensionPrinciple.Redundancy.IncomingScalarConvention

/-!
# Outgoing λ AC after λ continuity
Paper `e1a0fd5`, `equations.tex` lines 220–275.
All coefficient continuities have already been derived; outgoing λ AC is absent.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- Outgoing λ is AC on every off-axis segment without its own outgoing AC field.
The coefficient is uniformly Lipschitz in v; its incoming integral equals log λ by the initial
gauge. Paper `e1a0fd5`, `eq:lambda-integrating-factor`, lines 87–89, 122–124, 222. -/
theorem MinimalExpansionDraft.ac_lam_out_offAxis {ui u a b : ℝ} {S : SSFields}
    (h : MinimalExpansionDraft ui S) (hu : ui ≤ u) (hua : u < a)
    (hab : a ≤ b) (hb : b ≤ 0) :
    AbsolutelyContinuousOnInterval (S.lam u) a b := by
  have hu0 : u < 0 := hua.trans_le (hab.trans hb)
  obtain ⟨B, hB, hlip⟩ := minimal_blueshift_uniform_outgoing_lipschitz h hab hua hb
  have hs : Icc ui u ×ˢ Icc a b ⊆ cylinderScalarRegion ui := by
    intro p hp
    exact ⟨hp.1.1, hp.1.2.trans_lt (hua.trans_le hp.2.1), hp.2.2.trans hb⟩
  have hA := (minimal_expansion_coefficients_continuous h).2.2.1
  have hi : ∀ v ∈ Icc a b, IntervalIntegrable
      (fun s => S.gamma s v * S.varkappa s v) volume ui u := by
    intro v hv
    apply ContinuousOn.intervalIntegrable_of_Icc hu
    exact hA.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs' => hs ⟨hs', hv⟩)
  let J := fun v => ∫ s in ui..u, S.gamma s v * S.varkappa s v
  have hJ : LipschitzOnWith ⟨B * (u - ui), mul_nonneg hB (sub_nonneg.mpr hu)⟩
      J (Icc a b) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [dist_eq_norm]
    dsimp [J]
    rw [← intervalIntegral.integral_sub (hi x hx) (hi y hy)]
    have hbnd := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := ui) (b := u) (C := B * dist x y)
      (f := fun s => S.gamma s x * S.varkappa s x - S.gamma s y * S.varkappa s y)
      (fun s hs' => by
        rw [uIoc_of_le hu] at hs'
        simpa only [dist_eq_norm] using hlip s ⟨hs'.1.le, hs'.2⟩ x hx y hy)
    change ‖∫ s in ui..u, S.gamma s x * S.varkappa s x -
      S.gamma s y * S.varkappa s y‖ ≤ (B * (u - ui)) * dist x y
    calc
      _ ≤ (B * dist x y) * |u - ui| := hbnd
      _ = _ := by rw [abs_of_nonneg (sub_nonneg.mpr hu)]; ring
  have hJ' : LipschitzOnWith ⟨B * (u - ui), mul_nonneg hB (sub_nonneg.mpr hu)⟩
      J (uIcc a b) := by simpa only [uIcc_of_le hab] using hJ
  have hac := q1_ac_exp hJ'.absolutelyContinuousOnInterval
  apply hac.congr
  intro v hv
  rw [uIcc_of_le hab] at hv
  have hp : (u, v) ∈ pastTriangle ui := ⟨hu, hu0, (hua.trans_le hv.1).le, hv.2.trans hb⟩
  have he := (h.toQ1StandingCore.log_lam_primitive hu le_rfl hu0
    (hua.trans_le hv.1) (hv.2.trans hb)).2
  have hg := (h.initial_gauge v ⟨hu.trans (hua.trans_le hv.1).le, hv.2.trans hb⟩).2
  dsimp only at he
  rw [hg, Real.log_one, sub_zero] at he
  dsimp [J]
  rw [← he, Real.exp_log (h.toQ1StandingCore.lam_pos hp)]


/-- The entire outgoing λ AC field is redundant, including segments starting at the axis.
Off-axis AC comes from the initial gauge and incoming integrating factor; the retained λ
continuity and core BV bound extend it through the single axis endpoint.
Paper `e1a0fd5`, `eq:lambda-integrating-factor`, lines 122–124 and 220–275. -/
theorem MinimalExpansionDraft.ac_lam_out {ui : ℝ} {S : SSFields}
    (h : MinimalExpansionDraft ui S) :
    ∀ u a b, a ≤ b → outSeg u a b ⊆ pastTriangle ui →
      AbsolutelyContinuousOnInterval (S.lam u) a b := by
  intro u a b hab hs
  rcases hab.eq_or_lt with he | he
  · subst b
    exact AbsolutelyContinuousOnInterval.refl _ _
  have haQ : (u, a) ∈ pastTriangle ui := hs ⟨by simp, le_rfl, hab⟩
  have hbQ : (u, b) ∈ pastTriangle ui := hs ⟨by simp, hab, le_rfl⟩
  rcases haQ.2.2.1.eq_or_lt with hea | hla
  · change u = a at hea
    subst a
    apply q1_ac_extend_left he
    · exact h.continuous_lam.comp (f := fun v : ℝ => (u, v))
        (continuous_const.prodMk continuous_id).continuousOn
        (fun v hv => hs ⟨by simp, hv⟩)
    · obtain ⟨C, hC, _⟩ := h.regularCenter.localBV.expansion_variation
        (outSeg u u b) (isCompact_singleton.prod isCompact_Icc) hs
      exact ne_top_of_lt (lt_of_le_of_lt (hC u u b hab Subset.rfl) ENNReal.ofReal_lt_top)
    · intro c hc
      exact MinimalExpansionDraft.ac_lam_out_offAxis h haQ.1 hc.1 hc.2 hbQ.2.2.2
  · exact MinimalExpansionDraft.ac_lam_out_offAxis h haQ.1 hla hab hbQ.2.2.2


end AcExtensionPrinciple

end
