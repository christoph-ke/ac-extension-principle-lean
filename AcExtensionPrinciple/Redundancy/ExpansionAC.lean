module

public import AcExtensionPrinciple.Redundancy.ExpansionParameter

/-!
# Outgoing absolute continuity of λ from the remaining class
Paper commit `e1a0fd5`, `equations.tex` lines 66–92 and 220–275,
`eq:radius`, `eq:mass`, `eq:logarithmic-expansions`.
The initial λ gauge and incoming integrating factor give outgoing AC off-axis.
Continuity and BV exclude a singular contribution supported at the axis endpoint.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- Exponentiation preserves AC on a compact interval. Compact extrema of the AC primitive
discharge the local Lipschitz composition premises. Paper `e1a0fd5`, lines 87–89, 222. -/
theorem q1_ac_exp {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun x => Real.exp (f x)) a b := by
  obtain ⟨x, hx, hmin⟩ := isCompact_uIcc.exists_isMinOn nonempty_uIcc hf.continuousOn
  obtain ⟨y, hy, hmax⟩ := isCompact_uIcc.exists_isMaxOn nonempty_uIcc hf.continuousOn
  have hF : ContDiffOn ℝ 1 Real.exp (Icc (f x) (f y)) := Real.contDiff_exp.contDiffOn
  obtain ⟨K, hK⟩ := hF.exists_lipschitzOnWith
    (by decide) (convex_Icc _ _) isCompact_Icc
  exact hK.comp_absolutelyContinuousOnInterval (fun z hz => ⟨hmin hz, hmax hz⟩) hf

/-- Outgoing λ is AC on every off-axis segment without its own outgoing AC field.
The coefficient is uniformly Lipschitz in v; its incoming integral equals log λ by the initial
gauge. Paper `e1a0fd5`, `eq:lambda-integrating-factor`, lines 87–89, 122–124, 222. -/
theorem ac_lam_out_offAxis_of_rest {ui u a b : ℝ} {S : SSFields}
    (h : StandingWithout_ac_lam_out ui S) (hu : ui ≤ u) (hua : u < a)
    (hab : a ≤ b) (hb : b ≤ 0) :
    AbsolutelyContinuousOnInterval (S.lam u) a b := by
  have hu0 : u < 0 := hua.trans_le (hab.trans hb)
  obtain ⟨B, hB, hlip⟩ := q1_blueshift_uniform_outgoing_lipschitz h hab hua hb
  have hs : Icc ui u ×ˢ Icc a b ⊆ cylinderScalarRegion ui := by
    intro p hp
    exact ⟨hp.1.1, hp.1.2.trans_lt (hua.trans_le hp.2.1), hp.2.2.trans hb⟩
  have hA := (q1_expansion_coefficients_continuous h).2.2.1
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

/-- A continuous BV function AC away from its left endpoint is AC through that endpoint.
For λ the retained continuity and core expansion variation discharge these premises.
Paper `e1a0fd5`, line 222, Luk–Oh Definition 2.1(2). -/
theorem q1_ac_extend_left {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hc : ContinuousOn f (Icc a b)) (hbv : BoundedVariationOn f (Icc a b))
    (hloc : ∀ c ∈ Ioc a b, AbsolutelyContinuousOnInterval f c b) :
    AbsolutelyContinuousOnInterval f a b := by
  have hi : IntervalIntegrable (deriv f) volume a b := by
    have hv : BoundedVariationOn f (uIcc a b) := by
      simpa only [uIcc_of_le hab.le] using hbv
    exact hv.intervalIntegrable_deriv
  let G := fun x => ∫ t in a..x, deriv f t
  have hG : AbsolutelyContinuousOnInterval G a b :=
    hi.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hfa : Tendsto f (𝓝[>] a) (𝓝 (f a)) := by
    have ht := hc a ⟨le_rfl, hab.le⟩
    rw [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsGE hab] at ht
    exact ht.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
  have hGa : Tendsto G (𝓝[>] a) (𝓝 (G a)) := by
    have ht := hG.continuousOn a (by simp [hab.le])
    rw [uIcc_of_le hab.le, ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsGE hab] at ht
    exact ht.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
  have he : ∀ x ∈ Icc a b, f x = G x + f a := by
    intro x hx
    rcases hx.1.eq_or_lt with he | he
    · subst x
      simp [G]
    have ht := (hfa.add_const (G x)).sub hGa
    have heq : (fun c => f c + G x - G c) =ᶠ[𝓝[>] a] fun _ => f x := by
      filter_upwards [self_mem_nhdsWithin,
        ((continuous_id.tendsto a).mono_left nhdsWithin_le_nhds).eventually
          (Iio_mem_nhds he)] with c hc hcx
      change a < c at hc
      change c < x at hcx
      have hac : AbsolutelyContinuousOnInterval f c x :=
        (hloc c ⟨hc, hcx.le.trans hx.2⟩).mono (by
          rw [uIcc_of_le (hcx.le.trans hx.2), uIcc_of_le hcx.le]
          exact Icc_subset_Icc le_rfl hx.2)
      have hAc := hac.integral_deriv_eq_sub
      have hic : IntervalIntegrable (deriv f) volume a c := hi.mono_set (by
        rw [uIcc_of_le hab.le, uIcc_of_le hc.le]
        exact Icc_subset_Icc le_rfl (hcx.le.trans hx.2))
      have hicx : IntervalIntegrable (deriv f) volume c x := hi.mono_set (by
        rw [uIcc_of_le hab.le, uIcc_of_le hcx.le]
        exact Icc_subset_Icc hc.le hx.2)
      have hisub := intervalIntegral.integral_add_adjacent_intervals hic hicx
      dsimp [G]
      linarith
    have ht' := ht.congr' heq
    have hu := tendsto_nhds_unique ht' tendsto_const_nhds
    simpa only [G, intervalIntegral.integral_same, sub_zero, add_comm] using hu.symm
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => f a) a b :=
    (LipschitzWith.const (f a)).lipschitzOnWith.absolutelyContinuousOnInterval
  apply (hG.fun_add hconst).congr
  intro x hx
  exact (he x (by simpa only [uIcc_of_le hab.le] using hx)).symm

/-- The entire outgoing λ AC field is redundant, including segments starting at the axis.
Off-axis AC comes from the initial gauge and incoming integrating factor; the retained λ
continuity and core BV bound extend it through the single axis endpoint.
Paper `e1a0fd5`, `eq:lambda-integrating-factor`, lines 122–124 and 220–275. -/
theorem ac_lam_out_of_rest {ui : ℝ} {S : SSFields}
    (h : StandingWithout_ac_lam_out ui S) :
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
      exact ac_lam_out_offAxis_of_rest h haQ.1 hc.1 hc.2 hbQ.2.2.2
  · exact ac_lam_out_offAxis_of_rest h haQ.1 hla hab hbQ.2.2.2

end AcExtensionPrinciple

end
