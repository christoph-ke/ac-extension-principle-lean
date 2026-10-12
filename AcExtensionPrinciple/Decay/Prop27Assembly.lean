module

public import AcExtensionPrinciple.Decay.Prop27Terminal
public import AcExtensionPrinciple.Decay.Prop27Envelope
public import AcExtensionPrinciple.Decay.Prop27CylinderDecay
public import AcExtensionPrinciple.Decay.ClassCylinderGeometry
public import AcExtensionPrinciple.Decay.Prop28Amplitude
public import AcExtensionPrinciple.Decay.DyadicSelection
public import AcExtensionPrinciple.Decay.CylinderNumbers
public import AcExtensionPrinciple.Analysis.LongCylinderTimes

/-!
# Uniform mass-ratio decay from the paper's cylinder lemmas

Paper `e1a0fd5`, `prop:uniform-mass-decay`, lines 835–925.
The cylinder lemmas enter only through their explicit source
statements. Terminal, envelope, selection, mass comparison and the required
cylinder geometry are proved from the standing solution class.
-/

public section

namespace AcExtensionPrinciple.StandingFull

open Set Filter MeasureTheory
open scoped Topology

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Proposition 2.7, in epsilon–delta form. Lemma 2.3 is used inside the
Lemma 2.6; the assembly itself needs only Lemmas 2.4–2.6 and a
geometric constant supplied by `exists_decay_cylinder_K`.
Paper `e1a0fd5`, `eq:uniform-mass-decay`, lines 835–925. -/
theorem uniform_mass_decay_of_cylinder_lemmas {K H C₁ rho : ℝ}
    (hg : CylinderKBounds ui S K) (h24 : Lemma24Statement ui S)
    (h25 : Lemma25Statement ui S H C₁ rho) (h26 : Lemma26Statement ui S K H) :
    UniformMassDecayStatement ui S := by
  by_contra hfail
  unfold UniformMassDecayStatement at hfail
  push Not at hfail
  obtain ⟨eta, heta, hbad⟩ := hfail
  obtain ⟨C₀, hC₀, h24⟩ := h24
  obtain ⟨D, hD, h26⟩ := h26
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one hg.1
  have hH := h25.1
  have hC₁ := h25.2.1
  have hrho := h25.2.2.1
  have hrho1 := h25.2.2.2.1
  let Q := C₁ * D ^ 2 / (1 - rho)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  obtain ⟨eps, heps, heps1, hepseta, hsmall, N, htransient⟩ :=
    decay_choose_parameters hC₀.le hQ hrho.le hrho1 heta
  have hepslt : eps < eta := by linarith
  obtain ⟨u₀, hui, hu0, hterminal⟩ := decay_exists_threshold h.initial_negative
    (h.decay_terminal_mu.eventually (gt_mem_nhds (show 0 < eps / 4 by positivity)))
  have hfuture : ∀ u ∈ Ico u₀ 0,
      (futureRadii (decayBadPoints ui S eps) (fun p => S.r p.1 p.2) u).Nonempty := by
    intro u hu
    obtain ⟨t, v, hut, ht0, htv, hv0, hmu⟩ := hbad u (hui.trans hu.1) hu.2
    have hp : (t, v) ∈ pastTriangle ui := ⟨hui.trans (hu.1.trans hut), ht0, htv, hv0⟩
    rw [abs_of_nonneg (h.mu_bounds hp).1] at hmu
    exact ⟨S.r t v, ⟨(t, v), ⟨⟨hp, hepslt.trans_le hmu⟩, hut⟩, rfl⟩⟩
  obtain ⟨hmono, hright, hlim, hpos, hmajor⟩ := h.decay_envelope_properties heps hui hu0 hfuture
  let b₀ := decayEnvelope ui S eps u₀ / 2
  have hb₀ : 0 < b₀ := by dsimp [b₀]; exact div_pos (hpos u₀ ⟨le_rfl, hu0⟩) (by norm_num)
  have hinit : b₀ < decayEnvelope ui S eps u₀ := by
    dsimp [b₀]
    linarith [hpos u₀ ⟨le_rfl, hu0⟩]
  let t := envelopeDyadicTime (decayEnvelope ui S eps) u₀ b₀
  let b := envelopeDyadicLevel b₀
  have hsel := fun n => envelope_dyadic_selection hu0 hb₀ hinit hlim hright hmono n
  have htmono : Monotone t := envelopeDyadicTime_monotone hu0 hb₀ hlim
  have htneg : ∀ n, t n < 0 := fun n => (hsel n).2.1
  have htlim : Tendsto t atTop (𝓝 0) :=
    envelopeDyadicTime_tendsto_zero hu0 hb₀ hlim hright hmono hpos
  have htw : Tendsto t atTop (𝓝[<] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨htlim, Eventually.of_forall htneg⟩
  have hmcont : ContinuousOn (fun u => 2 * S.m u 0 / eps) (Ico u₀ 0) := by
    have hc := h.regularCenter.continuous_m.comp
      (continuous_id.prodMk continuous_const).continuousOn
      (fun u (hu : u ∈ Ico u₀ 0) => ⟨hui.trans hu.1, hu.2, hu.2.le, le_rfl⟩)
    exact (continuousOn_const.mul hc).div_const eps
  have hlevel : ∀ n, b n ≤ 2 * S.m (t n) 0 / eps := fun n =>
    envelope_dyadic_level_le_majorant hu0 hb₀ hinit hlim hright hmono hmajor hmcont n
  have hscale : Tendsto (fun n => b n / (-t n)) atTop (𝓝 0) := by
    have hs := (h.decay_terminal_mass_scale.comp htw).const_mul (2 / eps)
    simp only [mul_zero, Function.comp_def] at hs
    apply squeeze_zero' _ _ hs
    · exact Eventually.of_forall (fun n => div_nonneg
        (envelopeDyadicLevel_properties hb₀ n).1.le (neg_pos.mpr (htneg n)).le)
    · apply Eventually.of_forall
      intro n
      have hh := div_le_div_of_nonneg_right (hlevel n) (neg_pos.mpr (htneg n)).le
      convert hh using 1; ring
  let T := K * (eps⁻¹ + (N : ℝ) * H)
  have hT0 : 0 ≤ T := by dsimp [T]; positivity
  have hlong := frequently_dyadic_increment_gt hb₀ (fun n => rfl) htmono htneg htlim hscale (T + 1)
  have htail : ∀ᶠ n in atTop, initialACTail ui S (t n) ≤ eps :=
    ((h.decay_tail_tendsto.comp htw).eventually (gt_mem_nhds heps)).mono (fun _ hn => hn.le)
  obtain ⟨n, hlong, htail⟩ := (hlong.and_eventually htail).exists
  change (T + 1) * b n < t (n + 1) - t n at hlong
  let a₀ := t n
  let a₁ := t (n + 1)
  let bn := b n
  have hbn : 0 < bn := (envelopeDyadicLevel_properties hb₀ n).1
  have ha₀i : ui ≤ a₀ := hui.trans (hsel n).1.le
  have ha₁0 : a₁ < 0 := htneg (n + 1)
  have haa : a₀ < a₁ := by
    have hh : 0 < (T + 1) * bn := mul_pos (by linarith) hbn
    linarith
  have hR : ∀ u ∈ Icc a₀ a₁, 2 * bn ≤ S.r u 0 := by
    have hc := continuous_in h.regularCenter.continuous_r
      (inSeg_subset_triangle ha₀i ha₁0 (le_of_lt ha₁0) le_rfl)
    intro u hu
    apply (interval_bounds_of_open haa hc (L := 2 * bn) (U := -a₀) ?_ u hu).1
    intro s hs
    have hdom : s ∈ Ico u₀ 0 := ⟨(hsel n).1.le.trans hs.1.le, hs.2.trans ha₁0⟩
    have hp : (s, 0) ∈ pastTriangle ui := ⟨hui.trans hdom.1, hdom.2, hdom.2.le, le_rfl⟩
    have hlo := (hsel n).2.2.2.2 s hs.1.le hs.2
    have hmaj := hmajor s hdom
    have hmu := (hterminal s hdom.1 hdom.2).le
    have hr := h.r_pos hp hdom.2
    have heq : 2 * S.m s 0 = S.mu s 0 * S.r s 0 := by
      simp [SSFields.mu, massRatio, ne_of_gt hr]
    have hquot : 2 * S.m s 0 / eps ≤ S.r s 0 / 4 := by
      apply (div_le_iff₀ heps).mpr
      rw [heq]
      nlinarith [mul_le_mul_of_nonneg_right hmu hr.le]
    refine ⟨by linarith, ?_⟩
    have hh := (h.radius_bounds hp).2
    change S.r s 0 ≤ 0 - s at hh
    linarith [hs.1]
  obtain ⟨c⟩ := h.decay_cylinder_of_strict_terminal_radius hbn ha₀i haa.le ha₁0
    (fun u hu => (by linarith : bn < 2 * bn).trans_le (hR u hu))
  have hext : ∀ u v, (u, v) ∈ pastTriangle ui → a₀ ≤ u → u ≤ a₁ → bn ≤ S.r u v →
      S.mu u v ≤ eps := by
    intro u v hp hau hu₁ hr
    exact h.decay_exterior_bound heps hbn hp hau (hR u ⟨hau, hu₁⟩) hr (hsel n).2.2.1
  let a := a₀ + T * bn
  have haa₀ : a₀ ≤ a := by dsimp [a]; nlinarith [mul_nonneg hT0 hbn.le]
  have haa₁ : a < a₁ := by dsimp [a]; nlinarith
  have hadom : a ∈ Ico u₀ 0 := ⟨(hsel n).1.le.trans haa₀, haa₁.trans ha₁0⟩
  have hbadRadius := (hsel n).2.2.2.2 a haa₀ haa₁
  obtain ⟨_, ⟨p, ⟨hp, hap⟩, rfl⟩, hrbad⟩ := exists_lt_of_lt_csSup (hfuture a hadom) hbadRadius
  have hpr : S.r p.1 p.2 ≤ bn := (le_csSup (h.decay_future_bdd eps a₀)
    ⟨p, ⟨hp, haa₀.trans hap⟩, rfl⟩).trans (hsel n).2.2.1
  have hpt : p.1 < a₁ := by
    by_contra hnot
    have hh := (le_csSup (h.decay_future_bdd eps a₁)
      ⟨p, ⟨hp, le_of_not_gt hnot⟩, rfl⟩).trans (hsel (n + 1)).2.2.1
    rw [(envelopeDyadicLevel_properties hb₀ n).2.2] at hh
    exact (not_le_of_gt hrbad) hh
  have hpi : p.1 ∈ Icc a₀ a₁ := ⟨haa₀.trans hap, hpt.le⟩
  have hE := decay_cylinder_energy hg h25 h26 hD.le heps heps1 c
    (fun u hu => (h24 bn a₀ a₁ c).1 u hu |>.2.2) hext htail hpi
    (by
      have heq : a₀ + K * bn / eps + K * ((N : ℝ) * H * bn) = a := by
        dsimp [a, T]
        simp only [div_eq_mul_inv]
        ring
      rw [heq]
      exact hap) hsmall htransient
  have hcp := c.points p.1 hpi
  have hvc : p.2 ≤ c.v p.1 := by
    by_contra hnot
    have hh := h.decay_radius_out_strict (lt_of_not_ge hnot)
      (c.point_mem hpi).1 (c.point_mem hpi).2.1 hcp.1.le hp.1.2.2.2
    rw [hcp.2.2] at hh
    linarith
  have hmass := h.decay_mass_out_le hvc hp.1.1 hp.1.2.1 hp.1.2.2.1 hcp.2.1
  have hmE := (h24 bn a₀ a₁ c).1 p.1 hpi |>.1
  have hmassbad : eps * bn / 4 < S.m p.1 p.2 := by
    have hrpos := h.r_pos hp.1 (h.decay_bad_off_axis heps hp)
    have hh : eps * S.r p.1 p.2 < 2 * S.m p.1 p.2 := (lt_div_iff₀ hrpos).mp hp.2
    nlinarith [mul_lt_mul_of_pos_left hrbad heps]
  exact bad_point_energy_contradiction heps hbn hmassbad (hmass.trans hmE) hE

/-- The exact regular cylinder geometry premise also plugs into Proposition 2.7; its additional
conclusions are already proved for the cylinders used above. Paper `e1a0fd5`,
`prop:uniform-mass-decay`, lines 835–925. -/
theorem uniform_mass_decay_of_cylinder_geometry {K H C rho : ℝ}
    (hg : CylinderGeometryStatement ui S K) (h24 : Lemma24Statement ui S)
    (h25 : Lemma25Statement ui S H C rho) (h26 : Lemma26Statement ui S K H) :
    UniformMassDecayStatement ui S := by
  have hK : CylinderKBounds ui S K := ⟨hg.1, fun p hp => hg.2.1 p.1 p.2 hp⟩
  exact h.uniform_mass_decay_of_cylinder_lemmas hK h24 h25 h26

end AcExtensionPrinciple.StandingFull

end
