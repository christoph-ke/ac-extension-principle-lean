module

public import AcExtensionPrinciple.Decay.Prop27Assembly
public import AcExtensionPrinciple.Decay.Prop28Comparison
public import AcExtensionPrinciple.ACDatum.RectangleFields

/-!
# Common scalar limit from interpolation and uniform mass decay

Paper `e1a0fd5`, `prop:common-scalar-limit`, lines 931–989. Compact
incoming transport bounds make the terminal datum Cauchy. Continuity on a
fixed proper cone then gives the uniform outgoing limit, and the incoming
damping comparison gives the third limit, including the actual axis values.
-/

public section

namespace AcExtensionPrinciple.StandingFull

open Set Filter MeasureTheory
open scoped Topology

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- A finite terminal scalar limit follows from vanishing amplitude and G5.
Paper `e1a0fd5`, `eq:terminal-scalar-variation`, lines 952–962. -/
theorem decay_terminal_scalar_limit (h23 : Lemma23Statement ui S)
    (hmass : UniformMassDecayStatement ui S) :
    ∃ L : ℝ, Tendsto (fun u => S.dvpsi u 0 / S.lam u 0) (𝓝[<] 0) (𝓝 L) := by
  apply cauchy_map_iff_exists_tendsto.mp
  apply Metric.cauchy_iff.mpr
  refine ⟨inferInstance, ?_⟩
  intro eps heps
  let delta := eps / (2 * (Bstar ui S + 1))
  have hB : 0 ≤ Bstar ui S := ENNReal.toReal_nonneg
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hsmall : Bstar ui S * delta < eps := by
    have he : delta * (2 * (Bstar ui S + 1)) = eps := by
      dsimp [delta]
      field_simp
    nlinarith
  obtain ⟨a, hai, ha0, hA⟩ := h.decay_outgoing_amplitude_small h23 hmass delta hdelta
  refine ⟨(fun u => S.dvpsi u 0 / S.lam u 0) '' Ioo a 0, ?_, ?_⟩
  · change (fun u => S.dvpsi u 0 / S.lam u 0) ⁻¹'
      ((fun u => S.dvpsi u 0 / S.lam u 0) '' Ioo a 0) ∈ 𝓝[<] 0
    exact mem_of_superset (Ioo_mem_nhdsLT ha0) (fun u hu => ⟨u, hu, rfl⟩)
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    rw [Real.dist_eq]
    rcases le_total u v with huv | hvu
    · rw [abs_sub_comm]
      exact (h.decay_datum_comparison huv (hai.trans hu.1.le) hv.2 hv.2 le_rfl
        (fun x hx => (hA x 0 (hu.1.le.trans hx.1)
          (hx.2.trans_lt hv.2) (hx.2.trans hv.2.le) le_rfl).le)).trans_lt hsmall
    · exact (h.decay_datum_comparison hvu (hai.trans hv.1.le) hu.2 hu.2 le_rfl
        (fun x hx => (hA x 0 (hv.1.le.trans hx.1)
          (hx.2.trans_lt hu.2) (hx.2.trans hu.2.le) le_rfl).le)).trans_lt hsmall

/-- Fixed-cone continuity and incoming comparison upgrade the terminal limit
to uniform convergence of the outgoing normalized datum.
Paper `e1a0fd5`, `eq:scalar-nearby-cone-comparison`, lines 964–971. -/
theorem decay_uniform_outgoing_scalar {L : ℝ} (h23 : Lemma23Statement ui S)
    (hmass : UniformMassDecayStatement ui S)
    (hL : Tendsto (fun u => S.dvpsi u 0 / S.lam u 0) (𝓝[<] 0) (𝓝 L)) :
    ∀ eps : ℝ, 0 < eps → ∃ a : ℝ, ui ≤ a ∧ a < 0 ∧
      ∀ u v, a ≤ u → u < 0 → u ≤ v → v ≤ 0 →
        |S.dvpsi u v / S.lam u v - L| < eps := by
  intro eps heps
  let delta := eps / (4 * (Bstar ui S + 1))
  have hB : 0 ≤ Bstar ui S := ENNReal.toReal_nonneg
  have hd : 0 < delta := by dsimp [delta]; positivity
  have hBd : Bstar ui S * delta < eps / 4 := by
    have he : delta * (4 * (Bstar ui S + 1)) = eps := by
      dsimp [delta]
      field_simp
    nlinarith
  obtain ⟨aA, haAi, haA0, hA⟩ := h.decay_outgoing_amplitude_small h23 hmass delta hd
  obtain ⟨aL, haLi, haL0, hLt⟩ := decay_exists_threshold h.initial_negative
    ((Metric.tendsto_nhds.mp hL) (eps / 4) (by positivity))
  let u₀ := max aA aL
  have hu₀i : ui ≤ u₀ := haAi.trans (le_max_left _ _)
  have hu₀0 : u₀ < 0 := max_lt haA0 haL0
  have hhalf : u₀ < u₀ / 2 := by linarith
  have hhalf0 : u₀ / 2 < 0 := by linarith
  have hdv : ContinuousOn (S.dvpsi u₀) (Icc (u₀ / 2) 0) :=
    (h.dvpsi_continuous_rectangle hu₀i hhalf0.le hu₀0 hhalf le_rfl).comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun _v hv => ⟨⟨hu₀i, le_rfl⟩, hv⟩)
  have hlam := continuous_out h.regularCenter.continuous_lam
    (outSeg_subset_triangle hu₀i hu₀0 hhalf.le le_rfl)
  have hc := (hdv.div hlam (fun v hv => (h.lam_pos (p := (u₀, v))
    ⟨hu₀i, hu₀0, hhalf.le.trans hv.1, hv.2⟩).ne')) 0 ⟨hhalf0.le, le_rfl⟩
  have hmap : Tendsto (fun v : ℝ => v) (𝓝[<] 0) (𝓝[Icc (u₀ / 2) 0] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨nhdsWithin_le_nhds, ?_⟩
    filter_upwards [Ioo_mem_nhdsLT hhalf0] with v hv
    exact ⟨hv.1.le, hv.2.le⟩
  have htc : Tendsto (fun v => S.dvpsi u₀ v / S.lam u₀ v) (𝓝[Icc (u₀ / 2) 0] 0)
      (𝓝 (S.dvpsi u₀ 0 / S.lam u₀ 0)) := hc
  obtain ⟨av, havi, hav0, hv⟩ := decay_exists_threshold h.initial_negative
    ((Metric.tendsto_nhds.mp (htc.comp hmap)) (eps / 4) (by positivity))
  refine ⟨max u₀ av, hu₀i.trans (le_max_left _ _), max_lt hu₀0 hav0, ?_⟩
  intro u v hau hu0 huv hv0
  have hu₀u : u₀ ≤ u := (le_max_left _ _).trans hau
  have hcomp := h.decay_datum_comparison_closed hu₀u hu₀i hu0 huv hv0
    (fun x hx => (hA x v ((le_max_left _ _).trans hx.1)
      (hx.2.trans_lt hu0) (hx.2.trans huv) hv0).le)
  have hfixed : |S.dvpsi u₀ v / S.lam u₀ v - S.dvpsi u₀ 0 / S.lam u₀ 0| < eps / 4 := by
    rcases hv0.eq_or_lt with he | he
    · subst v
      simpa using (show 0 < eps / 4 by positivity)
    · simpa only [Real.dist_eq, Function.comp_def] using
        hv v ((le_max_right _ _).trans (hau.trans huv)) he
  have hterminal : |S.dvpsi u₀ 0 / S.lam u₀ 0 - L| < eps / 4 := by
    simpa only [Real.dist_eq] using hLt u₀ (le_max_right _ _) hu₀0
  have ht := abs_sub_le (S.dvpsi u v / S.lam u v) (S.dvpsi u₀ v / S.lam u₀ v) L
  have ht₀ := abs_sub_le (S.dvpsi u₀ v / S.lam u₀ v) (S.dvpsi u₀ 0 / S.lam u₀ 0) L
  linarith

/-- Proposition 2.8: a common finite uniform scalar limit under precisely
Lemma 2.3 and Proposition 2.7. Paper `e1a0fd5`,
`eq:common-scalar-limit`, lines 931–987. -/
theorem common_scalar_limit_of_interpolation_mass_decay (h23 : Lemma23Statement ui S)
    (hmass : UniformMassDecayStatement ui S) : CommonScalarLimitStatement ui S := by
  obtain ⟨L, hL⟩ := h.decay_terminal_scalar_limit h23 hmass
  refine ⟨L, ?_⟩
  intro eps heps
  obtain ⟨aP, haPi, haP0, hP⟩ := h.decay_uniform_outgoing_scalar h23 hmass hL
    (eps / 8) (by positivity)
  obtain ⟨aA, haAi, haA0, hA⟩ := h.decay_outgoing_amplitude_small h23 hmass
    (eps / 8) (by positivity)
  refine ⟨max aP aA, haPi.trans (le_max_left _ _), max_lt haP0 haA0, ?_⟩
  intro u v hau hu0 huv hv0
  have hui : ui ≤ u := haPi.trans ((le_max_left _ _).trans hau)
  have hphi (w : ℝ) (hw : w ∈ Icc u v) : |S.phi u w - L| ≤ eps / 4 := by
    have hp := hP u w ((le_max_left _ _).trans hau) hu0 hw.1 (hw.2.trans hv0)
    have ha := hA u w ((le_max_right _ _).trans hau) hu0 hw.1 (hw.2.trans hv0)
    have ht := abs_sub_le (S.phi u w) (S.dvpsi u w / S.lam u w) L
    rw [abs_sub_comm (S.phi u w) (S.dvpsi u w / S.lam u w)] at ht
    linarith
  have hi := h.decay_incoming_scalar_bound ⟨hui, hu0, huv, hv0⟩ hphi
  have hp := hP u v ((le_max_left _ _).trans hau) hu0 huv hv0
  have hv := hphi v ⟨huv, le_rfl⟩
  linarith

/-- The normalized outgoing and incoming amplitudes vanish uniformly by
their algebraic identities, including on the regular axis.
Paper `e1a0fd5`, `eq:normalized-scalar-amplitudes-vanish`, lines 987–989. -/
theorem normalized_scalar_amplitudes_vanish_of_common_limit
    (hlimit : CommonScalarLimitStatement ui S) :
    NormalizedScalarAmplitudesVanishStatement ui S := by
  obtain ⟨L, hL⟩ := hlimit
  intro eps heps
  obtain ⟨a, hai, ha0, ha⟩ := hL (eps / 2) (by positivity)
  refine ⟨a, hai, ha0, ?_⟩
  intro u v hau hu0 huv hv0
  have hp : (u, v) ∈ pastTriangle ui := ⟨hai.trans hau, hu0, huv, hv0⟩
  rw [h.decay_outgoing_amplitude hp, h.decay_incoming_amplitude hp]
  have ht := abs_sub_le (S.dvpsi u v / S.lam u v) L (S.phi u v)
  have hi := abs_sub_le (S.dupsi u v / S.nu u v) L (S.phi u v)
  rw [abs_sub_comm L] at ht hi
  have hh := ha u v hau hu0 huv hv0
  linarith [abs_nonneg (S.dvpsi u v / S.lam u v - L),
    abs_nonneg (S.dupsi u v / S.nu u v - L)]

/-- Both conclusions of Proposition 2.8 using the proved Proposition 2.7 assembly. Paper `e1a0fd5`,
`prop:common-scalar-limit`, lines 931–989. -/
theorem common_scalar_limit_of_decay_lemmas {K H C rho : ℝ}
    (h23 : Lemma23Statement ui S) (hg : CylinderKBounds ui S K)
    (h24 : Lemma24Statement ui S) (h25 : Lemma25Statement ui S H C rho)
    (h26 : Lemma26Statement ui S K H) :
    CommonScalarLimitStatement ui S ∧ NormalizedScalarAmplitudesVanishStatement ui S := by
  have hlimit := h.common_scalar_limit_of_interpolation_mass_decay h23
    (h.uniform_mass_decay_of_cylinder_lemmas hg h24 h25 h26)
  exact ⟨hlimit, h.normalized_scalar_amplitudes_vanish_of_common_limit hlimit⟩

/-- The decay chain for Propositions 2.7 and 2.8 also accepts the stronger regular cylinder geometry
interface. The main proof uses `CylinderKBounds` and the strict terminal-radius construction
in `ClassCylinderGeometry.lean`. Paper `e1a0fd5`, `prop:common-scalar-limit`, lines 931–989. -/
theorem common_scalar_limit_of_cylinder_geometry {K H C rho : ℝ}
    (h23 : Lemma23Statement ui S) (hg : CylinderGeometryStatement ui S K)
    (h24 : Lemma24Statement ui S) (h25 : Lemma25Statement ui S H C rho)
    (h26 : Lemma26Statement ui S K H) :
    CommonScalarLimitStatement ui S ∧ NormalizedScalarAmplitudesVanishStatement ui S := by
  have hlimit := h.common_scalar_limit_of_interpolation_mass_decay h23
    (h.uniform_mass_decay_of_cylinder_geometry hg h24 h25 h26)
  exact ⟨hlimit, h.normalized_scalar_amplitudes_vanish_of_common_limit hlimit⟩

end AcExtensionPrinciple.StandingFull

end
