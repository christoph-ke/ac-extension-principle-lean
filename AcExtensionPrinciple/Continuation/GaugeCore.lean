module

public import AcExtensionPrinciple.Continuation.GaugeAxis
public import AcExtensionPrinciple.Gauge.AbsoluteContinuity

/-!
# Core equations under a regular inverse chart

Paper `e1a0fd5`, `equations.tex` lines 1390–1411, original class membership in the continuation
chart. The coordinate and local boundedness premises below are component premises: they do not alter
the source standing assumptions.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- A common increasing continuous chart maps closed outgoing segments to
closed outgoing segments. Paper `e1a0fd5`, line 1411, Q8. -/
theorem mapped_outSeg_subset {U : ℝ → ℝ} {D E : Set (ℝ × ℝ)} {u a b : ℝ}
    (hU : StrictMono U) (hc : Continuous U) (hab : a ≤ b)
    (hmap : ∀ p ∈ E, (U p.1, U p.2) ∈ D) (hs : outSeg u a b ⊆ E) :
    outSeg (U u) (U a) (U b) ⊆ D := by
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  simp only [mem_singleton_iff] at hx
  subst x
  have himage := hc.continuousOn.image_Icc_of_monotoneOn hab (hU.monotone.monotoneOn _)
  rw [← himage] at hy
  obtain ⟨v, hv, rfl⟩ := hy
  exact hmap (u, v) (hs ⟨by simp, hv⟩)

/-- Incoming counterpart of segment transport. Paper `e1a0fd5`, line 1411, Q8. -/
theorem mapped_inSeg_subset {U : ℝ → ℝ} {D E : Set (ℝ × ℝ)} {v a b : ℝ}
    (hU : StrictMono U) (hc : Continuous U) (hab : a ≤ b)
    (hmap : ∀ p ∈ E, (U p.1, U p.2) ∈ D) (hs : inSeg v a b ⊆ E) :
    inSeg (U v) (U a) (U b) ⊆ D := by
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  simp only [mem_singleton_iff] at hy
  subst y
  have himage := hc.continuousOn.image_Icc_of_monotoneOn hab (hU.monotone.monotoneOn _)
  rw [← himage] at hx
  obtain ⟨u, hu, rfl⟩ := hx
  exact hmap (u, v) (hs ⟨hu, by simp⟩)

/-- The outgoing domain-relative axis filter maps into the original one.
Paper `e1a0fd5`, `eq:continuation-null-gauge`, lines 1390–1411. -/
theorem tendsto_mapped_axis_filter {U : ℝ → ℝ} {D E : Set (ℝ × ℝ)} {a : ℝ}
    (hU : StrictMono U) (hc : Continuous U)
    (hmap : ∀ p ∈ E, (U p.1, U p.2) ∈ D) :
    Tendsto U (𝓝[>] a ⊓ 𝓟 {v | (a, v) ∈ E})
      (𝓝[>] U a ⊓ 𝓟 {v | (U a, v) ∈ D}) := by
  apply tendsto_inf.mpr
  constructor
  · apply (tendsto_nhdsWithin_iff.mpr ?_).mono_left inf_le_left
    refine ⟨(hc.tendsto a).mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with v hv
    exact hU hv
  · apply tendsto_principal.mpr
    have hm : ∀ᶠ v in 𝓝[>] a ⊓ 𝓟 {v | (a, v) ∈ E}, (a, v) ∈ E :=
      Filter.Eventually.filter_mono inf_le_right (by simp)
    exact hm.mono (fun v hv => hmap (a, v) hv)

/-- All ten integral equations, scalar AC, and five axis conditions transport through the inverse
chart. Paper `e1a0fd5`, lines 1390–1411. Coordinate derivatives are supplied on I. The axis
boundedness premise is discharged by the original class's λ/dvψ variation on each proper cone; it is
needed for cancellation of the derivative mismatch at Γ. -/
theorem ChrBVCore.pullback {D E : Set (ℝ × ℝ)} {A B I : Set ℝ} {S : SSFields}
    {U dU : ℝ → ℝ} (h : ChrBVCore D A S) (hU : StrictMono U) (hc : Continuous U)
    (hmap : ∀ p ∈ E, (U p.1, U p.2) ∈ D)
    (hA : ∀ a ∈ B, U a ∈ A) (hB : B ⊆ I)
    (hI : ∀ p ∈ E, p.1 ∈ I ∧ p.2 ∈ I)
    (hderiv : ∀ a b, a ≤ b → Icc a b ⊆ I →
      ∀ x ∈ Icc a b, HasDerivWithinAt U (dU x) (Icc a b) x)
    (hpos : ∀ x ∈ I, 0 < dU x) (hdc : ContinuousOn dU I)
    (hbound : ∀ a ∈ B, ∃ C : ℝ,
      ∀ᶠ v in 𝓝[>] a ⊓ 𝓟 {v | (a, v) ∈ E},
        |S.lam (U a) (U v)| ≤ C ∧ |S.dvpsi (U a) (U v)| ≤ C) :
    ChrBVCore E B (S.pullback U dU) := by
  have houtI (u a b : ℝ) (hs : outSeg u a b ⊆ E) : Icc a b ⊆ I :=
    fun v hv => (hI (u, v) (hs ⟨by simp, hv⟩)).2
  have hinI (v a b : ℝ) (hs : inSeg v a b ⊆ E) : Icc a b ⊆ I :=
    fun u hu => (hI (u, v) (hs ⟨hu, by simp⟩)).1
  have hG (a b : ℝ) (hab : a ≤ b) (hs : Icc a b ⊆ I) : GaugeSegment U dU a b :=
    GaugeSegment.of_hasDerivWithinAt (by simpa only [uIcc_of_le hab] using hderiv a b hab hs)
      (by simpa only [uIcc_of_le hab] using fun x hx => (hpos x (hs hx)).le)
  have hout (u a b : ℝ) (hab : a ≤ b) (hs : outSeg u a b ⊆ E) :=
    mapped_outSeg_subset hU hc hab hmap hs
  have hin (v a b : ℝ) (hab : a ≤ b) (hs : inSeg v a b ⊆ E) :=
    mapped_inSeg_subset hU hc hab hmap hs
  have hmon := hU.monotone
  have houtmap (p : ℝ × ℝ) :
      MapsTo U {w | p.2 ≤ w ∧ (p.1, w) ∈ E}
        {w | U p.2 ≤ w ∧ (U p.1, w) ∈ D} :=
    fun _ hw => ⟨hmon hw.1, hmap _ hw.2⟩
  have hinmap (p : ℝ × ℝ) :
      MapsTo U {s | p.1 ≤ s ∧ (s, p.2) ∈ E}
        {s | U p.1 ≤ s ∧ (s, U p.2) ∈ D} :=
    fun _ hs => ⟨hmon hs.1, hmap _ hs.2⟩
  have hdout (p : ℝ × ℝ) (hp : p ∈ E) :
      ContinuousWithinAt dU {w | p.2 ≤ w ∧ (p.1, w) ∈ E} p.2 :=
    (hdc p.2 (hI p hp).2).mono (fun _ hw => (hI _ hw.2).2)
  have hdin (p : ℝ × ℝ) (hp : p ∈ E) :
      ContinuousWithinAt dU {s | p.1 ≤ s ∧ (s, p.2) ∈ E} p.1 :=
    (hdc p.1 (hI p hp).1).mono (fun _ hs => (hI _ hs.2).1)
  refine {
    off_axis := fun p hp => (hU.lt_iff_lt).mp (h.off_axis (hmap p hp))
    radius_out := fun u a b hab hs => SSFields.pullback_radius_out (hG a b hab (houtI u a b hs))
      (h.radius_out (U u) (U a) (U b) (hmon hab) (hout u a b hab hs))
    radius_in := fun v a b hab hs => SSFields.pullback_radius_in (hG a b hab (hinI v a b hs))
      (h.radius_in (U v) (U a) (U b) (hmon hab) (hin v a b hab hs))
    psi_out := fun u a b hab hs => SSFields.pullback_psi_out (hG a b hab (houtI u a b hs))
      (h.psi_out (U u) (U a) (U b) (hmon hab) (hout u a b hab hs))
    psi_in := fun v a b hab hs => SSFields.pullback_psi_in (hG a b hab (hinI v a b hs))
      (h.psi_in (U v) (U a) (U b) (hmon hab) (hin v a b hab hs))
    mass_out := fun u a b hab hs => SSFields.pullback_mass_out (hG a b hab (houtI u a b hs))
      (fun x hx => ne_of_gt (hpos x (houtI u a b hs (by simpa [uIcc_of_le hab] using hx))))
      (h.mass_out (U u) (U a) (U b) (hmon hab) (hout u a b hab hs))
    mass_in := fun v a b hab hs => SSFields.pullback_mass_in (hG a b hab (hinI v a b hs))
      (fun x hx => ne_of_gt (hpos x (hinI v a b hs (by simpa [uIcc_of_le hab] using hx))))
      (h.mass_in (U v) (U a) (U b) (hmon hab) (hin v a b hab hs))
    lam_in := fun v a b hab hs => SSFields.pullback_lam_in (hG a b hab (hinI v a b hs))
      (h.lam_in (U v) (U a) (U b) (hmon hab) (hin v a b hab hs))
    nu_out := fun u a b hab hs => SSFields.pullback_nu_out (hG a b hab (houtI u a b hs))
      (h.nu_out (U u) (U a) (U b) (hmon hab) (hout u a b hab hs))
    dvpsi_in := fun v a b hab hs => SSFields.pullback_dvpsi_in (hG a b hab (hinI v a b hs))
      (h.dvpsi_in (U v) (U a) (U b) (hmon hab) (hin v a b hab hs))
    dupsi_out := fun u a b hab hs => SSFields.pullback_dupsi_out (hG a b hab (houtI u a b hs))
      (h.dupsi_out (U u) (U a) (U b) (hmon hab) (hout u a b hab hs))
    scalar_ac_out := fun u a b hab hs => absolutelyContinuous_comp_gauge
      (f := S.phi (U u)) (T := U) (dT := dU) hab
      (hmon.monotoneOn _) (hderiv a b hab (houtI u a b hs))
      (fun x hx => (hpos x (houtI u a b hs hx)).le)
      (h.scalar_ac_out (U u) (U a) (U b) (hmon hab) (hout u a b hab hs))
    scalar_ac_in := fun v a b hab hs => absolutelyContinuous_comp_gauge
      (f := fun u => S.phi u (U v)) (T := U) (dT := dU) hab
      (hmon.monotoneOn _) (hderiv a b hab (hinI v a b hs))
      (fun x hx => (hpos x (hinI v a b hs hx)).le)
      (h.scalar_ac_in (U v) (U a) (U b) (hmon hab) (hin v a b hab hs))
    radius_axis_limit := fun a ha => (h.radius_axis_limit (U a) (hA a ha)).comp
      (tendsto_mapped_axis_filter hU hc hmap)
    mass_axis_limit := fun a ha => (h.mass_axis_limit (U a) (hA a ha)).comp
      (tendsto_mapped_axis_filter hU hc hmap)
    scalar_axis_variation := fun a ha =>
      (h.scalar_axis_variation (U a) (hA a ha)).pullback hU hc hmap
    expansion_axis_limit := ?_
    psi_axis_limit := ?_
    lam_right_cont := fun p hp =>
      ((h.lam_right_cont _ (hmap p hp)).comp_of_eq hc.continuousWithinAt (houtmap p) rfl).mul
        (hdout p hp)
    theta_right_cont := ?_
    nu_right_cont := fun p hp =>
      ((h.nu_right_cont _ (hmap p hp)).comp_of_eq hc.continuousWithinAt (hinmap p) rfl).mul
        (hdin p hp)
    zeta_right_cont := ?_ }
  · intro a ha
    have ht := tendsto_mapped_axis_filter (a := a) hU hc hmap
    have hdi : Tendsto dU (𝓝[>] a ⊓ 𝓟 {v | (a, v) ∈ E}) (𝓝 (dU a)) := by
      apply (hdc a (hB ha)).tendsto.mono_left
      apply le_inf (inf_le_left.trans nhdsWithin_le_nhds)
      apply le_principal_iff.mpr
      have hm : ∀ᶠ v in 𝓝[>] a ⊓ 𝓟 {v | (a, v) ∈ E}, (a, v) ∈ E :=
        Filter.Eventually.filter_mono inf_le_right (by simp)
      exact hm.mono (fun v hv => (hI (a, v) hv).2)
    rcases hbound a ha with ⟨C, hb⟩
    have hmismatch := bdd_le_mul_tendsto_zero' C (hb.mono (fun _ hv => hv.1))
      (by simpa using hdi.sub_const (dU a))
    have hs := ((h.expansion_axis_limit (U a) (hA a ha)).comp ht).mul_const (dU a)
    simpa only [Function.comp_def, SSFields.pullback_expansion_sum, mul_zero, zero_mul, zero_add]
      using hs.add hmismatch
  · intro a ha
    have ht := tendsto_mapped_axis_filter (a := a) hU hc hmap
    have hdi : Tendsto dU (𝓝[>] a ⊓ 𝓟 {v | (a, v) ∈ E}) (𝓝 (dU a)) := by
      apply (hdc a (hB ha)).tendsto.mono_left
      apply le_inf (inf_le_left.trans nhdsWithin_le_nhds)
      apply le_principal_iff.mpr
      have hm : ∀ᶠ v in 𝓝[>] a ⊓ 𝓟 {v | (a, v) ∈ E}, (a, v) ∈ E :=
        Filter.Eventually.filter_mono inf_le_right (by simp)
      exact hm.mono (fun v hv => (hI (a, v) hv).2)
    rcases hbound a ha with ⟨C, hb⟩
    have hmismatch := bdd_le_mul_tendsto_zero' C (hb.mono (fun _ hv => hv.2))
      (by simpa using hdi.sub_const (dU a))
    have hs := ((h.psi_axis_limit (U a) (hA a ha)).comp ht).mul_const (dU a)
    have he (v : ℝ) : (S.pullback U dU).dvpsi a v + (S.pullback U dU).dupsi a v =
        (S.dvpsi (U a) (U v) + S.dupsi (U a) (U v)) * dU a +
          S.dvpsi (U a) (U v) * (dU v - dU a) := by
      simp only [SSFields.pullback]
      ring
    simpa only [Function.comp_def, he, mul_zero, zero_mul, zero_add] using hs.add hmismatch
  · intro p hp
    convert
      ((h.theta_right_cont _ (hmap p hp)).comp_of_eq hc.continuousWithinAt (houtmap p) rfl).mul
        (hdout p hp) using 1
    funext w
    simp only [SSFields.pullback_theta, Function.comp_apply, Pi.mul_apply]
  · intro p hp
    convert
      ((h.zeta_right_cont _ (hmap p hp)).comp_of_eq hc.continuousWithinAt (hinmap p) rfl).mul
        (hdin p hp) using 1
    funext s
    simp only [SSFields.pullback_zeta, Function.comp_apply, Pi.mul_apply]

end AcExtensionPrinciple

end
