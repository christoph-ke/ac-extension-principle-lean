module

public import AcExtensionPrinciple.Decay.ClassRayConsequences
public import AcExtensionPrinciple.Decay.BadRadiusEnvelope

/-!
# The class-level bad-radius envelope

Paper `e1a0fd5`, lines 859–891. Strict bad points persist by off-axis
continuity. Mass monotonicity supplies the continuous majorant and outward
persistence supplies the exterior bound including equality at r=b.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- Bad points in the entire future triangle; paper `e1a0fd5`,
`eq:bad-radius-envelope`, lines 861–864. -/
@[expose] def decayBadPoints (ui : ℝ) (S : SSFields) (eps : ℝ) : Set (ℝ × ℝ) :=
  {p ∈ pastTriangle ui | eps < S.mu p.1 p.2}

/-- The paper's b* constructed from the shared envelope; paper `e1a0fd5`,
`eq:bad-radius-envelope`, lines 861–864. -/
@[expose] noncomputable def decayEnvelope (ui : ℝ) (S : SSFields) (eps u : ℝ) : ℝ :=
  badRadiusEnvelope (decayBadPoints ui S eps) (fun p => S.r p.1 p.2) u

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Every strict bad point has positive radius. Paper `e1a0fd5`, lines 859–869. -/
theorem decay_bad_off_axis {eps : ℝ} (heps : 0 < eps) {p : ℝ × ℝ}
    (hp : p ∈ decayBadPoints ui S eps) : p.1 < p.2 := by
  rcases hp.1.2.2.1.eq_or_lt with he | he
  · have hm := h.mu_axis ⟨hp.1.1, hp.1.2.1, rfl⟩
    have hb := hp.2
    rw [← he, hm] at hb
    exact False.elim (by linarith)
  · exact he

/-- Future bad radii are bounded by the remaining time. Paper `e1a0fd5`, line 865. -/
theorem decay_future_bdd (eps u : ℝ) :
    BddAbove (futureRadii (decayBadPoints ui S eps) (fun p => S.r p.1 p.2) u) := by
  refine ⟨-u, ?_⟩
  rintro _ ⟨p, ⟨hp, hup⟩, rfl⟩
  have hr := (h.radius_bounds hp.1).2
  linarith [hp.1.2.2.2]

/-- Strict bad points persist to later outgoing times at almost the same radius.
Paper `e1a0fd5`, line 869. -/
theorem decay_bad_persistence {eps : ℝ} (heps : 0 < eps) {p : ℝ × ℝ}
    (hp : p ∈ decayBadPoints ui S eps) {z : ℝ} (hz : z < S.r p.1 p.2) :
    ∃ q ∈ decayBadPoints ui S eps, p.1 < q.1 ∧ q.1 < 0 ∧ z < S.r q.1 q.2 := by
  let D := {q ∈ pastTriangle ui | q.1 < q.2}
  have huv := h.decay_bad_off_axis heps hp
  have hpair : Tendsto (fun t : ℝ => (t, p.2)) (𝓝[>] p.1) (𝓝[D] p) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · have ht : Tendsto (fun t : ℝ => t) (𝓝[>] p.1) (𝓝 p.1) := nhdsWithin_le_nhds
      simpa using ht.prodMk_nhds (tendsto_const_nhds (x := p.2))
    filter_upwards [Ioo_mem_nhdsGT huv] with t ht
    exact ⟨⟨hp.1.1.trans ht.1.le, ht.2.trans_le hp.1.2.2.2, ht.2.le,
      hp.1.2.2.2⟩, ht.2⟩
  have hm : Tendsto (fun q : ℝ × ℝ => S.mu q.1 q.2) (𝓝[D] p) (𝓝 (S.mu p.1 p.2)) :=
    h.decay_continuous_mu p ⟨hp.1, huv⟩
  have hr : Tendsto (fun q : ℝ × ℝ => S.r q.1 q.2) (𝓝[D] p) (𝓝 (S.r p.1 p.2)) :=
    (h.regularCenter.continuous_r.mono (fun _ hq => hq.1)) p ⟨hp.1, huv⟩
  have hI : ∀ᶠ t : ℝ in 𝓝[>] p.1, t ∈ Ioo p.1 p.2 := Ioo_mem_nhdsGT huv
  obtain ⟨t, ht, hmt, hrt⟩ := (hI.and
    (((hm.comp hpair).eventually (lt_mem_nhds hp.2)).and
      ((hr.comp hpair).eventually (lt_mem_nhds hz)))).exists
  refine ⟨(t, p.2), ⟨⟨hp.1.1.trans ht.1.le, ht.2.trans_le hp.1.2.2.2,
    ht.2.le, hp.1.2.2.2⟩, hmt⟩, ht.1, ht.2.trans_le hp.1.2.2.2, hrt⟩

/-- The bad-radius scale follows from both mass monotonicities.
Paper `e1a0fd5`, `eq:bad-radius-scale`, lines 865–868. -/
theorem decay_envelope_majorant {eps u : ℝ} (heps : 0 < eps) (hui : ui ≤ u)
    (_hu0 : u < 0)
    (hne : (futureRadii (decayBadPoints ui S eps) (fun p => S.r p.1 p.2) u).Nonempty) :
    decayEnvelope ui S eps u ≤ 2 * S.m u 0 / eps := by
  apply csSup_le hne
  rintro _ ⟨p, ⟨hp, hup⟩, rfl⟩
  have huv := h.decay_bad_off_axis heps hp
  have hr := h.r_pos hp.1 huv
  have hm1 := h.decay_mass_out_le hp.1.2.2.2 hp.1.1 hp.1.2.1 hp.1.2.2.1 le_rfl
  have hm2 := h.decay_mass_in_le hup hui hp.1.2.1 hp.1.2.1.le le_rfl
  have hh : eps * S.r p.1 p.2 < 2 * S.m p.1 p.2 :=
    (lt_div_iff₀ hr).mp hp.2
  apply (le_div_iff₀ heps).mpr
  nlinarith

/-- Complete envelope properties for the dyadic selector; future nonemptiness
is discharged by failure of uniform mass decay. Paper `e1a0fd5`, lines 859–869. -/
theorem decay_envelope_properties {eps u₀ : ℝ} (heps : 0 < eps) (hui : ui ≤ u₀)
    (hu0 : u₀ < 0)
    (hne : ∀ u ∈ Ico u₀ 0,
      (futureRadii (decayBadPoints ui S eps) (fun p => S.r p.1 p.2) u).Nonempty) :
    AntitoneOn (decayEnvelope ui S eps) (Ico u₀ 0) ∧
    (∀ u ∈ Ico u₀ 0, ContinuousWithinAt (decayEnvelope ui S eps) (Ici u) u) ∧
    Tendsto (decayEnvelope ui S eps) (𝓝[<] 0) (𝓝 0) ∧
    (∀ u ∈ Ico u₀ 0, 0 < decayEnvelope ui S eps u) ∧
    (∀ u ∈ Ico u₀ 0, decayEnvelope ui S eps u ≤ 2 * S.m u 0 / eps) := by
  have hbd := fun u (_ : u ∈ Ico u₀ 0) => h.decay_future_bdd eps u
  have hpos (u : ℝ) (hu : u ∈ Ico u₀ 0) : 0 < decayEnvelope ui S eps u := by
    obtain ⟨_, ⟨p, ⟨hp, hup⟩, rfl⟩⟩ := hne u hu
    exact (h.r_pos hp.1 (h.decay_bad_off_axis heps hp)).trans_le
      (le_csSup (hbd u hu) ⟨p, ⟨hp, hup⟩, rfl⟩)
  refine ⟨badRadiusEnvelope_antitoneOn hne hbd, ?_, ?_, hpos, ?_⟩
  · intro u hu
    apply badRadiusEnvelope_right_continuous hne hbd hu
    intro p hp hup z hz
    obtain ⟨q, hq, hpq, hq0, hzq⟩ := h.decay_bad_persistence heps hp hz
    exact ⟨q, hq, hup.trans_lt hpq, hq0, hzq⟩
  · apply squeeze_zero' _ _ (by
      simpa using (show Tendsto (fun u : ℝ => u) (𝓝[<] 0) (𝓝 0) from
        nhdsWithin_le_nhds).neg)
    · filter_upwards [Ioo_mem_nhdsLT hu0] with u hu
      exact (hpos u ⟨hu.1.le, hu.2⟩).le
    · filter_upwards [Ioo_mem_nhdsLT hu0] with u hu
      apply csSup_le (hne u ⟨hu.1.le, hu.2⟩)
      rintro _ ⟨p, ⟨hp, hup⟩, rfl⟩
      linarith [(h.radius_bounds hp.1).2, hp.1.2.2.2]
  · intro u hu
    exact h.decay_envelope_majorant heps (hui.trans hu.1) hu.2 (hne u hu)

/-- Continuity extends the exterior bound to r=b when the terminal radius leaves outward room. Paper
`e1a0fd5`, lines 884–891 (the past exterior). -/
theorem decay_exterior_bound {eps b u₀ u v : ℝ} (heps : 0 < eps) (hb : 0 < b)
    (hp : (u, v) ∈ pastTriangle ui) (hu : u₀ ≤ u)
    (hR : 2 * b ≤ S.r u 0) (hr : b ≤ S.r u v)
    (henv : decayEnvelope ui S eps u₀ ≤ b) : S.mu u v ≤ eps := by
  by_contra hnot
  have hbad : (u, v) ∈ decayBadPoints ui S eps := ⟨hp, lt_of_not_ge hnot⟩
  have hle : S.r u v ≤ b := (le_csSup (h.decay_future_bdd eps u₀)
    ⟨(u, v), ⟨hbad, hu⟩, rfl⟩).trans henv
  have heq : S.r u v = b := le_antisymm hle hr
  have huv := h.decay_bad_off_axis heps hbad
  have hv0 : v < 0 := by
    rcases hp.2.2.2.eq_or_lt with hv | hv
    · change v = 0 at hv
      subst v
      linarith
    · exact hv
  let D := {p ∈ pastTriangle ui | p.1 < p.2}
  have hpair : Tendsto (fun w : ℝ => (u, w)) (𝓝[>] v) (𝓝[D] (u, v)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_const_nhds.prodMk_nhds nhdsWithin_le_nhds, ?_⟩
    filter_upwards [Ioo_mem_nhdsGT hv0] with w hw
    exact ⟨⟨hp.1, hp.2.1, (huv.trans hw.1).le, hw.2.le⟩, huv.trans hw.1⟩
  have hm : Tendsto (fun p : ℝ × ℝ => S.mu p.1 p.2)
      (𝓝[D] (u, v)) (𝓝 (S.mu u v)) := h.decay_continuous_mu (u, v) ⟨hp, huv⟩
  have hI : ∀ᶠ w : ℝ in 𝓝[>] v, w ∈ Ioo v 0 := Ioo_mem_nhdsGT hv0
  obtain ⟨w, hw, hmw⟩ := (hI.and
    ((hm.comp hpair).eventually (lt_mem_nhds hbad.2))).exists
  have hrw := h.decay_radius_out_strict hw.1 hp.1 hp.2.1 huv.le hw.2.le
  have hwb : (u, w) ∈ decayBadPoints ui S eps :=
    ⟨⟨hp.1, hp.2.1, (huv.trans hw.1).le, hw.2.le⟩, hmw⟩
  have hbnd := (le_csSup (h.decay_future_bdd eps u₀)
    ⟨(u, w), ⟨hwb, hu⟩, rfl⟩).trans henv
  linarith

end StandingFull

end AcExtensionPrinciple

end
