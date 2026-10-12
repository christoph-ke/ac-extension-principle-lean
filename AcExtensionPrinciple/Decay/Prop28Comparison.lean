module

public import AcExtensionPrinciple.Decay.ClassScalarTransport

/-!
# Scalar comparisons including the regular axis

Paper `e1a0fd5`, lines 964–989. Limits through compact off-axis segments
recover the closed-cone statements by the prescribed continuous axis traces
and their actual values in the corrected standing class.
-/

public section

namespace AcExtensionPrinciple.StandingFull

open Set Filter MeasureTheory
open scoped Topology

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Incoming-ray comparison extends to its regular axis endpoint.
Paper `e1a0fd5`, `eq:scalar-nearby-cone-comparison`, lines 964–971. -/
theorem decay_datum_comparison_closed {v a b M : ℝ} (hab : a ≤ b) (ha : ui ≤ a)
    (hb0 : b < 0) (hbv : b ≤ v) (hv0 : v ≤ 0)
    (hA : ∀ x ∈ Icc a b, |S.dvpsi x v / S.lam x v - S.phi x v| ≤ M) :
    |S.dvpsi b v / S.lam b v - S.dvpsi a v / S.lam a v| ≤ Bstar ui S * M := by
  rcases hbv.eq_or_lt with he | he
  · subst v
    rcases hab.eq_or_lt with hab | hab
    · subst b
      have hM := (abs_nonneg _).trans (hA a ⟨le_rfl, le_rfl⟩)
      simpa using mul_nonneg (show 0 ≤ Bstar ui S from ENNReal.toReal_nonneg) hM
    · have hpair : Tendsto (fun t : ℝ => (t, b)) (𝓝[<] b)
          (𝓝[pastTriangle ui \ axis ui] (b, b)) := by
        apply tendsto_nhdsWithin_iff.mpr
        refine ⟨(show Tendsto (fun t : ℝ => t) (𝓝[<] b) (𝓝 b) from
          nhdsWithin_le_nhds).prodMk_nhds tendsto_const_nhds, ?_⟩
        filter_upwards [Ioo_mem_nhdsLT hab] with t ht
        refine ⟨⟨ha.trans ht.1.le, ht.2.trans hb0, ht.2.le, hb0.le⟩, ?_⟩
        change ¬(ui ≤ t ∧ t < 0 ∧ b = t)
        exact fun haxis => (ne_of_lt ht.2) haxis.2.2.symm
      have htr : Tendsto (fun t => S.dvpsi t b / S.lam t b) (𝓝[<] b)
          (𝓝 (S.phi b b)) := by
        simpa only [Function.comp_def] using
          (h.regularCenter.axis_dvpsi_trace b ⟨ha.trans hab.le, hb0, rfl⟩).comp hpair
      have hlim := (htr.sub_const (S.dvpsi a b / S.lam a b)).abs
      have hbound : ∀ᶠ t in 𝓝[<] b,
          |S.dvpsi t b / S.lam t b - S.dvpsi a b / S.lam a b| ≤ Bstar ui S * M := by
        filter_upwards [Ioo_mem_nhdsLT hab] with t ht
        exact h.decay_datum_comparison ht.1.le ha (ht.2.trans hb0) ht.2 hb0.le
          (fun x hx => hA x ⟨hx.1, hx.2.trans ht.2.le⟩)
      rw [h.regularCenter.axis_dvpsi_value b ⟨ha.trans hab.le, hb0, rfl⟩]
      exact le_of_tendsto hlim hbound
  · exact h.decay_datum_comparison hab ha hb0 he hv0 hA

/-- Damping and the actual axis value give the incoming scalar comparison
on a whole closed cone segment. Paper `e1a0fd5`,
`eq:incoming-scalar-comparison`, lines 974–987. -/
theorem decay_incoming_scalar_bound {u v L M : ℝ} (hp : (u, v) ∈ pastTriangle ui)
    (hphi : ∀ w ∈ Icc u v, |S.phi u w - L| ≤ M) :
    |S.dupsi u v / S.nu u v - L| ≤ M := by
  rcases hp.2.2.1.eq_or_lt with huv | huv
  · change u = v at huv
    subst v
    rw [h.regularCenter.axis_dupsi_value u ⟨hp.1, hp.2.1, rfl⟩]
    exact hphi u ⟨le_rfl, le_rfl⟩
  · have hpair : Tendsto (fun a : ℝ => (u, a)) (𝓝[>] u)
        (𝓝[pastTriangle ui \ axis ui] (u, u)) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨tendsto_const_nhds.prodMk_nhds nhdsWithin_le_nhds, ?_⟩
      filter_upwards [Ioo_mem_nhdsGT huv] with a ha
      refine ⟨⟨hp.1, hp.2.1, ha.1.le, ha.2.le.trans hp.2.2.2⟩, ?_⟩
      change ¬(ui ≤ u ∧ u < 0 ∧ a = u)
      exact fun haxis => (ne_of_gt ha.1) haxis.2.2
    have htr : Tendsto (fun a => S.dupsi u a / S.nu u a) (𝓝[>] u)
        (𝓝 (S.phi u u)) := by
      simpa only [Function.comp_def] using
        (h.regularCenter.axis_dupsi_trace u ⟨hp.1, hp.2.1, rfl⟩).comp hpair
    have hlim := (htr.sub_const L).abs.max (tendsto_const_nhds (x := M))
    have hbound : ∀ᶠ a in 𝓝[>] u,
        |S.dupsi u v / S.nu u v - L| ≤ max (|S.dupsi u a / S.nu u a - L|) M := by
      filter_upwards [Ioo_mem_nhdsGT huv] with a ha
      apply incoming_scalar_comparison_bound ha.2.le
        (h.decay_incoming_ac_out ha.2.le hp.1 hp.2.1 ha.1 hp.2.2.2) (le_max_left _ _)
        (fun w hw => (hphi w ⟨ha.1.le.trans hw.1, hw.2⟩).trans (le_max_right _ _))
      · apply Eventually.of_forall
        intro w hw
        have hwp : (u, w) ∈ pastTriangle ui :=
          ⟨hp.1, hp.2.1, (ha.1.trans hw.1).le, hw.2.le.trans hp.2.2.2⟩
        exact mul_nonneg (h.kappa_pos hwp).le
          (div_nonneg (h.mu_bounds hwp).1 (h.r_pos hwp (ha.1.trans hw.1)).le)
      · exact h.decay_incoming_deriv_out ha.2.le hp.1 hp.2.1 ha.1 hp.2.2.2
    have hh := ge_of_tendsto hlim hbound
    rw [max_eq_right (hphi u ⟨le_rfl, huv.le⟩)] at hh
    exact hh

end AcExtensionPrinciple.StandingFull

end
