module

public import AcExtensionPrinciple.Minimal.OneSidedScalarRays
public import AcExtensionPrinciple.Minimal.MassContinuity
public import AcExtensionPrinciple.Solution.PositiveAC
public import AcExtensionPrinciple.Decay.ScalarComparison

/-!
# Incoming normalized scalar traces from outgoing damping

Paper `e1a0fd5`, `equations.tex` lines 99–105 and 974–986,
`eq:normalized-scalar-transport`, `eq:incoming-normalized-damping`.
The four-field source class suffices for the closed-cone comparison. Joint φ
continuity at an axis point is an explicit helper premise for the joint incoming
trace below; `ScalarAxis` derives it independently, and `OneSidedTraces` supplies it.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- The incoming normalized datum is AC on off-axis outgoing segments using
only primitive equations. Paper `e1a0fd5`, lines 99–105, 974–979. -/
theorem StandingAssumptions.oneSided_incoming_ac_out {ui u a b : ℝ} {S : SSFields}
    (h : StandingAssumptions ui S) (hab : a ≤ b) (hu : ui ≤ u)
    (hu0 : u < 0) (hua : u < a) (hb0 : b ≤ 0) :
    AbsolutelyContinuousOnInterval (fun v => S.dupsi u v / S.nu u v) a b := by
  have hs (x : ℝ) (hx : x ∈ Icc a b) :=
    outSeg_subset_offAxis hu hu0 hua (hx.2.trans hb0)
  have hd := intervalPrimitive_ac hab
    (fun x hx => h.regularCenter.localBV.dupsi_out u a x hx.1 (hs x hx))
  have hn := intervalPrimitive_ac hab
    (fun x hx => h.regularCenter.localBV.nu_out u a x hx.1 (hs x hx))
  have hi := (positive_ac_inv hn.fun_neg (fun x hx => by
    rw [uIcc_of_le hab] at hx
    exact neg_pos.mpr (h.nu_neg (p := (u, x))
      ⟨hu, hu0, (hua.trans_le hx.1).le, hx.2.trans hb0⟩))).fun_neg
  simpa only [neg_inv, neg_neg, div_eq_mul_inv] using hd.fun_mul hi

/-- Damping follows from the ν and duψ primitive equations, without joint traces.
Paper `e1a0fd5`, lines 99–105, 974–979, `eq:incoming-normalized-damping`. -/
theorem StandingAssumptions.oneSided_incoming_damping_ae {ui u a b : ℝ} {S : SSFields}
    (h : StandingAssumptions ui S) (hab : a ≤ b) (hu : ui ≤ u)
    (hu0 : u < 0) (hua : u < a) (hb0 : b ≤ 0) :
    ∀ᵐ x, x ∈ Ioo a b → HasDerivAt (fun v => S.dupsi u v / S.nu u v)
      (-(S.kappa u x * S.varkappa u x) * (S.dupsi u x / S.nu u x - S.phi u x)) x := by
  have hs (x : ℝ) (hx : x ∈ Icc a b) :=
    outSeg_subset_offAxis hu hu0 hua (hx.2.trans hb0)
  have hd := intervalPrimitive_ae_hasDerivAt hab
    (fun x hx => h.regularCenter.localBV.dupsi_out u a x hx.1 (hs x hx))
  have hn := intervalPrimitive_ae_hasDerivAt hab
    (fun x hx => h.regularCenter.localBV.nu_out u a x hx.1 (hs x hx))
  filter_upwards [hd, hn] with x hdx hnx hx
  convert (hdx hx).div (hnx hx) (h.nu_neg (p := (u, x))
    ⟨hu, hu0, (hua.trans hx.1).le, hx.2.le.trans hb0⟩).ne using 1
  rw [S.radiusCoeff_eq u x]
  field_simp [(h.nu_neg (p := (u, x))
    ⟨hu, hu0, (hua.trans hx.1).le, hx.2.le.trans hb0⟩).ne]
  ring

/-- The closed-cone incoming comparison needs only the outgoing dupsi trace.
Paper `e1a0fd5`, lines 974–986, `eq:incoming-scalar-comparison`. -/
theorem StandingAssumptions.oneSided_incoming_comparison {ui u v L M : ℝ} {S : SSFields}
    (h : StandingAssumptions ui S) (hp : (u, v) ∈ pastTriangle ui)
    (hphi : ∀ w ∈ Icc u v, |S.phi u w - L| ≤ M) :
    |S.dupsi u v / S.nu u v - L| ≤ M := by
  rcases hp.2.2.1.eq_or_lt with huv | huv
  · change u = v at huv
    subst v
    rw [h.regularCenter.axis_dupsi_value u ⟨hp.1, hp.2.1, rfl⟩]
    exact hphi u ⟨le_rfl, le_rfl⟩
  · have htr : Tendsto (fun a => S.dupsi u a / S.nu u a) (𝓝[>] u)
        (𝓝 (S.phi u u)) :=
      oneSided_outgoing_reparam (f := fun a => S.dupsi u a / S.nu u a)
        (h.regularCenter.axis_dupsi_out u ⟨hp.1, hp.2.1, rfl⟩)
    have hlim := (htr.sub_const L).abs.max (tendsto_const_nhds (x := M))
    have hbound : ∀ᶠ a in 𝓝[>] u,
        |S.dupsi u v / S.nu u v - L| ≤ max (|S.dupsi u a / S.nu u a - L|) M := by
      filter_upwards [Ioo_mem_nhdsGT huv] with a ha
      apply incoming_scalar_comparison_bound ha.2.le
        (h.oneSided_incoming_ac_out ha.2.le hp.1 hp.2.1 ha.1 hp.2.2.2)
        (le_max_left _ _)
        (fun w hw => (hphi w ⟨ha.1.le.trans hw.1, hw.2⟩).trans (le_max_right _ _))
      · apply Eventually.of_forall
        intro w hw
        have hwp : (u, w) ∈ pastTriangle ui :=
          ⟨hp.1, hp.2.1, (ha.1.trans hw.1).le, hw.2.le.trans hp.2.2.2⟩
        exact mul_nonneg
          (div_nonneg (h.lam_pos hwp).le (sub_pos.mpr (h.mu_bounds hwp).2).le)
          (div_nonneg (h.mu_bounds hwp).1 (h.r_pos hwp (ha.1.trans hw.1)).le)
      · filter_upwards [h.oneSided_incoming_damping_ae ha.2.le hp.1 hp.2.1
          ha.1 hp.2.2.2] with w hw hwI
        exact (hw hwI).deriv
    have hh := ge_of_tendsto hlim hbound
    rw [max_eq_right (hphi u ⟨le_rfl, huv.le⟩)] at hh
    exact hh

/-- Joint scalar continuity at one axis point and outgoing damping give the
joint incoming normalized derivative trace there. `ScalarAxis` discharges the
scalar continuity premise without joint normalized traces. Paper `e1a0fd5`,
lines 247–261, 974–986, `eq:regular-axis-scalar-traces`, `eq:incoming-scalar-comparison`. -/
theorem StandingAssumptions.oneSided_dupsi_joint_of_phi_continuous
    {ui a : ℝ} {S : SSFields} (h : StandingAssumptions ui S)
    (_ha : (a, a) ∈ axis ui)
    (hphi : ContinuousWithinAt (fun p : ℝ × ℝ => S.phi p.1 p.2)
      (pastTriangle ui) (a, a)) :
    Tendsto (fun p : ℝ × ℝ => S.dupsi p.1 p.2 / S.nu p.1 p.2)
      (𝓝[pastTriangle ui \ axis ui] (a, a)) (𝓝 (S.phi a a)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := Metric.continuousWithinAt_iff.mp hphi (ε / 2) (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro p hp hpd
  have hc := h.oneSided_incoming_comparison hp.1 (L := S.phi a a) (M := ε / 2) (by
    intro w hw
    have hwQ : (p.1, w) ∈ pastTriangle ui :=
      ⟨hp.1.1, hp.1.2.1, hw.1, hw.2.trans hp.1.2.2.2⟩
    have hnear : dist (p.1, w) (a, a) < δ := by
      rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq, abs_lt, abs_lt] at hpd ⊢
      exact ⟨hpd.1, ⟨by dsimp only at *; linarith [hw.1, hpd.1.1],
        by dsimp only at *; linarith [hw.2, hpd.2.2]⟩⟩
    have hh := hb hwQ hnear
    rw [Real.dist_eq] at hh
    exact hh.le)
  rw [Real.dist_eq]
  exact hc.trans_lt (by linarith)

end AcExtensionPrinciple

end
