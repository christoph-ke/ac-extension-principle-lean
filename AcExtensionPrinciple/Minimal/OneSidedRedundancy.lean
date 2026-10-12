module

public import AcExtensionPrinciple.Minimal.OneSidedPaths

/-!
# One outgoing normalized trace determines the other

Paper `e1a0fd5`, `equations.tex` lines 220–261,
`eq:regular-axis-scalar-traces`; Luk–Oh Definition 2.1(3),(7).
The retained expansion and ψ axis-sum limits make `axis_dupsi_out` redundant.
The source class keeps all four one-sided fields.
-/

public section

namespace AcExtensionPrinciple

open Set Filter
open scoped Topology

/-- The outgoing dvψ/λ trace determines the outgoing duψ/ν trace through the
retained expansion and ψ axis-sum limits. Every helper premise is a retained
source field. Paper `e1a0fd5`, lines 220–261, `eq:regular-axis-scalar-traces`. -/
theorem oneSided_dupsi_out_of_dvpsi_out {ui a : ℝ} {S : SSFields}
    (h : LocalBVSolution (pastTriangle ui) S)
    (hnu : ContinuousOn (fun p => S.nu p.1 p.2) (pastTriangle ui))
    (ha : (a, a) ∈ axis ui) (hexp : S.nu a a = -S.lam a a)
    (ht : Tendsto (fun ε => S.dvpsi a (a + ε) / S.lam a (a + ε))
      (𝓝[>] 0) (𝓝 (S.phi a a))) :
    Tendsto (fun ε => S.dupsi a (a + ε) / S.nu a (a + ε))
      (𝓝[>] 0) (𝓝 (S.phi a a)) := by
  have hp := axis_subset_pastTriangle ui ha
  have hlam {p : ℝ × ℝ} (hp : p ∈ pastTriangle ui) : 0 < S.lam p.1 p.2 := by
    obtain ⟨c, hc, hb⟩ := h.expansion_bounds {p} isCompact_singleton
      (singleton_subset_iff.mpr hp)
    exact hc.trans_le (hb p (mem_singleton p)).1
  have hn := (hnu (a, a) hp).tendsto.comp
    ((oneSided_outgoing_path ha).mono_right (nhdsWithin_mono _ sdiff_subset))
  have hl : Tendsto (fun ε => S.lam a (a + ε)) (𝓝[>] 0) (𝓝 (S.lam a a)) := by
    simpa only [Function.comp_def, add_sub_cancel_left, zero_sub, hexp, neg_neg] using
      (h.expansion_axis_limit a hp).sub hn
  have hdv : Tendsto (fun ε => S.dvpsi a (a + ε)) (𝓝[>] 0)
      (𝓝 (S.phi a a * S.lam a a)) := by
    apply (ht.mul hl).congr'
    filter_upwards [Ioo_mem_nhdsGT (neg_pos.mpr ha.2.1)] with ε hε
    exact div_mul_cancel₀ _ (hlam (p := (a, a + ε))
      ⟨ha.1, ha.2.1, by linarith [hε.1], by linarith [hε.2]⟩).ne'
  have hdu : Tendsto (fun ε => S.dupsi a (a + ε)) (𝓝[>] 0)
      (𝓝 (S.phi a a * S.nu a a)) := by
    simpa only [add_sub_cancel_left, zero_sub, hexp, mul_neg] using
      (h.psi_axis_limit a hp).sub hdv
  have hn0 : S.nu a a ≠ 0 := by rw [hexp]; exact neg_ne_zero.mpr (hlam hp).ne'
  have hdiv := hdu.div hn hn0
  rw [mul_div_cancel_right₀ _ hn0] at hdiv
  apply hdiv.congr'
  exact Eventually.of_forall (fun ε => by simp only [Function.comp_def, Pi.div_apply])

/-- Three one-sided fields suffice to construct the requested four-field source
class; outgoing duψ/ν is derived rather than assumed. Paper `e1a0fd5`,
lines 220–261, `eq:regular-axis-scalar-traces`. -/
theorem oneSided_regularCenter_of_three {ui : ℝ} {S : SSFields}
    (h : LocalBVSolution (pastTriangle ui) S)
    (hnu : ContinuousOn (fun p => S.nu p.1 p.2) (pastTriangle ui))
    (hexp : ∀ a, (a, a) ∈ axis ui → S.nu a a = -S.lam a a)
    (hdout : ∀ a, (a, a) ∈ axis ui →
      Tendsto (fun ε => S.dvpsi a (a + ε) / S.lam a (a + ε))
        (𝓝[>] 0) (𝓝 (S.phi a a)))
    (hdin : ∀ a, (a, a) ∈ axis ui →
      Tendsto (fun ε => S.dvpsi (a - ε) a / S.lam (a - ε) a)
        (𝓝[>] 0 ⊓ 𝓟 {ε | ui ≤ a - ε}) (𝓝 (S.phi a a)))
    (huin : ∀ a, (a, a) ∈ axis ui →
      Tendsto (fun ε => S.dupsi (a - ε) a / S.nu (a - ε) a)
        (𝓝[>] 0 ⊓ 𝓟 {ε | ui ≤ a - ε}) (𝓝 (S.phi a a)))
    (hdvalue : ∀ a, (a, a) ∈ axis ui → S.dvpsi a a / S.lam a a = S.phi a a)
    (huvalue : ∀ a, (a, a) ∈ axis ui → S.dupsi a a / S.nu a a = S.phi a a) :
    RegularCenterLocalACBV ui S := {
  localBV := h
  continuous_nu := hnu
  axis_expansions := hexp
  axis_dvpsi_out := hdout
  axis_dupsi_out := fun a ha => oneSided_dupsi_out_of_dvpsi_out h hnu ha (hexp a ha) (hdout a ha)
  axis_dvpsi_in := hdin
  axis_dupsi_in := huin
  axis_dvpsi_value := hdvalue
  axis_dupsi_value := huvalue
}

end AcExtensionPrinciple

end
