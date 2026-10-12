module

public import AcExtensionPrinciple.GeometricBounds.RayBounds
public import AcExtensionPrinciple.Reduced.OutgoingRay

/-!
# Late outgoing expansion comparison in the solution class

Paper `e1a0fd5`, `eq:late-radial-expansion-comparison`,
`equations.tex` lines 1130–1144. The late mass-ratio bound is an explicit
premise Propositions 2.7/2.8; no regularity premise is added.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory Filter

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Radius is AC on each outgoing segment. Paper `e1a0fd5`,
`eq:radius`, `eq:late-radial-expansion-comparison`, lines 1137–1142. -/
theorem weighted_radius_ac_out {u a b : ℝ} (hu : ui ≤ u) (hu0 : u < 0)
    (hua : u ≤ a) (hab : a ≤ b) (hb0 : b ≤ 0) :
    AbsolutelyContinuousOnInterval (S.r u) a b := by
  apply intervalPrimitive_ac (g := S.lam u) hab
  intro x hx
  exact h.regularCenter.localBV.radius_out u a x hx.1
    (outSeg_subset_triangle hu hu0 hua (hx.2.trans hb0))

/-- Incoming expansion is AC on off-axis outgoing segments, from its
primitive. Paper `e1a0fd5`, `eq:radius`, lines 1137–1142. -/
theorem weighted_nu_ac_out {u a b : ℝ} (hu : ui ≤ u) (hu0 : u < 0)
    (hua : u < a) (hab : a ≤ b) (hb0 : b ≤ 0) :
    AbsolutelyContinuousOnInterval (S.nu u) a b := by
  apply intervalPrimitive_ac (g := S.radiusCoeff u) hab
  intro x hx
  exact h.regularCenter.localBV.nu_out u a x hx.1
    (outSeg_subset_offAxis hu hu0 hua (hx.2.trans hb0))

/-- The outgoing logarithmic expansion primitive holds through the terminal
ray. Paper `e1a0fd5`, `eq:logarithmic-expansions`, lines 1137–1142. -/
theorem weighted_log_neg_nu_primitive {u a b : ℝ} (hu : ui ≤ u) (hu0 : u < 0)
    (hua : u < a) (hab : a ≤ b) (hb0 : b ≤ 0) :
    IntervalPrimitive (fun v => Real.log (-S.nu u v))
      (fun v => S.kappa u v * S.varkappa u v) a b := by
  have hac := (h.weighted_nu_ac_out hu hu0 hua hab hb0).fun_neg
  apply ac_integral_eq_sub hab (positive_ac_log hac ?_)
  · have hd := intervalPrimitive_ae_hasDerivAt hab
      (f := S.nu u) (g := S.radiusCoeff u) (fun x hx =>
        h.regularCenter.localBV.nu_out u a x hx.1
          (outSeg_subset_offAxis hu hu0 hua (hx.2.trans hb0)))
    filter_upwards [hd] with x hx
    intro hxI
    have hp : (u, x) ∈ pastTriangle ui :=
      ⟨hu, hu0, (hua.trans hxI.1).le, hxI.2.le.trans hb0⟩
    exact OutgoingRay.log_neg_nu (r := S.r u) (m := S.m u) (lam := S.lam u)
      ((hx hxI).congr_deriv (S.radiusCoeff_eq u x)) (h.nu_neg hp)
  · intro x hx
    rw [uIcc_of_le hab] at hx
    exact neg_pos.mpr (h.nu_neg (p := (u, x))
      ⟨hu, hu0, (hua.trans_le hx.1).le, hx.2.trans hb0⟩)

/-- The radius logarithm primitive. Paper `e1a0fd5`,
`eq:late-radial-expansion-comparison`, lines 1137–1142. -/
theorem weighted_log_radius_primitive {u a b : ℝ} (hu : ui ≤ u) (hu0 : u < 0)
    (hua : u < a) (hab : a ≤ b) (hb0 : b ≤ 0) :
    IntervalPrimitive (fun v => Real.log (S.r u v))
      (fun v => S.lam u v / S.r u v) a b := by
  apply ac_integral_eq_sub hab
    (positive_ac_log (h.weighted_radius_ac_out hu hu0 hua.le hab hb0) ?_)
  · have hd := intervalPrimitive_ae_hasDerivAt hab (f := S.r u) (g := S.lam u)
      (fun x hx => h.regularCenter.localBV.radius_out u a x hx.1
        (outSeg_subset_triangle hu hu0 hua.le (hx.2.trans hb0)))
    filter_upwards [hd] with x hx
    intro hxI
    exact (hx hxI).log (h.r_pos
      ⟨hu, hu0, (hua.trans hxI.1).le, hxI.2.le.trans hb0⟩ (hua.trans hxI.1)).ne'
  · intro x hx
    rw [uIcc_of_le hab] at hx
    exact h.r_pos ⟨hu, hu0, (hua.trans_le hx.1).le, hx.2.trans hb0⟩
      (hua.trans_le hx.1)

/-- W1: the late expansion comparison from standing assumptions and exactly
the late mass-ratio conclusion. Paper `e1a0fd5`,
`eq:late-radial-expansion-comparison`, lines 1139–1142. -/
theorem late_radial_expansion_comparison_of_smallness {u a b δ : ℝ}
    (hu : ui ≤ u) (hu0 : u < 0) (hua : u < a) (hab : a ≤ b) (hb0 : b ≤ 0)
    (hsmall : ∀ v ∈ Icc a b, S.mu u v / (1 - S.mu u v) ≤ δ) :
    1 ≤ (-S.nu u b) / (-S.nu u a) ∧
      (-S.nu u b) / (-S.nu u a) ≤ (S.r u b / S.r u a) ^ δ := by
  have hp (x : ℝ) (hx : x ∈ Icc a b) : (u, x) ∈ pastTriangle ui :=
    ⟨hu, hu0, (hua.trans_le hx.1).le, hx.2.trans hb0⟩
  have ha0 := neg_pos.mpr (h.nu_neg (hp a ⟨le_rfl, hab⟩))
  have hb0' := neg_pos.mpr (h.nu_neg (hp b ⟨hab, le_rfl⟩))
  have hra := h.r_pos (hp a ⟨le_rfl, hab⟩) hua
  have hrb := h.r_pos (hp b ⟨hab, le_rfl⟩) (hua.trans_le hab)
  have hn := h.weighted_log_neg_nu_primitive hu hu0 hua hab hb0
  have hr := h.weighted_log_radius_primitive hu hu0 hua hab hb0
  have hl : Real.log (-S.nu u b) - Real.log (-S.nu u a) ≤
      δ * (Real.log (S.r u b) - Real.log (S.r u a)) := by
    rw [hn.2, hr.2, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hab hn.1 (hr.1.const_mul δ)
    intro x hx
    have hxp := hp x hx
    have hfac : 0 ≤ S.lam u x / S.r u x :=
      (div_pos (h.lam_pos hxp) (h.r_pos hxp (hua.trans_le hx.1))).le
    calc
      S.kappa u x * S.varkappa u x =
          (S.mu u x / (1 - S.mu u x)) * (S.lam u x / S.r u x) := by
        unfold SSFields.kappa SSFields.varkappa kappaOf varkappaOf
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hsmall x hx) hfac
  refine ⟨(le_div_iff₀ ha0).mpr ?_, ?_⟩
  · simpa using neg_le_neg (h.nu_le_of_le hu hu0 hua hab hb0)
  · have he := Real.exp_le_exp.mpr hl
    rw [Real.exp_sub, Real.exp_log hb0', Real.exp_log ha0,
      ← Real.log_div hrb.ne' hra.ne', mul_comm δ,
      ← Real.rpow_def_of_pos (div_pos hrb hra)] at he
    exact he

end StandingFull

end AcExtensionPrinciple

end
