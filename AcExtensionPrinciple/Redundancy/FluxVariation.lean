module

public import AcExtensionPrinciple.Redundancy.CoreRaychaudhuri

/-!
# Incoming expansion transport controlled by scalar variation
Paper commit `e1a0fd5`, `equations.tex` lines 90–92, 220–275 and 334–339,
`eq:raychaudhuri`, `eq:regular-axis-scalar-traces`, `eq:incoming-flux-identity`.
The normalized scalar amplitude converts the quadratic flux into an AC scalar derivative.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- Incoming scalar primitives give the encoded scalar derivative almost everywhere off-axis.
Paper `e1a0fd5`, `eq:wave-psi`, lines 78–84 and 222. -/
theorem Q1StandingCore.phi_in_ae_hasDerivAt {ui v a b : ℝ} {S : SSFields}
    (h : Q1StandingCore ui S) (hab : a ≤ b) (ha : ui ≤ a) (hb0 : b < 0)
    (hbv : b < v) (hv0 : v ≤ 0) :
    ∀ᵐ x, x ∈ Ioo a b → HasDerivAt (fun u => S.phi u v) (S.duphi x v) x := by
  have hp : ∀ x ∈ Icc a b, (x, v) ∈ pastTriangle ui ∧ x < v := by
    intro x hx
    exact ⟨⟨ha.trans hx.1, hx.2.trans_lt hb0, (hx.2.trans_lt hbv).le, hv0⟩,
      hx.2.trans_lt hbv⟩
  have hr := intervalPrimitive_ae_hasDerivAt hab (fun x hx =>
    h.regularCenter.localBV.radius_in v a x hx.1
      (inSeg_subset_triangle ha (hx.2.trans_lt hb0) (hx.2.trans_lt hbv).le hv0))
  have hψ := intervalPrimitive_ae_hasDerivAt hab (fun x hx =>
    h.regularCenter.localBV.psi_in v a x hx.1
      (inSeg_subset_triangle ha (hx.2.trans_lt hb0) (hx.2.trans_lt hbv).le hv0))
  filter_upwards [hr, hψ] with x hrx hψx
  intro hx
  have hrne := (h.r_pos (hp x ⟨hx.1.le, hx.2.le⟩).1
    (hp x ⟨hx.1.le, hx.2.le⟩).2).ne'
  have hd := (hψx hx).div (hrx hx) hrne
  have he : (S.dupsi x v * S.r x v - (S.r x v * S.phi x v) * S.nu x v) /
      S.r x v ^ 2 = S.duphi x v := by
    unfold SSFields.duphi SSFields.zeta
    field_simp
  rw [he] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds hx.1 hx.2] with y hy
  exact (mul_div_cancel_left₀ (S.phi y v) (h.r_pos (hp y hy).1 (hp y hy).2).ne').symm

/-- Incoming flux is the normalized incoming amplitude times minus the scalar derivative.
Paper `e1a0fd5`, `eq:incoming-flux-identity`, lines 334–339. -/
theorem SSFields.incomingFlux_eq_normalized (S : SSFields) {u v : ℝ}
    (hr : S.r u v ≠ 0) (hn : S.nu u v ≠ 0) :
    S.incomingFlux u v = -(S.dupsi u v / S.nu u v - S.phi u v) * S.duphi u v := by
  unfold SSFields.incomingFlux SSFields.duphi SSFields.zeta
  field_simp

/-- Scalar variation controls log κ transport on each off-axis incoming segment. The normalized
axis trace supplies B; the core uniform scalar BV bound supplies the variation factor.
Paper `e1a0fd5`, `eq:raychaudhuri`, `eq:regular-axis-scalar-traces`, lines 220–275, 334–339. -/
theorem Q1StandingCore.log_kappa_sub_le_variation {ui v a b B : ℝ} {S : SSFields}
    (h : Q1StandingCore ui S) (hab : a ≤ b) (ha : ui ≤ a) (hb0 : b < 0)
    (hbv : b < v) (hv0 : v ≤ 0) (hB : 0 ≤ B)
    (hamp : ∀ u ∈ Ioo a b, |S.dupsi u v / S.nu u v - S.phi u v| ≤ B) :
    |Real.log (S.kappa b v) - Real.log (S.kappa a v)| ≤
      B * (eVariationOn (fun u => S.phi u v) (Icc a b)).toReal := by
  have hs := inSeg_subset_triangle ha hb0 hbv.le hv0
  obtain ⟨C, _, hC⟩ := h.regularCenter.localBV.scalar_ac_variation (inSeg v a b)
    (isCompact_Icc.prod isCompact_singleton) hs
  have hbvar : BoundedVariationOn (fun u => S.phi u v) (Icc a b) :=
    ne_of_lt (lt_of_le_of_lt (hC v a b hab Subset.rfl).2 ENNReal.ofReal_lt_top)
  have hiD : IntervalIntegrable (deriv (fun u => S.phi u v)) volume a b :=
    (show BoundedVariationOn (fun u => S.phi u v) (uIcc a b) by
      simpa only [uIcc_of_le hab] using hbvar).intervalIntegrable_deriv
  have hlog := h.log_kappa_primitive hab ha hb0 hbv hv0
  have hd := h.phi_in_ae_hasDerivAt hab ha hb0 hbv hv0
  rw [hlog.2]
  calc
    _ ≤ ∫ u in a..b, |-S.incomingFlux u v| := by
      simpa only [Real.norm_eq_abs] using
        intervalIntegral.norm_integral_le_integral_norm (f := fun u => -S.incomingFlux u v) hab
    _ ≤ ∫ u in a..b, B * |deriv (fun x => S.phi x v) u| := by
      apply intervalIntegral.integral_mono_ae_restrict hab hlog.1.abs (hiD.abs.const_mul B)
      rw [Filter.EventuallyLE, ← restrict_Ioo_eq_restrict_Icc,
        ae_restrict_iff' measurableSet_Ioo]
      filter_upwards [hd] with u hu huI
      have hp : (u, v) ∈ pastTriangle ui :=
        ⟨ha.trans huI.1.le, huI.2.trans hb0, (huI.2.trans hbv).le, hv0⟩
      rw [S.incomingFlux_eq_normalized (h.r_pos hp (huI.2.trans hbv)).ne'
        (h.nu_neg hp).ne, abs_neg, abs_mul, abs_neg, (hu huI).deriv]
      exact mul_le_mul_of_nonneg_right (hamp u huI) (abs_nonneg _)
    _ = B * ∫ u in a..b, |deriv (fun x => S.phi x v) u| :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (integral_abs_deriv_le_variation hab hbvar) hB

end AcExtensionPrinciple

end
