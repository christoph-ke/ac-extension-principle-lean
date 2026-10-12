module

public import AcExtensionPrinciple.GeometricBounds.RayBounds

/-!
# Incoming Raychaudhuri equation from the integral solution class

Paper `e1a0fd5`, `eq:raychaudhuri`,
`eq:incoming-flux-identity` (lines 90–92 and 334–339). No positivity of a
uniform initial-gap constant is assumed here.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory

/-- Incoming scalar flux density. Paper `e1a0fd5`, `eq:incoming-flux-bound`. -/
@[expose] noncomputable def SSFields.incomingFlux (S : SSFields) (u v : ℝ) : ℝ :=
  S.r u v / (-S.nu u v) * S.duphi u v ^ 2

/-- Mass integrands in the integral class match the reduced incoming ray equation.
Paper `e1a0fd5`, `eq:mass`, lines 74–77. -/
theorem SSFields.massU_eq (S : SSFields) {u v : ℝ} (hr : S.r u v ≠ 0)
    (hn : S.nu u v ≠ 0) (hgap : 1 - S.mu u v ≠ 0) :
    S.massU u v = S.r u v ^ 2 / (2 * S.gamma u v) * S.duphi u v ^ 2 := by
  unfold SSFields.massU SSFields.gamma gammaOf SSFields.duphi
  field_simp

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- κ is positive, including on the axis. Paper `e1a0fd5`, `eq:normalized-expansions`. -/
theorem kappa_pos {p : ℝ × ℝ} (hp : p ∈ pastTriangle ui) : 0 < S.kappa p.1 p.2 := by
  exact div_pos (h.lam_pos hp) (sub_pos.mpr (h.mu_bounds hp).2)

/-- κ is AC on every compact off-axis incoming segment.
Paper `e1a0fd5`, lines 222 and 318–328. -/
theorem kappa_ac_in {v a b : ℝ} (hab : a ≤ b) (ha : ui ≤ a) (hb0 : b < 0)
    (hbv : b < v) (hv0 : v ≤ 0) :
    AbsolutelyContinuousOnInterval (fun u => S.kappa u v) a b := by
  have hr := intervalPrimitive_ac (g := fun u => S.nu u v) hab
    (fun x hx => h.regularCenter.localBV.radius_in v a x hx.1
      (inSeg_subset_triangle ha (hx.2.trans_lt hb0) (hx.2.trans_lt hbv).le hv0))
  have hm := intervalPrimitive_ac (g := fun u => S.massU u v) hab
    (fun x hx => h.regularCenter.localBV.mass_in v a x hx.1
      (inSeg_subset_triangle ha (hx.2.trans_lt hb0) (hx.2.trans_lt hbv).le hv0))
  have hp : ∀ x ∈ uIcc a b, (x, v) ∈ pastTriangle ui ∧ x < v := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    exact ⟨⟨ha.trans hx.1, hx.2.trans_lt hb0, (hx.2.trans_lt hbv).le, hv0⟩,
      hx.2.trans_lt hbv⟩
  have hri := positive_ac_inv hr (fun x hx => h.r_pos (hp x hx).1 (hp x hx).2)
  have hmu : AbsolutelyContinuousOnInterval (fun u => S.mu u v) a b :=
    (hm.const_mul 2).fun_mul hri
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1 : ℝ)) a b :=
    (LipschitzWith.const 1).lipschitzOnWith.absolutelyContinuousOnInterval
  have hgap := positive_ac_inv (hconst.fun_sub hmu)
    (fun x hx => sub_pos.mpr (h.mu_bounds (hp x hx).1).2)
  exact (h.lam_ac_in hab ha hb0 hbv hv0).fun_mul hgap

/-- The incoming logarithmic Raychaudhuri identity in interval primitive form.
Paper `e1a0fd5`, `eq:raychaudhuri`, `eq:incoming-flux-identity`. -/
theorem log_kappa_primitive {v a b : ℝ} (hab : a ≤ b) (ha : ui ≤ a) (hb0 : b < 0)
    (hbv : b < v) (hv0 : v ≤ 0) :
    IntervalPrimitive (fun u => Real.log (S.kappa u v))
      (fun u => -S.incomingFlux u v) a b := by
  have hp : ∀ x ∈ Icc a b, (x, v) ∈ pastTriangle ui ∧ x < v := by
    intro x hx
    exact ⟨⟨ha.trans hx.1, hx.2.trans_lt hb0, (hx.2.trans_lt hbv).le, hv0⟩,
      hx.2.trans_lt hbv⟩
  have hac := positive_ac_log (h.kappa_ac_in hab ha hb0 hbv hv0)
    (fun x hx => h.kappa_pos (hp x (by simpa [uIcc_of_le hab] using hx)).1)
  apply ac_integral_eq_sub hab hac
  have hr := intervalPrimitive_ae_hasDerivAt (g := fun u => S.nu u v) hab
    (fun x hx => h.regularCenter.localBV.radius_in v a x hx.1
      (inSeg_subset_triangle ha (hx.2.trans_lt hb0) (hx.2.trans_lt hbv).le hv0))
  have hm := intervalPrimitive_ae_hasDerivAt (g := fun u => S.massU u v) hab
    (fun x hx => h.regularCenter.localBV.mass_in v a x hx.1
      (inSeg_subset_triangle ha (hx.2.trans_lt hb0) (hx.2.trans_lt hbv).le hv0))
  have hl := intervalPrimitive_ae_hasDerivAt (g := fun u => S.radiusCoeff u v) hab
    (fun x hx => h.regularCenter.localBV.lam_in v a x hx.1
      (inSeg_subset_offAxis ha (hx.2.trans_lt hb0) (hx.2.trans_lt hbv) hv0))
  filter_upwards [hr, hm, hl] with x hrx hmx hlx
  intro hx
  have hxp := (hp x ⟨hx.1.le, hx.2.le⟩).1
  have hxv := (hp x ⟨hx.1.le, hx.2.le⟩).2
  have hr0 := h.r_pos hxp hxv
  have hn0 := h.nu_neg hxp
  have hmu := (h.mu_bounds hxp).2
  have hd := IncomingRay.log_kappa (r := fun u => S.r u v) (m := fun u => S.m u v)
    (nu := fun u => S.nu u v) (phiU := fun u => S.duphi u v)
    (hrx hx) ((hlx hx).congr_deriv (S.radiusCoeff_eq x v))
    ((hmx hx).congr_deriv (S.massU_eq (ne_of_gt hr0) (ne_of_lt hn0)
      (ne_of_gt (sub_pos.mpr hmu)))) hr0 (h.lam_pos hxp) hn0 hmu
  convert hd using 1
  · rfl
  · unfold SSFields.incomingFlux
    ring

/-- Exact flux integral on a regular incoming segment.
Paper `e1a0fd5`, `eq:incoming-flux-identity`, lines 334–339. -/
theorem incoming_flux_identity {v a b : ℝ} (hab : a ≤ b) (ha : ui ≤ a) (hb0 : b < 0)
    (hbv : b < v) (hv0 : v ≤ 0) :
    IntervalIntegrable (fun u => S.incomingFlux u v) volume a b ∧
      (∫ u in a..b, S.incomingFlux u v) = Real.log (S.kappa a v) - Real.log (S.kappa b v) := by
  have hl := h.log_kappa_primitive hab ha hb0 hbv hv0
  refine ⟨?_, ?_⟩
  · convert hl.1.neg using 1
    funext u
    exact (neg_neg _).symm
  · have he := hl.2
    dsimp only at he
    rw [intervalIntegral.integral_neg] at he
    linarith

/-- Nonincreasing κ on incoming rays, including the terminal ray away from its endpoint.
Paper `e1a0fd5`, `eq:kappa-monotonicity-bound`, lines 318–328. -/
theorem kappa_le_of_le {v a b : ℝ} (hab : a ≤ b) (ha : ui ≤ a) (hb0 : b < 0)
    (hbv : b < v) (hv0 : v ≤ 0) : S.kappa b v ≤ S.kappa a v := by
  have hf := h.incoming_flux_identity hab ha hb0 hbv hv0
  have hn : 0 ≤ ∫ u in a..b, S.incomingFlux u v := by
    apply intervalIntegral.integral_nonneg hab
    intro u hu
    have hp : (u, v) ∈ pastTriangle ui :=
      ⟨ha.trans hu.1, hu.2.trans_lt hb0, (hu.2.trans_lt hbv).le, hv0⟩
    exact mul_nonneg (div_nonneg (h.r_pos hp (hu.2.trans_lt hbv)).le
      (neg_pos.mpr (h.nu_neg hp)).le) (sq_nonneg _)
  have hlog : Real.log (S.kappa b v) ≤ Real.log (S.kappa a v) := by linarith [hf.2]
  exact (Real.log_le_log_iff (h.kappa_pos (p := (b, v)) ⟨ha.trans hab, hb0, hbv.le, hv0⟩)
    (h.kappa_pos (p := (a, v)) ⟨ha, hab.trans_lt hb0, (hab.trans_lt hbv).le, hv0⟩)).mp hlog

end StandingFull

end AcExtensionPrinciple

end
