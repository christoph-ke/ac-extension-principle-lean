module

public import AcExtensionPrinciple.Redundancy.AxisMassRatio
public import AcExtensionPrinciple.Solution.Raychaudhuri
public import AcExtensionPrinciple.BoundaryEnergy.Stability

/-!
# Incoming Raychaudhuri transport without the Q1 additions
Paper commit `e1a0fd5`, `eq:raychaudhuri`, `eq:incoming-flux-identity`,
`equations.tex` lines 90–92, 220–275 and 334–339.
Characteristic primitives suffice for these off-axis identities.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

variable {ui : ℝ} {S : SSFields} (h : Q1StandingCore ui S)
include h

/-- κ is positive, including on the axis. Paper `e1a0fd5`, `eq:normalized-expansions`. -/
theorem Q1StandingCore.kappa_pos {p : ℝ × ℝ} (hp : p ∈ pastTriangle ui) : 0 < S.kappa p.1 p.2 := by
  exact div_pos (h.lam_pos hp) (sub_pos.mpr (h.mu_bounds hp).2)

/-- κ is AC on every compact off-axis incoming segment.
Paper `e1a0fd5`, lines 222 and 318–328. -/
theorem Q1StandingCore.kappa_ac_in {v a b : ℝ} (hab : a ≤ b) (ha : ui ≤ a) (hb0 : b < 0)
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
  exact (intervalPrimitive_ac hab (fun x hx =>
      h.regularCenter.localBV.lam_in v a x hx.1
        (inSeg_subset_offAxis ha (hx.2.trans_lt hb0) (hx.2.trans_lt hbv) hv0))).fun_mul hgap

/-- The incoming logarithmic Raychaudhuri identity in interval primitive form.
Paper `e1a0fd5`, `eq:raychaudhuri`, `eq:incoming-flux-identity`. -/
theorem Q1StandingCore.log_kappa_primitive {v a b : ℝ} (hab : a ≤ b) (ha : ui ≤ a) (hb0 : b < 0)
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

end AcExtensionPrinciple

end
