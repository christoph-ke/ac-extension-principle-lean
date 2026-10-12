module

public import AcExtensionPrinciple.ScalarBound.Transport

/-!
# Characteristic scalar calculus

Paper commit `e1a0fd5`, `equations.tex`
lines 407–418 and 450–454. All derivative statements are used through
their interval primitives, as required by the solution class.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- Recover the scalar primitive from the radius and rφ primitives away
from the axis. Paper `e1a0fd5`, lines 407 and 450–454. -/
theorem scalar_primitive_of_product {r f dr dpsi : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hr : ∀ x ∈ Icc a b, 0 < r x)
    (hR : ∀ x ∈ Icc a b, IntervalPrimitive r dr a x)
    (hP : ∀ x ∈ Icc a b, IntervalPrimitive (fun s => r s * f s) dpsi a x) :
    IntervalPrimitive f (fun s => (dpsi s - dr s * f s) / r s) a b := by
  have hacR := intervalPrimitive_ac hab hR
  have hacP := intervalPrimitive_ac hab hP
  have hacQ := hacP.fun_mul (positive_ac_inv hacR
    (fun x hx => hr x (by simpa [uIcc_of_le hab] using hx)))
  have hac : AbsolutelyContinuousOnInterval f a b := by
    apply hacQ.congr
    intro x hx
    have hrx := (hr x (by simpa [uIcc_of_le hab] using hx)).ne'
    dsimp only
    field_simp
  apply ac_integral_eq_sub hab hac
  filter_upwards [intervalPrimitive_ae_hasDerivAt hab hR,
    intervalPrimitive_ae_hasDerivAt hab hP] with x hRx hPx
  intro hx
  have hrx := (hr x ⟨hx.1.le, hx.2.le⟩).ne'
  have hd := (hPx hx).div (hRx hx) hrx
  have he : (dpsi x * r x - (r x * f x) * dr x) / r x ^ 2 =
      (dpsi x - dr x * f x) / r x := by field_simp
  apply (hd.congr_deriv he).congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds hx.1 hx.2] with y hy
  change f y = r y * f y / r y
  field_simp [(hr y hy).ne']

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Incoming φ primitive with its explicitly defined derivative field.
Paper `e1a0fd5`, lines 407 and 484–488. -/
theorem scalar_primitive_in {v a b : ℝ} (hab : a ≤ b) (ha : ui ≤ a)
    (hb0 : b < 0) (hbv : b < v) (hv0 : v ≤ 0) :
    IntervalPrimitive (fun u => S.phi u v) (fun u => S.duphi u v) a b := by
  apply scalar_primitive_of_product hab
  · intro x hx
    exact h.r_pos ⟨ha.trans hx.1, hx.2.trans_lt hb0, (hx.2.trans_lt hbv).le, hv0⟩
      (hx.2.trans_lt hbv)
  · intro x hx
    exact h.regularCenter.localBV.radius_in v a x hx.1
      (inSeg_subset_triangle ha (hx.2.trans_lt hb0) (hx.2.trans_lt hbv).le hv0)
  · intro x hx
    exact h.regularCenter.localBV.psi_in v a x hx.1
      (inSeg_subset_triangle ha (hx.2.trans_lt hb0) (hx.2.trans_lt hbv).le hv0)

/-- Outgoing φ primitive away from the axis.
Paper `e1a0fd5`, lines 407 and 450–454. -/
theorem scalar_primitive_out {u a b : ℝ} (hab : a ≤ b) (hu : ui ≤ u)
    (hu0 : u < 0) (hua : u < a) (hb0 : b ≤ 0) :
    IntervalPrimitive (S.phi u) (S.dvphi u) a b := by
  apply scalar_primitive_of_product hab
  · intro x hx
    exact h.r_pos ⟨hu, hu0, (hua.trans_le hx.1).le, hx.2.trans hb0⟩
      (hua.trans_le hx.1)
  · intro x hx
    exact h.regularCenter.localBV.radius_out u a x hx.1
      (outSeg_subset_triangle hu hu0 hua.le (hx.2.trans hb0))
  · intro x hx
    exact h.regularCenter.localBV.psi_out u a x hx.1
      (outSeg_subset_triangle hu hu0 hua.le (hx.2.trans hb0))

/-- Incoming scalar amplitude transport in integral form.
Paper `e1a0fd5`, `eq:scalar-bound-first-derivative-transport`, lines 450–454. -/
theorem theta_primitive_in {v a b : ℝ} (hab : a ≤ b) (ha : ui ≤ a)
    (hb0 : b < 0) (hbv : b < v) (hv0 : v ≤ 0) :
    IntervalPrimitive (fun u => S.theta u v)
      (fun u => -S.lam u v * S.duphi u v) a b := by
  have hL : ∀ x ∈ Icc a b, IntervalPrimitive (fun u => S.lam u v)
      (fun u => S.radiusCoeff u v) a x := fun x hx =>
    h.regularCenter.localBV.lam_in v a x hx.1
      (inSeg_subset_offAxis ha (hx.2.trans_lt hb0) (hx.2.trans_lt hbv) hv0)
  have hD : ∀ x ∈ Icc a b, IntervalPrimitive (fun u => S.dvpsi u v)
      (fun u => S.radiusCoeff u v * S.phi u v) a x := fun x hx =>
    h.regularCenter.localBV.dvpsi_in v a x hx.1
      (inSeg_subset_offAxis ha (hx.2.trans_lt hb0) (hx.2.trans_lt hbv) hv0)
  have hF : ∀ x ∈ Icc a b, IntervalPrimitive (fun u => S.phi u v)
      (fun u => S.duphi u v) a x := fun x hx =>
    h.scalar_primitive_in hx.1 ha (hx.2.trans_lt hb0) (hx.2.trans_lt hbv) hv0
  have hac := (intervalPrimitive_ac hab hD).fun_sub
    ((intervalPrimitive_ac hab hL).fun_mul (intervalPrimitive_ac hab hF))
  apply ac_integral_eq_sub hab hac
  filter_upwards [intervalPrimitive_ae_hasDerivAt hab hD,
    intervalPrimitive_ae_hasDerivAt hab hL,
    intervalPrimitive_ae_hasDerivAt hab hF] with x hDx hLx hFx
  intro hx
  exact ((hDx hx).sub ((hLx hx).mul (hFx hx))).congr_deriv (by ring)

/-- Outgoing incoming-amplitude transport in integral form.
Paper `e1a0fd5`, `eq:scalar-bound-first-derivative-transport`, lines 450–454. -/
theorem zeta_primitive_out {u a b : ℝ} (hab : a ≤ b) (hu : ui ≤ u)
    (hu0 : u < 0) (hua : u < a) (hb0 : b ≤ 0) :
    IntervalPrimitive (S.zeta u) (fun v => -S.nu u v * S.dvphi u v) a b := by
  have hN : ∀ x ∈ Icc a b, IntervalPrimitive (S.nu u) (S.radiusCoeff u) a x :=
    fun x hx => h.regularCenter.localBV.nu_out u a x hx.1
      (outSeg_subset_offAxis hu hu0 hua (hx.2.trans hb0))
  have hD : ∀ x ∈ Icc a b, IntervalPrimitive (S.dupsi u)
      (fun v => S.radiusCoeff u v * S.phi u v) a x := fun x hx =>
    h.regularCenter.localBV.dupsi_out u a x hx.1
      (outSeg_subset_offAxis hu hu0 hua (hx.2.trans hb0))
  have hF : ∀ x ∈ Icc a b, IntervalPrimitive (S.phi u) (S.dvphi u) a x :=
    fun x hx => h.scalar_primitive_out hx.1 hu hu0 hua (hx.2.trans hb0)
  have hac := (intervalPrimitive_ac hab hD).fun_sub
    ((intervalPrimitive_ac hab hN).fun_mul (intervalPrimitive_ac hab hF))
  apply ac_integral_eq_sub hab hac
  filter_upwards [intervalPrimitive_ae_hasDerivAt hab hD,
    intervalPrimitive_ae_hasDerivAt hab hN,
    intervalPrimitive_ae_hasDerivAt hab hF] with x hDx hNx hFx
  intro hx
  exact ((hDx hx).sub ((hNx hx).mul (hFx hx))).congr_deriv (by ring)

/-- The normalized datum satisfies the linear incoming transport equation
in integral form. Paper `e1a0fd5`, `eq:scalar-bound-linear-transport`,
`eq:scalar-bound-normalized-datum`, lines 414–418 and 526–532. -/
theorem normalized_datum_primitive_in {v a b : ℝ} (hab : a ≤ b) (ha : ui ≤ a)
    (hb0 : b < 0) (hbv : b < v) (hv0 : v ≤ 0) :
    IntervalPrimitive (fun u => S.dvpsi u v / S.lam u v)
      (fun u => -(S.gamma u v * S.varkappa u v) * (S.theta u v / S.lam u v)) a b := by
  have hL : ∀ x ∈ Icc a b, IntervalPrimitive (fun u => S.lam u v)
      (fun u => S.radiusCoeff u v) a x := fun x hx =>
    h.regularCenter.localBV.lam_in v a x hx.1
      (inSeg_subset_offAxis ha (hx.2.trans_lt hb0) (hx.2.trans_lt hbv) hv0)
  have hD : ∀ x ∈ Icc a b, IntervalPrimitive (fun u => S.dvpsi u v)
      (fun u => S.radiusCoeff u v * S.phi u v) a x := fun x hx =>
    h.regularCenter.localBV.dvpsi_in v a x hx.1
      (inSeg_subset_offAxis ha (hx.2.trans_lt hb0) (hx.2.trans_lt hbv) hv0)
  have hl : ∀ x ∈ Icc a b, 0 < S.lam x v := fun x hx =>
    h.lam_pos (p := (x, v)) ⟨ha.trans hx.1, hx.2.trans_lt hb0, (hx.2.trans_lt hbv).le, hv0⟩
  have hac := (intervalPrimitive_ac hab hD).fun_mul
    (positive_ac_inv (intervalPrimitive_ac hab hL)
      (fun x hx => hl x (by simpa [uIcc_of_le hab] using hx)))
  apply ac_integral_eq_sub hab (by simpa only [div_eq_mul_inv] using hac)
  filter_upwards [intervalPrimitive_ae_hasDerivAt hab hD,
    intervalPrimitive_ae_hasDerivAt hab hL] with x hDx hLx
  intro hx
  apply ((hDx hx).div (hLx hx) (hl x ⟨hx.1.le, hx.2.le⟩).ne').congr_deriv
  rw [h.radiusCoeff_eq_lam_gamma]
  unfold SSFields.theta
  field_simp
  ring

end StandingFull

end AcExtensionPrinciple

end
