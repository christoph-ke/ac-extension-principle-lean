module

public import AcExtensionPrinciple.GeometricBounds.Blueshift

/-!
# Incoming logarithmic calculus without the blueshift hypothesis
Paper `e1a0fd5`, `eq:radius`, `eq:logarithmic-expansions`, `eq:uniform-blueshift`.
Only regular-center local AC/BV regularity and the stated signs are used.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- Local expansion bounds make λ positive also at the axis.
Paper `e1a0fd5`, lines 222–243, Luk–Oh Definition 2.1(1). -/
theorem blueshift_lam_pos {ui : ℝ} {S : SSFields} (h : RegularCenterFull ui S)
    {p : ℝ × ℝ} (hp : p ∈ pastTriangle ui) : 0 < S.lam p.1 p.2 := by
  obtain ⟨c, hc, hb⟩ := h.localBV.expansion_bounds {p} isCompact_singleton
    (singleton_subset_iff.mpr hp)
  exact hc.trans_le (hb p (mem_singleton p)).1

/-- Radius is positive away from the axis using only the local class.
Paper `e1a0fd5`, `eq:radius-from-axis`, line 66. -/
theorem blueshift_r_pos {ui u v : ℝ} {S : SSFields} (h : RegularCenterFull ui S)
    (hp : (u, v) ∈ pastTriangle ui) (huv : u < v) : 0 < S.r u v := by
  have hs := outSeg_subset_triangle hp.1 hp.2.1 le_rfl hp.2.2.2
  obtain ⟨c, hc, hb⟩ := h.localBV.expansion_bounds (outSeg u u v)
    (isCompact_singleton.prod isCompact_Icc) hs
  have hi := h.localBV.radius_out u u v huv.le hs
  have he : S.r u v = ∫ s in u..v, S.lam u s := by
    simpa [(h.localBV.axis_values u ⟨hp.1, hp.2.1, le_rfl, hp.2.1.le⟩).1] using hi.2
  have hl : c * (v - u) ≤ S.r u v := by
    rw [he]
    calc
      _ = ∫ s in u..v, c := by simp [mul_comm]
      _ ≤ _ := intervalIntegral.integral_mono_on huv.le intervalIntegrable_const hi.1
        (fun s hs' => (hb (u, s) ⟨mem_singleton u, hs'⟩).1)
  exact (mul_pos hc (sub_pos.mpr huv)).trans_le hl

/-- The density is nonnegative without any integral bound.
Paper `e1a0fd5`, `eq:uniform-blueshift`, `eq:normalized-expansions`, `eq:varkappa`. -/
theorem blueshift_density_nonneg {ui : ℝ} {S : SSFields} (h : RegularCenterFull ui S)
    (signs : ∀ p ∈ pastTriangle ui, p.1 < p.2 →
      0 < S.lam p.1 p.2 ∧ S.nu p.1 p.2 < 0 ∧ 0 ≤ S.mu p.1 p.2 ∧ S.mu p.1 p.2 < 1)
    {u v : ℝ} (hp : (u, v) ∈ pastTriangle ui) (huv : u < v) :
    0 ≤ -(S.gamma u v * S.varkappa u v) := by
  have hs := signs (u, v) hp huv
  unfold SSFields.gamma gammaOf SSFields.varkappa varkappaOf
  exact neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg
    (div_nonpos_of_nonpos_of_nonneg hs.2.1.le (sub_pos.mpr hs.2.2.2).le)
    (div_nonneg hs.2.2.1 (blueshift_r_pos h hp huv).le))

/-- Log λ satisfies its incoming primitive identity using only regular-center regularity.
Paper `e1a0fd5`, `eq:radius`, `eq:logarithmic-expansions`, lines 87–89, 222. -/
theorem blueshift_log_lam_primitive {ui v a b : ℝ} {S : SSFields}
    (h : RegularCenterFull ui S) (hab : a ≤ b) (ha : ui ≤ a) (hb0 : b < 0)
    (hbv : b < v) (hv0 : v ≤ 0) :
    IntervalPrimitive (fun u => Real.log (S.lam u v))
      (fun u => S.gamma u v * S.varkappa u v) a b := by
  have hp := fun x (hx : x ∈ Icc a b) => h.localBV.lam_in v a x hx.1
    (inSeg_subset_offAxis ha (hx.2.trans_lt hb0) (hx.2.trans_lt hbv) hv0)
  have hac := intervalPrimitive_ac hab hp
  apply ac_integral_eq_sub hab (positive_ac_log hac ?_)
  · have hd := intervalPrimitive_ae_hasDerivAt hab hp
    filter_upwards [hd] with x hx
    intro hxI
    exact IncomingRay.log_lam (r := fun s => S.r s v) (m := fun s => S.m s v)
      (nu := fun s => S.nu s v)
      ((hx hxI).congr_deriv (S.radiusCoeff_eq x v))
      (blueshift_lam_pos h (p := (x, v))
        ⟨ha.trans hxI.1.le, hxI.2.trans hb0, (hxI.2.trans hbv).le, hv0⟩)
  · intro x hx
    rw [uIcc_of_le hab] at hx
    exact blueshift_lam_pos h (p := (x, v))
      ⟨ha.trans hx.1, hx.2.trans_lt hb0, (hx.2.trans_lt hbv).le, hv0⟩

/-- The truncated lower integral equals the negative log expansion in the initial gauge.
Paper `e1a0fd5`, `eq:lambda-integrating-factor`, `eq:initial-radius-gauge`. -/
theorem blueshift_partial_identity {ui v b : ℝ} {S : SSFields}
    (h : RegularCenterFull ui S)
    (signs : ∀ p ∈ pastTriangle ui, p.1 < p.2 →
      0 < S.lam p.1 p.2 ∧ S.nu p.1 p.2 < 0 ∧ 0 ≤ S.mu p.1 p.2 ∧ S.mu p.1 p.2 < 1)
    (gauge : ∀ v ∈ Icc ui 0, S.r ui v = v - ui ∧ S.lam ui v = 1)
    (hv : v ∈ Ioo ui 0) (hb : ui ≤ b) (hbv : b < v) :
    (∫⁻ u in Ioo ui b, ENNReal.ofReal (-(S.gamma u v * S.varkappa u v))) =
      ENNReal.ofReal (-Real.log (S.lam b v)) := by
  have hp := blueshift_log_lam_primitive h hb le_rfl (hbv.trans hv.2) hbv hv.2.le
  have he : (∫ u in ui..b, -(S.gamma u v * S.varkappa u v)) =
      -Real.log (S.lam b v) := by
    have ht := hp.2
    dsimp only at ht
    rw [(gauge v ⟨hv.1.le, hv.2.le⟩).2, Real.log_one, sub_zero] at ht
    rw [intervalIntegral.integral_neg, ← ht]
  have hr := ofReal_intervalIntegral (f := fun u => -(S.gamma u v * S.varkappa u v))
    hb hp.1.neg (fun u hu =>
    blueshift_density_nonneg h signs
      ⟨hu.1.le, hu.2.trans (hbv.trans hv.2), (hu.2.trans hbv).le, hv.2.le⟩
      (hu.2.trans hbv))
  exact hr.symm.trans (congrArg ENNReal.ofReal he)

end AcExtensionPrinciple

end
