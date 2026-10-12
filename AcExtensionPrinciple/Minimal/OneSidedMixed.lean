module

public import AcExtensionPrinciple.Minimal.OneSidedAxisControl

/-!
# Scalar control across the characteristics through an axis point

Paper `e1a0fd5`, `equations.tex` lines 70–83, 220–261,
`eq:radius`, `eq:wave-psi`, `eq:regular-axis-scalar-traces`.
The mixed rectangle u < a < v is controlled by the retained ν continuity
and the radius and scalar primitive equations.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- The radius transport coefficient is nonpositive in the untrapped triangle.
Paper `e1a0fd5`, lines 66–72, `eq:radius`. -/
theorem StandingAssumptions.oneSided_radiusCoeff_nonpos {ui : ℝ} {S : SSFields}
    (h : StandingAssumptions ui S) {p : ℝ × ℝ} (hp : p ∈ pastTriangle ui)
    (huv : p.1 < p.2) : S.radiusCoeff p.1 p.2 ≤ 0 := by
  unfold SSFields.radiusCoeff
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (h.mu_bounds hp).1 (h.lam_pos hp).le) (h.nu_neg hp).le)
    (mul_nonneg (sub_pos.mpr (h.mu_bounds hp).2).le (h.r_pos hp huv).le)

/-- A small transverse change of ν controls the mixed primitive error.
The amplitude and ν-change premises are discharged by the compact scalar bound
and retained ν continuity near the axis. Paper `e1a0fd5`, lines 70–83, 220–261,
`eq:radius`, `eq:wave-psi`, `eq:regular-axis-scalar-traces`. -/
theorem StandingAssumptions.oneSided_mixed_primitive_bound
    {ui u a v L B η : ℝ} {S : SSFields} (h : StandingAssumptions ui S)
    (hu : ui ≤ u) (hua : u < a) (hav : a < v) (hv : v ≤ 0)
    (hB : 0 ≤ B)
    (hphi : ∀ s ∈ Ioo u a, ∀ t ∈ Icc a v, |S.phi s t - L| ≤ B)
    (hnu : ∀ s ∈ Ioo u a, S.nu s a - S.nu s v ≤ η) :
    |(S.r u v * S.phi u v - L * S.r u v) -
      (S.r u a * S.phi u a - L * S.r u a) -
      (S.r a v * S.phi a v - L * S.r a v)| ≤ B * η * (a - u) := by
  have ha0 := hav.trans_le hv
  let G := fun s => (S.dupsi s v - S.dupsi s a) - L * (S.nu s v - S.nu s a)
  have hG (s : ℝ) (hs : s ∈ Ioo u a) : |G s| ≤ B * η := by
    have hsui := hu.trans hs.1.le
    have hs0 := hs.2.trans ha0
    have hseg := outSeg_subset_offAxis hsui hs0 hs.2 hv
    have hn := h.regularCenter.localBV.nu_out s a v hav.le hseg
    have hd := h.regularCenter.localBV.dupsi_out s a v hav.le hseg
    have _hig : IntervalIntegrable
        (fun t => S.radiusCoeff s t * (S.phi s t - L)) volume a v := by
      simpa only [mul_sub, mul_comm L] using hd.1.sub (hn.1.const_mul L)
    have he : (∫ t in a..v, S.radiusCoeff s t * (S.phi s t - L)) = G s := by
      simp only [mul_sub, mul_comm (S.radiusCoeff s _) L]
      rw [intervalIntegral.integral_sub hd.1 (hn.1.const_mul L),
        intervalIntegral.integral_const_mul, ← hd.2, ← hn.2]
    have hb := intervalIntegral.norm_integral_le_of_norm_le hav.le
      (f := fun t => S.radiusCoeff s t * (S.phi s t - L))
      (g := fun t => -S.radiusCoeff s t * B) (ae_of_all _ (fun t ht => by
        have hp : (s, t) ∈ pastTriangle ui :=
          ⟨hsui, hs0, hs.2.le.trans ht.1.le, ht.2.trans hv⟩
        have hnC := h.oneSided_radiusCoeff_nonpos hp (hs.2.trans ht.1)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonpos hnC]
        exact mul_le_mul_of_nonneg_left (hphi s hs t ⟨ht.1.le, ht.2⟩)
          (neg_nonneg.mpr hnC))) (hn.1.neg.mul_const B)
    rw [he, Real.norm_eq_abs, intervalIntegral.integral_mul_const,
      intervalIntegral.integral_neg, ← hn.2] at hb
    calc
      |G s| ≤ (S.nu s a - S.nu s v) * B := by linarith
      _ ≤ η * B := mul_le_mul_of_nonneg_right (hnu s hs) hB
      _ = _ := mul_comm _ _
  have hnv := h.regularCenter.localBV.radius_in v u a hua.le
    (inSeg_subset_triangle hu ha0 hav.le hv)
  have hna := h.regularCenter.localBV.radius_in a u a hua.le
    (inSeg_subset_triangle hu ha0 le_rfl ha0.le)
  have hdv := h.regularCenter.localBV.psi_in v u a hua.le
    (inSeg_subset_triangle hu ha0 hav.le hv)
  have hda := h.regularCenter.localBV.psi_in a u a hua.le
    (inSeg_subset_triangle hu ha0 le_rfl ha0.le)
  have hnI := (hnv.1.sub hna.1).const_mul L
  have heI : (∫ s in u..a, G s) =
      -((S.r u v * S.phi u v - L * S.r u v) -
        (S.r u a * S.phi u a - L * S.r u a) -
        (S.r a v * S.phi a v - L * S.r a v)) := by
    dsimp only [G]
    rw [intervalIntegral.integral_sub (hdv.1.sub hda.1) hnI,
      intervalIntegral.integral_sub hdv.1 hda.1,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub hnv.1 hna.1,
      ← hdv.2, ← hda.2, ← hnv.2, ← hna.2]
    dsimp only
    rw [(h.regularCenter.localBV.axis_values a ⟨hu.trans hua.le, ha0, le_rfl, ha0.le⟩).1]
    ring
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const_ae
    (f := G) (a := u) (b := a) (C := B * η) (by
      filter_upwards [volume.ae_ne a] with s hsa hs
      rw [uIoc_of_le hua.le] at hs
      simpa only [Real.norm_eq_abs] using hG s ⟨hs.1, lt_of_le_of_ne hs.2 hsa⟩)
  simpa only [heI, Real.norm_eq_abs, abs_neg, abs_of_pos (sub_pos.mpr hua)] using hb

/-- A lower radius bound converts the mixed primitive estimate into scalar
control. All premises come from local bounds and boundary characteristic traces.
Paper `e1a0fd5`, lines 70–83, 220–261, `eq:radius`, `eq:wave-psi`. -/
theorem StandingAssumptions.oneSided_mixed_scalar_bound
    {ui u a v L B η β c : ℝ} {S : SSFields} (h : StandingAssumptions ui S)
    (hu : ui ≤ u) (hua : u < a) (hav : a < v) (hv : v ≤ 0)
    (hB : 0 ≤ B) (hη : 0 ≤ η) (hβ : 0 ≤ β)
    (hlower : c * (v - u) ≤ S.r u v) (hsmall : B * η ≤ β * c)
    (hphi : ∀ s ∈ Ioo u a, ∀ t ∈ Icc a v, |S.phi s t - L| ≤ B)
    (hnu : ∀ s ∈ Ioo u a, S.nu s a - S.nu s v ≤ η)
    (hleft : |S.phi u a - L| ≤ β) (hright : |S.phi a v - L| ≤ β) :
    |S.phi u v - L| ≤ 3 * β := by
  have ha0 := hav.trans_le hv
  have hu0 := hua.trans ha0
  have hp : (u, v) ∈ pastTriangle ui := ⟨hu, hu0, (hua.trans hav).le, hv⟩
  have hr := h.r_pos hp (hua.trans hav)
  have hr1 := h.r_pos (u := u) (v := a) ⟨hu, hu0, hua.le, ha0.le⟩ hua
  have hr2 := h.r_pos (u := a) (v := v) ⟨hu.trans hua.le, ha0, hav.le, hv⟩ hav
  have hle1 : S.r u a ≤ S.r u v := by
    have hi := h.regularCenter.localBV.radius_out u a v hav.le
      (outSeg_subset_triangle hu hu0 hua.le hv)
    have hn : 0 ≤ ∫ t in a..v, S.lam u t := intervalIntegral.integral_nonneg hav.le
      (fun t ht => (h.lam_pos (p := (u, t))
        ⟨hu, hu0, hua.le.trans ht.1, ht.2.trans hv⟩).le)
    linarith [hi.2]
  have hle2 : S.r a v ≤ S.r u v := by
    have hi := h.regularCenter.localBV.radius_in v u a hua.le
      (inSeg_subset_triangle hu ha0 hav.le hv)
    have hn : (∫ s in u..a, S.nu s v) ≤ 0 := by
      simpa only [intervalIntegral.integral_zero] using
        intervalIntegral.integral_mono_on hua.le hi.1 intervalIntegrable_const
          (fun s hs => (h.nu_neg (p := (s, v))
            ⟨hu.trans hs.1, hs.2.trans_lt ha0, hs.2.trans hav.le, hv⟩).le)
    linarith [hi.2]
  have hb := h.oneSided_mixed_primitive_bound hu hua hav hv hB hphi hnu
  have he1 : |S.r u a * S.phi u a - L * S.r u a| ≤ β * S.r u a := by
    rw [show S.r u a * S.phi u a - L * S.r u a = S.r u a * (S.phi u a - L) by ring,
      abs_mul, abs_of_pos hr1]
    nlinarith [mul_le_mul_of_nonneg_left hleft hr1.le]
  have he2 : |S.r a v * S.phi a v - L * S.r a v| ≤ β * S.r a v := by
    rw [show S.r a v * S.phi a v - L * S.r a v = S.r a v * (S.phi a v - L) by ring,
      abs_mul, abs_of_pos hr2]
    nlinarith [mul_le_mul_of_nonneg_left hright hr2.le]
  have hres : B * η * (a - u) ≤ β * S.r u v := calc
    _ ≤ B * η * (v - u) := mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hB hη)
    _ ≤ β * c * (v - u) := mul_le_mul_of_nonneg_right hsmall (by linarith)
    _ ≤ β * S.r u v := by nlinarith [mul_le_mul_of_nonneg_left hlower hβ]
  have he : |S.r u v * S.phi u v - L * S.r u v| ≤ 3 * β * S.r u v := by
    have htri : |S.r u v * S.phi u v - L * S.r u v| ≤
        |(S.r u v * S.phi u v - L * S.r u v) -
          (S.r u a * S.phi u a - L * S.r u a) -
          (S.r a v * S.phi a v - L * S.r a v)| +
        |S.r u a * S.phi u a - L * S.r u a| +
        |S.r a v * S.phi a v - L * S.r a v| := by
      let X := S.r u v * S.phi u v - L * S.r u v
      let Y := S.r u a * S.phi u a - L * S.r u a
      let Z := S.r a v * S.phi a v - L * S.r a v
      change |X| ≤ |X - Y - Z| + |Y| + |Z|
      calc
        |X| = |(X - Y - Z) + Y + Z| := by congr 1; ring
        _ ≤ |(X - Y - Z) + Y| + |Z| := abs_add_le _ _
        _ ≤ (|X - Y - Z| + |Y|) + |Z| := add_le_add (abs_add_le _ _) le_rfl
    nlinarith [mul_le_mul_of_nonneg_left hle1 hβ, mul_le_mul_of_nonneg_left hle2 hβ]
  rw [show S.r u v * S.phi u v - L * S.r u v = S.r u v * (S.phi u v - L) by ring,
    abs_mul, abs_of_pos hr] at he
  nlinarith

end AcExtensionPrinciple

end
