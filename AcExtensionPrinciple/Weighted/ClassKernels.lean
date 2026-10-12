module

public import AcExtensionPrinciple.Weighted.ClassComparison
public import AcExtensionPrinciple.Weighted.Kernels
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Radial tail kernels in the solution coordinates

Paper `e1a0fd5`, `equations.tex` lines 1192–1195 and
1217–1223. The characteristic primitive supplies the change of radius;
the proof does not assume a differentiable solution.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory Filter
open scoped ENNReal

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- A radial power primitive in outgoing coordinates. Paper `e1a0fd5`,
`lem:weighted-radial-estimates`, lines 1192–1195, 1223. -/
theorem weighted_radius_power_primitive {u a b q : ℝ} (hu : ui ≤ u) (hu0 : u < 0)
    (hua : u < a) (hab : a ≤ b) (hb0 : b ≤ 0) (hq : q ≠ 0) :
    IntervalPrimitive (fun v => S.r u v ^ q / q)
      (fun v => S.lam u v * S.r u v ^ (q - 1)) a b := by
  have hp (x : ℝ) (hx : x ∈ Icc a b) : (u, x) ∈ pastTriangle ui :=
    ⟨hu, hu0, (hua.trans_le hx.1).le, hx.2.trans hb0⟩
  have hac := positive_ac_comp (h.weighted_radius_ac_out hu hu0 hua.le hab hb0)
    (fun x hx => h.r_pos (hp x (by simpa [uIcc_of_le hab] using hx))
      (hua.trans_le (by simpa [uIcc_of_le hab] using hx : x ∈ Icc a b).1))
    (contDiffOn_id.rpow_const_of_ne (p := q) (fun _ hx => ne_of_gt hx))
  have hac' : AbsolutelyContinuousOnInterval (fun v => S.r u v ^ q / q) a b := by
    simpa [div_eq_mul_inv, mul_comm] using hac.const_mul q⁻¹
  apply ac_integral_eq_sub hab hac'
  have hd := intervalPrimitive_ae_hasDerivAt hab (f := S.r u) (g := S.lam u)
    (fun x hx => h.regularCenter.localBV.radius_out u a x hx.1
      (outSeg_subset_triangle hu hu0 hua.le (hx.2.trans hb0)))
  filter_upwards [hd] with x hx
  intro hxI
  have hr := h.r_pos (hp x ⟨hxI.1.le, hxI.2.le⟩) (hua.trans hxI.1)
  convert ((hx hxI).rpow_const (Or.inl hr.ne')).div_const q using 1
  field_simp

/-- The weighted power tail after changing radius, in the original cone
coordinates. Paper `e1a0fd5`, lines 1192–1195, 1223. -/
theorem weighted_outgoing_power_kernel_le {u a b δ p : ℝ}
    (hu : ui ≤ u) (hu0 : u < 0) (hua : u < a) (hab : a ≤ b) (hb0 : b ≤ 0)
    (hp : δ + 1 < p)
    (hsmall : ∀ v ∈ Icc a b, S.mu u v / (1 - S.mu u v) ≤ δ) :
    (∫⁻ v in Ioc a b, ENNReal.ofReal
      ((-S.nu u v) * S.lam u v * S.r u v ^ (-p))) ≤
      ENNReal.ofReal ((-S.nu u a) * S.r u a ^ (1 - p) / (p - δ - 1)) := by
  have hpa : (u, a) ∈ pastTriangle ui := ⟨hu, hu0, hua.le, hab.trans hb0⟩
  have hpb : (u, b) ∈ pastTriangle ui := ⟨hu, hu0, (hua.trans_le hab).le, hb0⟩
  have hra := h.r_pos hpa hua
  have hrb := h.r_pos hpb (hua.trans_le hab)
  have hn := neg_pos.mpr (h.nu_neg hpa)
  have hfac : 0 ≤ (-S.nu u a) * S.r u a ^ (-δ) := by positivity
  have hq : δ - p + 1 < 0 := by linarith
  have hi := h.weighted_radius_power_primitive hu hu0 hua hab hb0 (ne_of_lt hq)
  have he : (∫ v in a..b, S.lam u v * S.r u v ^ (δ - p)) =
      S.r u b ^ (δ - p + 1) / (δ - p + 1) -
        S.r u a ^ (δ - p + 1) / (δ - p + 1) := by
    simpa only [show δ - p + 1 - 1 = δ - p by ring] using hi.2.symm
  have hib : IntervalIntegrable (fun v => S.lam u v * S.r u v ^ (δ - p))
      volume a b := by
    simpa only [show δ - p + 1 - 1 = δ - p by ring] using hi.1
  have hpos : ∀ v ∈ Ioc a b, 0 ≤ S.lam u v * S.r u v ^ (δ - p) := by
    intro v hv
    exact mul_nonneg (h.lam_pos (p := (u, v))
      ⟨hu, hu0, (hua.trans hv.1).le, hv.2.trans hb0⟩).le
      (Real.rpow_nonneg (h.r_pos
        ⟨hu, hu0, (hua.trans hv.1).le, hv.2.trans hb0⟩ (hua.trans hv.1)).le _)
  have htail : (∫ v in a..b, S.lam u v * S.r u v ^ (δ - p)) ≤
      S.r u a ^ (δ - p + 1) / (p - δ - 1) := by
    rw [he]
    have hbpow : 0 ≤ S.r u b ^ (δ - p + 1) := Real.rpow_nonneg hrb.le _
    have hden : p - δ - 1 = -(δ - p + 1) := by ring
    rw [hden, div_neg]
    linarith [div_nonpos_of_nonneg_of_nonpos hbpow hq.le]
  calc
    _ ≤ ∫⁻ v in Ioc a b, ENNReal.ofReal ((-S.nu u a) * S.r u a ^ (-δ)) *
        ENNReal.ofReal (S.lam u v * S.r u v ^ (δ - p)) := by
      apply setLIntegral_mono' measurableSet_Ioc
      intro v hv
      have hpv : (u, v) ∈ pastTriangle ui :=
        ⟨hu, hu0, (hua.trans hv.1).le, hv.2.trans hb0⟩
      have hrv := h.r_pos hpv (hua.trans hv.1)
      have hc := (h.late_radial_expansion_comparison_of_smallness hu hu0 hua
        hv.1.le (hv.2.trans hb0) (fun s hs => hsmall s ⟨hs.1, hs.2.trans hv.2⟩)).2
      have hw : -S.nu u v ≤ (-S.nu u a) * (S.r u v / S.r u a) ^ δ :=
        by simpa [mul_comm] using (div_le_iff₀ hn).mp hc
      rw [← ENNReal.ofReal_mul hfac]
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ ((-S.nu u a) * (S.r u v / S.r u a) ^ δ) *
            S.lam u v * S.r u v ^ (-p) := by
          gcongr
          exact (h.lam_pos hpv).le
        _ = _ := by
          rw [Real.div_rpow hrv.le hra.le, Real.rpow_neg hra.le,
            div_eq_mul_inv, show δ - p = δ + -p by ring, Real.rpow_add hrv]
          ring
    _ = ENNReal.ofReal ((-S.nu u a) * S.r u a ^ (-δ) *
        (∫ v in a..b, S.lam u v * S.r u v ^ (δ - p))) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        ← ofReal_integral_eq_lintegral_ofReal
          ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hib)
          (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
              exact hpos v hv), ← ENNReal.ofReal_mul hfac,
        intervalIntegral.integral_of_le hab]
    _ ≤ ENNReal.ofReal ((-S.nu u a) * S.r u a ^ (-δ) *
        (S.r u a ^ (δ - p + 1) / (p - δ - 1))) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left htail hfac)
    _ = _ := by
      congr 1
      rw [← mul_div_assoc, mul_assoc, ← Real.rpow_add hra,
        show -δ + (δ - p + 1) = 1 - p by ring]

/-- The exact transported-datum cone kernel constant is `1/(3-δ)`.
Paper `e1a0fd5`, `lem:weighted-radial-estimates`, lines 1193–1194. -/
theorem weighted_outgoing_transport_kernel_le {u a b δ : ℝ}
    (hu : ui ≤ u) (hu0 : u < 0) (hua : u < a) (hab : a ≤ b) (hb0 : b ≤ 0)
    (hδ : δ < 3)
    (hsmall : ∀ v ∈ Icc a b, S.mu u v / (1 - S.mu u v) ≤ δ) :
    (∫⁻ v in Ioc a b, ENNReal.ofReal
      ((-S.nu u v) * S.lam u v * S.r u a ^ 2 / S.r u v ^ 4)) ≤
      ENNReal.ofReal ((-S.nu u a) / ((3 - δ) * S.r u a)) := by
  have hk := h.weighted_outgoing_power_kernel_le hu hu0 hua hab hb0
    (p := 4) (by linarith) hsmall
  have hr : S.r u a ≠ 0 := (h.r_pos
    ⟨hu, hu0, hua.le, hab.trans hb0⟩ hua).ne'
  have he (v : ℝ) : (-S.nu u v) * S.lam u v * S.r u a ^ 2 / S.r u v ^ 4 =
      S.r u a ^ 2 * ((-S.nu u v) * S.lam u v * S.r u v ^ (-(4 : ℝ))) := by
    simp [div_eq_mul_inv]
    ring
  simp_rw [he, ENNReal.ofReal_mul (sq_nonneg _)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine (mul_le_mul le_rfl hk zero_le zero_le).trans_eq ?_
  rw [← ENNReal.ofReal_mul (sq_nonneg _)]
  congr 1
  norm_num [Real.rpow_neg, div_eq_mul_inv]
  field_simp
  ring

end StandingFull

end AcExtensionPrinciple

end
