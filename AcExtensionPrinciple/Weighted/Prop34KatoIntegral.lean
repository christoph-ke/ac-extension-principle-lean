module

public import AcExtensionPrinciple.Weighted.Prop34Kato

/-!
# Integrated Kato on proper incoming segments

Paper `e1a0fd5`, `eq:remainder-difference-kato`, lines 1305–1316.
The future boundary flux is discarded by positivity. The source in this
lemma is the full source F; no radial cutoff of the source is introduced.
-/

public section

namespace AcExtensionPrinciple.StandingFull

open Set Filter MeasureTheory

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Integrating the actual Kato inequality gives the incoming L¹ estimate
with constants uniform in the future endpoint. For the remainder difference,
J(a)=0 and F is the full radial operator T J, including below-cutoff radii.
Paper `e1a0fd5`, `eq:remainder-difference-kato`, lines 1305–1316. -/
theorem frozen_ray_kato_integral_bound {a b v δ ε : ℝ} {J F : ℝ → ℝ}
    (hab : a ≤ b) (ha : ui ≤ a) (hb : b < 0) (hbv : b < v) (hv : v ≤ 0)
    (hδ : δ < 1 / 3) (hsmall : WeightedLateSmallness ui S a δ ε)
    (hJ : AbsolutelyContinuousOnInterval J a b)
    (hJode : ∀ᵐ x, x ∈ Ioo a b → HasDerivAt J
      (S.incomingFlux x v * J x + 3 * S.nu x v * S.dvphi x v * F x) x)
    (hF : IntervalIntegrable F volume a b) :
    (∫ x in a..b, weightedRemainderDensity S (x, v) * |J x|) ≤
      (S.r a v * |J a| / ((1 - S.mu a v) ^ 2 * S.lam a v) +
        3 * ε * ∫ x in a..b, (-S.nu x v) / (1 - S.mu x v) ^ 2 * |F x|) /
          (1 - 3 * δ) := by
  let c := 1 - 3 * δ
  have hc : 0 < c := by dsimp only [c]; linarith
  let w := fun x => S.r x v / ((1 - S.mu x v) ^ 2 * S.lam x v)
  let q := fun x => weightedRemainderDensity S (x, v) * |J x|
  let t := fun x => (-S.nu x v) / (1 - S.mu x v) ^ 2
  let E := fun x => S.r x v * |J x| / ((1 - S.mu x v) ^ 2 * S.lam x v)
  let g := fun x => 3 * ε * (t x * |F x|)
  have hp (x : ℝ) (hx : x ∈ Icc a b) : (x, v) ∈ pastTriangle ui :=
    ⟨ha.trans hx.1, hx.2.trans_lt hb, (hx.2.trans_lt hbv).le, hv⟩
  have hAbs : AbsolutelyContinuousOnInterval (fun x => |J x|) a b := by
    have hLip : LipschitzWith 1 (norm : ℝ → ℝ) := lipschitzWith_one_norm
    simpa only [Real.norm_eq_abs, Function.comp_def] using
      hLip.comp_absolutelyContinuousOnInterval hJ
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1 : ℝ)) a b :=
    (LipschitzWith.const 1).lipschitzOnWith.absolutelyContinuousOnInterval
  have hw : AbsolutelyContinuousOnInterval w a b := by
    simpa only [one_pow, mul_one] using h.frozen_ray_energy_ac hab ha hb hbv hv hconst
  have hE : AbsolutelyContinuousOnInterval E a b := by
    convert hw.fun_mul hAbs using 1
    funext x
    dsimp only [E, w]
    ring
  obtain ⟨hr, hl, hm, _⟩ := h.incoming_components_ac hab ha hb hbv hv
  have hrc : ContinuousOn (fun x => S.r x v) (Icc a b) := by
    simpa only [uIcc_of_le hab] using hr.continuousOn
  have hmc : ContinuousOn (fun x => S.m x v) (Icc a b) := by
    simpa only [uIcc_of_le hab] using hm.continuousOn
  have hlc : ContinuousOn (fun x => S.lam x v) (Icc a b) := by
    simpa only [uIcc_of_le hab] using hl.continuousOn
  have hn := continuous_in h.regularCenter.continuous_nu
    (inSeg_subset_triangle ha hb hbv.le hv)
  have hmu : ContinuousOn (fun x => S.mu x v) (Icc a b) :=
    (hmc.const_mul 2).div hrc
      (fun x hx => (h.r_pos (hp x hx) (hx.2.trans_lt hbv)).ne')
  have ht : ContinuousOn t (Icc a b) :=
    hn.neg.div ((continuousOn_const.sub hmu).pow 2)
      (fun x hx => (sq_pos_of_pos (sub_pos.mpr (h.mu_bounds (hp x hx)).2)).ne')
  have hN : ContinuousOn (fun x => weightedRemainderDensity S (x, v)) (Icc a b) := by
    apply (ht.div hlc (fun x hx => (h.lam_pos (hp x hx)).ne')).congr
    intro x _
    simp only [Pi.div_apply, t, weightedRemainderDensity, div_div]
  have hqc : ContinuousOn q (Icc a b) :=
    hN.mul (by simpa only [uIcc_of_le hab] using hAbs.continuousOn)
  have hq : IntervalIntegrable q volume a b := hqc.intervalIntegrable_of_Icc hab
  have hg : IntervalIntegrable g volume a b :=
    (hF.abs.continuousOn_mul (by simpa only [← uIcc_of_le hab] using ht)).const_mul _
  have hderiv : ∀ᵐ x ∂volume.restrict (Ioc a b), deriv E x + c * q x ≤ g x := by
    have hk := h.frozen_ray_kato_ae hab ha hb hbv hv hJ hJode
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hk, volume.ae_ne b] with x hx hxb hxI
    have hxO : x ∈ Ioo a b := ⟨hxI.1, lt_of_le_of_ne hxI.2 hxb⟩
    have hpx := hp x ⟨hxI.1.le, hxI.2⟩
    have hlate := hsmall (x, v) hpx hxI.1.le
    have hA : |S.r x v / S.lam x v * S.dvphi x v| ≤ ε :=
      (le_add_of_nonneg_right (abs_nonneg (weightedIncomingAmplitude S x v))).trans hlate.2
    have hco : c ≤ 1 + (S.r x v / S.nu x v * S.duphi x v) ^ 2 -
        3 * S.mu x v / (1 - S.mu x v) := by
      calc
        c ≤ 1 - 3 * (S.mu x v / (1 - S.mu x v)) := by
          dsimp only [c]
          linarith [hlate.1]
        _ = 1 - 3 * S.mu x v / (1 - S.mu x v) := by ring
        _ ≤ _ := by nlinarith [sq_nonneg (S.r x v / S.nu x v * S.duphi x v)]
    have hq0 : 0 ≤ q x := mul_nonneg
      (div_nonneg (neg_pos.mpr (h.nu_neg hpx)).le
        (mul_nonneg (sq_nonneg _) (h.lam_pos hpx).le)) (abs_nonneg _)
    calc
      deriv E x + c * q x ≤ deriv E x +
          (1 + (S.r x v / S.nu x v * S.duphi x v) ^ 2 -
            3 * S.mu x v / (1 - S.mu x v)) * q x :=
        by simpa only [add_comm] using
          add_le_add_left (mul_le_mul_of_nonneg_right hco hq0) (deriv E x)
      _ ≤ (3 * (-S.nu x v) / (1 - S.mu x v) ^ 2) *
          |S.r x v / S.lam x v * S.dvphi x v| * |F x| := by
        convert hx hxO using 1
        dsimp only [E, q]
        ring
      _ ≤ g x := by
        have ht0 : 0 ≤ 3 * t x * |F x| := mul_nonneg
          (mul_nonneg (by norm_num) (div_nonneg (neg_pos.mpr (h.nu_neg hpx)).le
            (sq_nonneg _))) (abs_nonneg _)
        convert mul_le_mul_of_nonneg_left hA ht0 using 1 <;> dsimp only [t, g] <;> ring
  have hbE : 0 ≤ E b := div_nonneg
    (mul_nonneg (h.r_pos (hp b ⟨hab, le_rfl⟩) hbv).le (abs_nonneg _))
    (mul_nonneg (sq_nonneg _) (h.lam_pos (hp b ⟨hab, le_rfl⟩)).le)
  have hres := ac_coercive_energy_bound hab hc hE hq hg hderiv hbE
  simpa only [E, q, g, t, intervalIntegral.integral_const_mul, c] using hres

end AcExtensionPrinciple.StandingFull

end
