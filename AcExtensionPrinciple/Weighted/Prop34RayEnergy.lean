module

public import AcExtensionPrinciple.Weighted.Prop34Energy
public import AcExtensionPrinciple.Weighted.Prop34Source
public import AcExtensionPrinciple.Weighted.Lemma33Remainder

/-!
# Integrated frozen energy on a proper incoming ray

Paper `e1a0fd5`, `eq:frozen-solution-operators`, lines 1265–1276.
The boundary energy is nonnegative. The coercive coefficient and Young
constants are explicit and independent of the incoming endpoint.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory

/-- The source Young bound gives half the coercivity to the remainder.
Paper `e1a0fd5`, lines 1248–1254 and 1265–1268. -/
theorem frozen_coercive_differential_bound {t lam A F J c coeff d ε : ℝ}
    (ht : 0 ≤ t) (hl : 0 < lam) (hc : 0 < c) (hcoeff : c ≤ coeff)
    (hA : |A| ≤ ε)
    (hd : d = -(t / lam) * coeff * J ^ 2 - t * (6 * A * F * J)) :
    d + c / 2 * (t / lam * J ^ 2) ≤
      (18 * ε ^ 2 / c) * (t * lam * F ^ 2) := by
  have hY := mul_le_mul_of_nonneg_left (frozen_source_young_bound (F := F) (J := J) hc hl hA) ht
  have hS : -t * (6 * A * F * J) ≤ t * |6 * A * F * J| := by
    simpa only [mul_neg, neg_mul] using mul_le_mul_of_nonneg_left (neg_le_abs _) ht
  have hC := mul_le_mul_of_nonneg_left hcoeff
    (mul_nonneg (div_nonneg ht hl.le) (sq_nonneg J))
  have he : t * (c / (2 * lam) * J ^ 2 + 18 * ε ^ 2 * lam / c * F ^ 2) =
      c / 2 * (t / lam * J ^ 2) + (18 * ε ^ 2 / c) * (t * lam * F ^ 2) := by ring
  rw [he] at hY
  rw [hd]
  nlinarith

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- AC of an arbitrary frozen solution's energy from incoming AC and the
class geometry. Paper `e1a0fd5`, lines 1240–1248 and 1268–1276. -/
theorem frozen_ray_energy_ac {a b v : ℝ} {J : ℝ → ℝ}
    (hab : a ≤ b) (ha : ui ≤ a) (hb : b < 0) (hbv : b < v) (hv : v ≤ 0)
    (hJ : AbsolutelyContinuousOnInterval J a b) :
    AbsolutelyContinuousOnInterval
      (fun s => S.r s v * J s ^ 2 / ((1 - S.mu s v) ^ 2 * S.lam s v)) a b := by
  obtain ⟨hr, hl, hm, _⟩ := h.incoming_components_ac hab ha hb hbv hv
  have hp (x : ℝ) (hx : x ∈ uIcc a b) : (x, v) ∈ pastTriangle ui := by
    rw [uIcc_of_le hab] at hx
    exact ⟨ha.trans hx.1, hx.2.trans_lt hb, (hx.2.trans_lt hbv).le, hv⟩
  have hir := positive_ac_inv hr (fun x hx => by
    rw [uIcc_of_le hab] at hx
    exact h.r_pos (hp x (by rwa [uIcc_of_le hab])) (hx.2.trans_lt hbv))
  have hmu : AbsolutelyContinuousOnInterval (fun x => S.mu x v) a b := by
    simpa only [SSFields.mu, massRatio, div_eq_mul_inv] using (hm.const_mul 2).fun_mul hir
  have hone : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1 : ℝ)) a b :=
    (LipschitzWith.const 1).lipschitzOnWith.absolutelyContinuousOnInterval
  have hgap := hone.fun_sub hmu
  have hden : AbsolutelyContinuousOnInterval (fun x => (1 - S.mu x v) ^ 2 * S.lam x v)
      a b := by
    simpa only [pow_two] using (hgap.fun_mul hgap).fun_mul hl
  have hi := positive_ac_inv hden (fun x hx =>
    mul_pos (sq_pos_of_pos (sub_pos.mpr (h.mu_bounds (hp x hx)).2)) (h.lam_pos (hp x hx)))
  simpa only [div_eq_mul_inv, pow_two] using (hr.fun_mul (hJ.fun_mul hJ)).fun_mul hi

/-- The class energy identity for any frozen incoming ODE, rather than
only the actual remainder. Paper `e1a0fd5`, lines 1240–1248 and 1265–1268. -/
theorem frozen_ray_energy_identity_ae {a b v : ℝ} {J F : ℝ → ℝ}
    (hab : a ≤ b) (ha : ui ≤ a) (hb : b < 0) (hbv : b < v) (hv : v ≤ 0)
    (hJ : ∀ᵐ x, x ∈ Ioo a b → HasDerivAt J
      (S.incomingFlux x v * J x + 3 * S.nu x v * S.dvphi x v * F x) x) :
    ∀ᵐ x, x ∈ Ioo a b → HasDerivAt
      (fun s => S.r s v * J s ^ 2 / ((1 - S.mu s v) ^ 2 * S.lam s v))
      (-weightedRemainderDensity S (x, v) *
        (1 - 3 * S.mu x v / (1 - S.mu x v)) * J x ^ 2 +
        (6 * S.nu x v / (1 - S.mu x v) ^ 2) *
          (S.r x v / S.lam x v * S.dvphi x v) * F x * J x) x := by
  filter_upwards [h.incoming_reduced_ae hab ha hb hbv hv, hJ] with x hx hJx hxI
  have hp : (x, v) ∈ pastTriangle ui :=
    ⟨ha.trans hxI.1.le, hxI.2.trans hb, (hxI.2.trans hbv).le, hv⟩
  obtain ⟨hr, hl, hm, _, _⟩ := hx hxI
  simpa only [weightedRemainderDensity, SSFields.mu, SSFields.incomingFlux, neg_div, neg_neg] using
    Renormalized.Incoming.frozen_energy_identity
      (r := fun s => S.r s v) (lam := fun s => S.lam s v)
      (nu := fun s => S.nu s v) (m := fun s => S.m s v)
      (phiU := fun s => S.duphi s v) (phiV := fun s => S.dvphi s v)
      hr hl hm (hJx hxI) (h.r_pos hp (hxI.2.trans hbv)) (h.lam_pos hp)
      (h.nu_neg hp) (h.mu_bounds hp).2

/-- The integrated frozen incoming energy bound, with the nonnegative
future flux discarded and constants uniform in b and v. Ray source-square
integrability follows almost everywhere from finite M_U. Paper `e1a0fd5`,
`eq:frozen-solution-operators`, lines 1265–1276. -/
theorem frozen_ray_coercive_energy_bound {a b v δ ε : ℝ} {J F : ℝ → ℝ}
    (hab : a ≤ b) (ha : ui ≤ a) (hb : b < 0) (hbv : b < v) (hv : v ≤ 0)
    (hδ : δ < 1 / 3) (hsmall : WeightedLateSmallness ui S a δ ε)
    (hJ : AbsolutelyContinuousOnInterval J a b)
    (hJode : ∀ᵐ x, x ∈ Ioo a b → HasDerivAt J
      (S.incomingFlux x v * J x + 3 * S.nu x v * S.dvphi x v * F x) x)
    (hF : IntervalIntegrable (fun x => F x ^ 2) volume a b) :
    (∫ x in a..b, weightedRemainderDensity S (x, v) * J x ^ 2) ≤
      (S.r a v * J a ^ 2 / ((1 - S.mu a v) ^ 2 * S.lam a v) +
        (18 * ε ^ 2 / (1 - 3 * δ)) * ∫ x in a..b,
          weightedSourceDensity S (x, v) * F x ^ 2) / ((1 - 3 * δ) / 2) := by
  let c := 1 - 3 * δ
  have hc : 0 < c := by dsimp only [c]; linarith
  let E := fun x => S.r x v * J x ^ 2 / ((1 - S.mu x v) ^ 2 * S.lam x v)
  let q := fun x => weightedRemainderDensity S (x, v) * J x ^ 2
  let g := fun x => (18 * ε ^ 2 / c) * (weightedSourceDensity S (x, v) * F x ^ 2)
  have hp (x : ℝ) (hx : x ∈ Icc a b) : (x, v) ∈ pastTriangle ui :=
    ⟨ha.trans hx.1, hx.2.trans_lt hb, (hx.2.trans_lt hbv).le, hv⟩
  obtain ⟨hr, hl, hm, _⟩ := h.incoming_components_ac hab ha hb hbv hv
  have hn := continuous_in h.regularCenter.continuous_nu
    (inSeg_subset_triangle ha hb hbv.le hv)
  have hrc : ContinuousOn (fun x => S.r x v) (Icc a b) := by
    simpa only [uIcc_of_le hab] using hr.continuousOn
  have hmc : ContinuousOn (fun x => S.m x v) (Icc a b) := by
    simpa only [uIcc_of_le hab] using hm.continuousOn
  have hmu : ContinuousOn (fun x => S.mu x v) (Icc a b) :=
    (hmc.const_mul 2).div hrc
      (fun x hx => (h.r_pos (hp x hx) (hx.2.trans_lt hbv)).ne')
  have hden : ContinuousOn (fun x => (1 - S.mu x v) ^ 2 * S.lam x v) (Icc a b) :=
    ((continuousOn_const.sub hmu).pow 2).mul
    (by simpa only [uIcc_of_le hab] using hl.continuousOn)
  have hw : ContinuousOn (fun x => weightedRemainderDensity S (x, v)) (Icc a b) :=
    hn.neg.div hden (fun x hx => (mul_pos
      (sq_pos_of_pos (sub_pos.mpr (h.mu_bounds (hp x hx)).2)) (h.lam_pos (hp x hx))).ne')
  have hs : ContinuousOn (fun x => weightedSourceDensity S (x, v)) (Icc a b) :=
    (hn.neg.mul (by simpa only [uIcc_of_le hab] using hl.continuousOn)).div
      ((continuousOn_const.sub hmu).pow 2)
      (fun x hx => (sq_pos_of_pos (sub_pos.mpr (h.mu_bounds (hp x hx)).2)).ne')
  have hqc : ContinuousOn q (Icc a b) :=
    hw.mul (by simpa only [uIcc_of_le hab] using hJ.continuousOn.fun_pow 2)
  have hq : IntervalIntegrable q volume a b := hqc.intervalIntegrable_of_Icc hab
  have hg : IntervalIntegrable g volume a b :=
    (hF.continuousOn_mul (by simpa only [← uIcc_of_le hab] using hs)).const_mul _
  have hE := h.frozen_ray_energy_ac hab ha hb hbv hv hJ
  have hbound : ∀ᵐ x ∂volume.restrict (Ioc a b), deriv E x + (c / 2) * q x ≤ g x := by
    have hid := h.frozen_ray_energy_identity_ae hab ha hb hbv hv hJode
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hid, volume.ae_ne b] with x hx hxb hxI
    have hxO : x ∈ Ioo a b := ⟨hxI.1, lt_of_le_of_ne hxI.2 hxb⟩
    have hpx := hp x ⟨hxI.1.le, hxI.2⟩
    have hlate := hsmall (x, v) hpx hxI.1.le
    have hA : |S.r x v / S.lam x v * S.dvphi x v| ≤ ε :=
      (le_add_of_nonneg_right (abs_nonneg (weightedIncomingAmplitude S x v))).trans hlate.2
    have hd := (hx hxO).deriv
    have hcoeff : c ≤ 1 - 3 * S.mu x v / (1 - S.mu x v) := by
      calc
        c ≤ 1 - 3 * (S.mu x v / (1 - S.mu x v)) := by
          dsimp only [c]
          linarith [hlate.1]
        _ = _ := by ring
    have halg := frozen_coercive_differential_bound
      (t := (-S.nu x v) / (1 - S.mu x v) ^ 2) (lam := S.lam x v)
      (A := S.r x v / S.lam x v * S.dvphi x v) (F := F x) (J := J x)
      (coeff := 1 - 3 * S.mu x v / (1 - S.mu x v)) (d := deriv E x)
      (div_nonneg (neg_pos.mpr (h.nu_neg hpx)).le (sq_nonneg _)) (h.lam_pos hpx) hc
      hcoeff hA (by
        rw [hd]
        simp only [weightedRemainderDensity, div_eq_mul_inv, mul_inv_rev]
        ring)
    convert halg using 1 <;>
      simp only [q, g, weightedRemainderDensity, weightedSourceDensity,
        div_eq_mul_inv, mul_inv_rev] <;> ring
  have hbE : 0 ≤ E b := div_nonneg (mul_nonneg (h.r_pos (hp b ⟨hab, le_rfl⟩) hbv).le
    (sq_nonneg _)) (mul_nonneg (sq_nonneg _) (h.lam_pos (hp b ⟨hab, le_rfl⟩)).le)
  have hres := ac_coercive_energy_bound hab (by positivity : 0 < c / 2) hE hq hg hbound hbE
  simpa only [E, q, g, intervalIntegral.integral_const_mul, c] using hres

end StandingFull

end AcExtensionPrinciple

end
