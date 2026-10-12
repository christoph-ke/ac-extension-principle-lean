module

public import AcExtensionPrinciple.Decay.ClassRayConsequences
public import AcExtensionPrinciple.Decay.ScalarVariation
public import AcExtensionPrinciple.Decay.ScalarComparison

/-!
# Normalized scalar transport in the standing class

Paper `e1a0fd5`, `eq:normalized-scalar-transport`, lines 100–104 and 952–987.
The characteristic primitives give AC quotients and their prescribed
derivatives; no pointwise differentiability hypothesis is added to the class.
-/

public section

namespace AcExtensionPrinciple.StandingFull

open Set Filter MeasureTheory
open scoped Topology ENNReal

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The outgoing normalized datum is AC on compact incoming segments.
Paper `e1a0fd5`, lines 952–971, `eq:normalized-scalar-transport`. -/
theorem decay_datum_ac_in {v a b : ℝ} (hab : a ≤ b) (ha : ui ≤ a)
    (hb0 : b < 0) (hbv : b < v) (hv0 : v ≤ 0) :
    AbsolutelyContinuousOnInterval (fun u => S.dvpsi u v / S.lam u v) a b := by
  have hd := intervalPrimitive_ac hab (fun x hx =>
    h.regularCenter.localBV.dvpsi_in v a x hx.1
      (inSeg_subset_offAxis ha (hx.2.trans_lt hb0) (hx.2.trans_lt hbv) hv0))
  have hi := positive_ac_inv (h.lam_ac_in hab ha hb0 hbv hv0) (by
    intro x hx
    rw [uIcc_of_le hab] at hx
    exact h.lam_pos (p := (x, v))
      ⟨ha.trans hx.1, hx.2.trans_lt hb0, (hx.2.trans_lt hbv).le, hv0⟩)
  simpa only [div_eq_mul_inv] using hd.fun_mul hi

/-- Incoming transport of the normalized outgoing datum, a.e. on compact
segments. Paper `e1a0fd5`, lines 952–971, `eq:normalized-scalar-transport`. -/
theorem decay_datum_deriv_in {v a b : ℝ} (hab : a ≤ b) (ha : ui ≤ a)
    (hb0 : b < 0) (hbv : b < v) (hv0 : v ≤ 0) :
    ∀ᵐ x ∂volume, x ∈ Ioo a b →
      deriv (fun u => S.dvpsi u v / S.lam u v) x =
        -(S.gamma x v * S.varkappa x v) * (S.dvpsi x v / S.lam x v - S.phi x v) := by
  have hd := intervalPrimitive_ae_hasDerivAt hab (fun x hx =>
    h.regularCenter.localBV.dvpsi_in v a x hx.1
      (inSeg_subset_offAxis ha (hx.2.trans_lt hb0) (hx.2.trans_lt hbv) hv0))
  have hl := intervalPrimitive_ae_hasDerivAt hab (fun x hx =>
    h.regularCenter.localBV.lam_in v a x hx.1
      (inSeg_subset_offAxis ha (hx.2.trans_lt hb0) (hx.2.trans_lt hbv) hv0))
  filter_upwards [hd, hl] with x hdx hlx hx
  have hp : (x, v) ∈ pastTriangle ui :=
    ⟨ha.trans hx.1.le, hx.2.trans hb0, (hx.2.trans hbv).le, hv0⟩
  have hl0 := ne_of_gt (h.lam_pos hp)
  have hc : S.radiusCoeff x v = S.lam x v * (S.gamma x v * S.varkappa x v) := by
    rw [S.radiusCoeff_eq]
    exact radius_coefficient_eq _ _ _ _
  rw [((hdx hx).fun_div (hlx hx) hl0).deriv, hc]
  field_simp [hl0]
  ring

/-- The incoming normalized datum is AC on compact off-axis outgoing segments.
Paper `e1a0fd5`, `eq:incoming-normalized-damping`, lines 974–981. -/
theorem decay_incoming_ac_out {u a b : ℝ} (hab : a ≤ b) (hu : ui ≤ u)
    (hu0 : u < 0) (hua : u < a) (hb0 : b ≤ 0) :
    AbsolutelyContinuousOnInterval (fun v => S.dupsi u v / S.nu u v) a b := by
  have hd := intervalPrimitive_ac hab (fun x hx =>
    h.regularCenter.localBV.dupsi_out u a x hx.1 (outSeg_subset_offAxis hu hu0 hua
      (hx.2.trans hb0)))
  have hn := intervalPrimitive_ac hab (fun x hx =>
    h.regularCenter.localBV.nu_out u a x hx.1 (outSeg_subset_offAxis hu hu0 hua
      (hx.2.trans hb0)))
  have hi := (positive_ac_inv hn.neg (by
    intro x hx
    rw [uIcc_of_le hab] at hx
    exact neg_pos.mpr (h.nu_neg (p := (u, x))
      ⟨hu, hu0, (hua.trans_le hx.1).le, hx.2.trans hb0⟩))).neg
  simpa only [Pi.neg_apply, inv_neg, neg_neg, div_eq_mul_inv] using hd.fun_mul hi

/-- Outgoing damping of the normalized incoming datum, with no scalar second
derivatives. Paper `e1a0fd5`, `eq:incoming-normalized-damping`, lines 974–981. -/
theorem decay_incoming_deriv_out {u a b : ℝ} (hab : a ≤ b) (hu : ui ≤ u)
    (hu0 : u < 0) (hua : u < a) (hb0 : b ≤ 0) :
    ∀ᵐ x ∂volume, x ∈ Ioo a b →
      deriv (fun v => S.dupsi u v / S.nu u v) x =
        -(S.kappa u x * S.varkappa u x) * (S.dupsi u x / S.nu u x - S.phi u x) := by
  have hd := intervalPrimitive_ae_hasDerivAt hab (fun x hx =>
    h.regularCenter.localBV.dupsi_out u a x hx.1 (outSeg_subset_offAxis hu hu0 hua
      (hx.2.trans hb0)))
  have hn := intervalPrimitive_ae_hasDerivAt hab (fun x hx =>
    h.regularCenter.localBV.nu_out u a x hx.1 (outSeg_subset_offAxis hu hu0 hua
      (hx.2.trans hb0)))
  filter_upwards [hd, hn] with x hdx hnx hx
  have hp : (u, x) ∈ pastTriangle ui := ⟨hu, hu0, (hua.trans hx.1).le, hx.2.le.trans hb0⟩
  have hn0 := ne_of_lt (h.nu_neg hp)
  have hc : S.radiusCoeff u x = S.nu u x * (S.kappa u x * S.varkappa u x) := by
    rw [S.radiusCoeff_eq]
    ring
  rw [((hdx hx).fun_div (hnx hx) hn0).deriv, hc]
  field_simp [hn0]
  ring

/-- A truncated blueshift integral, also on the terminal ray, is bounded by B*.
Paper `e1a0fd5`, lines 952–971 and `eq:terminal-blueshift-bound`. -/
theorem decay_blueshift_segment {v a b : ℝ} (hab : a ≤ b) (ha : ui ≤ a)
    (hb0 : b < 0) (hbv : b < v) (hv0 : v ≤ 0) :
    IntervalIntegrable (fun s => -(S.gamma s v * S.varkappa s v)) volume a b ∧
      (∫ s in a..b, -(S.gamma s v * S.varkappa s v)) ≤ Bstar ui S := by
  have hc := h.continuous_blueshift.comp (continuous_id.prodMk continuous_const).continuousOn
    (fun x (hx : x ∈ Icc a b) => ⟨⟨ha.trans hx.1, hx.2.trans_lt hb0,
      (hx.2.trans_lt hbv).le, hv0⟩, hx.2.trans_lt hbv⟩)
  have hi : IntervalIntegrable (fun s => -(S.gamma s v * S.varkappa s v)) volume a b :=
    hc.intervalIntegrable_of_Icc hab
  refine ⟨hi, ?_⟩
  have hbound : (∫⁻ s in Ioo a b, ENNReal.ofReal (-(S.gamma s v * S.varkappa s v))) ≤
      blueshiftSup ui S := by
    have hsub : Ioo a b ⊆ Ioo ui v := fun s hs => ⟨ha.trans_lt hs.1, hs.2.trans hbv⟩
    apply (lintegral_mono_set hsub).trans
    rcases hv0.eq_or_lt with hv | hv
    · subst v
      exact h.terminal_blueshift_le
    · exact le_iSup_of_le v (le_iSup_of_le (show v ∈ Ioo ui 0 from
        ⟨ha.trans_lt (hab.trans_lt hbv), hv⟩) le_rfl)
  rw [← ofReal_intervalIntegral hab hi (fun s hs => h.blueshift_nonneg (u := s) (v := v)
    ⟨ha.trans hs.1.le, hs.2.trans hb0, (hs.2.trans hbv).le, hv0⟩ (hs.2.trans hbv))] at hbound
  exact (ENNReal.ofReal_le_iff_le_toReal h.blueshift_finite.ne).mp hbound

/-- Tail amplitude controls variation of the normalized datum on a compact
incoming segment. Paper `e1a0fd5`, `eq:terminal-scalar-variation`, lines 952–961. -/
theorem decay_datum_variation {v a b M : ℝ} (hab : a ≤ b) (ha : ui ≤ a)
    (hb0 : b < 0) (hbv : b < v) (hv0 : v ≤ 0)
    (hA : ∀ x ∈ Icc a b, |S.dvpsi x v / S.lam x v - S.phi x v| ≤ M) :
    eVariationOn (fun u => S.dvpsi u v / S.lam u v) (Icc a b) ≤
      ENNReal.ofReal (Bstar ui S * M) := by
  have hg := h.decay_blueshift_segment hab ha hb0 hbv hv0
  apply scalar_variation_le_weighted_bound hab (h.decay_datum_ac_in hab ha hb0 hbv hv0)
    hg.1 _ _ hA hg.2
  · exact Eventually.of_forall (fun x hx => h.blueshift_nonneg (u := x) (v := v)
      ⟨ha.trans hx.1.le, hx.2.trans hb0, (hx.2.trans hbv).le, hv0⟩ (hx.2.trans hbv))
  · filter_upwards [h.decay_datum_deriv_in hab ha hb0 hbv hv0] with x hx hxi
    rw [hx hxi, abs_mul, abs_of_nonneg (h.blueshift_nonneg (u := x) (v := v)
      ⟨ha.trans hxi.1.le, hxi.2.trans hb0, (hxi.2.trans hbv).le, hv0⟩ (hxi.2.trans hbv))]

/-- Comparison of nearby cones along an incoming ray. Paper `e1a0fd5`,
`eq:scalar-nearby-cone-comparison`, lines 964–971. -/
theorem decay_datum_comparison {v a b M : ℝ} (hab : a ≤ b) (ha : ui ≤ a)
    (hb0 : b < 0) (hbv : b < v) (hv0 : v ≤ 0)
    (hA : ∀ x ∈ Icc a b, |S.dvpsi x v / S.lam x v - S.phi x v| ≤ M) :
    |S.dvpsi b v / S.lam b v - S.dvpsi a v / S.lam a v| ≤ Bstar ui S * M := by
  have hb := (eVariationOn.edist_le (fun u => S.dvpsi u v / S.lam u v)
    (show b ∈ Icc a b from ⟨hab, le_rfl⟩) (show a ∈ Icc a b from ⟨le_rfl, hab⟩)).trans
    (h.decay_datum_variation hab ha hb0 hbv hv0 hA)
  rw [edist_dist, Real.dist_eq] at hb
  exact ENNReal.ofReal_le_ofReal_iff (by
    have hm := (abs_nonneg _).trans (hA a ⟨le_rfl, hab⟩)
    exact mul_nonneg ENNReal.toReal_nonneg hm) |>.mp hb

end AcExtensionPrinciple.StandingFull

end
