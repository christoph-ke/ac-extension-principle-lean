module

public import AcExtensionPrinciple.Observability.LemmaA3Lapse

/-!
# Lemma A.3: annular scalar estimate

Paper `e1a0fd5`, `eq:observability-annular-scalar`, lines 1585–1591.
All calculus takes place on a compact outgoing segment away from the axis.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory

namespace NormalizedChartData

variable {b T K : ℝ} {S : SSFields} (h : NormalizedChartData b T K S)

include h

/-- The scalar and incoming scalar amplitude are AC on an outgoing annular
segment. Paper `e1a0fd5`, lines 1585–1591, local AC at line 1522. -/
theorem lemmaA3_radial_scalar_ac {s t : ℝ}
    (hq : (s, t) ∈ chartInterior (chartCylinder h.g T) S) :
    AbsolutelyContinuousOnInterval (S.phi s) t s ∧
      AbsolutelyContinuousOnInterval (S.zeta s) t s := by
  have hseg := h.lemmaA3_out_interior hq
  have hsub {z : ℝ} (hz : z ∈ Icc t s) : outSeg s t z ⊆ chartInterior (chartCylinder h.g T) S :=
    fun q hq' => hseg ⟨hq'.1, hq'.2.1, hq'.2.2.trans hz.2⟩
  have hrac := (h.lemmaA3_radial_ac hq).1
  have hri := positive_ac_inv hrac (by
    intro z hz
    rw [uIcc_of_le hq.1.2.2.2] at hz
    exact (hseg (show (s, z) ∈ outSeg s t s from ⟨by simp, hz⟩)).2)
  have hψ := intervalPrimitive_ac hq.1.2.2.2 (fun z hz =>
    h.equations.psi_t s t z hz.1 (fun q hq' => (hsub hz hq').1))
  have hφ : AbsolutelyContinuousOnInterval (S.phi s) t s := by
    apply (hψ.mul hri).congr
    intro z hz
    rw [uIcc_of_le hq.1.2.2.2] at hz
    change S.r s z * S.phi s z * (S.r s z)⁻¹ = S.phi s z
    field_simp [(hseg (show (s, z) ∈ outSeg s t s from ⟨by simp, hz⟩)).2.ne']
  have hU := intervalPrimitive_ac hq.1.2.2.2 (fun z hz =>
    h.equations.dupsi_t s t z hz.1 (hsub hz))
  refine ⟨hφ, ?_⟩
  exact hU.sub ((h.lemmaA3_radial_ac hq).2.2.1.mul hφ)

/-- Integral form of the incoming scalar amplitude's radial equation. Paper
`e1a0fd5`, `eq:observability-annular-scalar`, lines 1585–1591. -/
theorem lemmaA3_scalar_primitive {s t : ℝ}
    (hq : (s, t) ∈ chartInterior (chartCylinder h.g T) S) :
    IntervalPrimitive (S.zeta s) (fun z => -S.nu s z * S.dvphi s z) t s := by
  apply ac_integral_eq_sub hq.1.2.2.2 (h.lemmaA3_radial_scalar_ac hq).2
  filter_upwards [h.equations_t_ae hq.1.2.2.2 (h.lemmaA3_out_interior hq)] with z hz hzI
  exact (hz hzI).2.2

/-- The inverse-radius integral gives exactly the scalar estimate's radial
factor. Paper `e1a0fd5`, `eq:observability-annular-scalar`, lines 1588–1591. -/
theorem lemmaA3_inverse_radius_integral {s t : ℝ}
    (hq : (s, t) ∈ chartInterior (chartCylinder h.g T) S) :
    (∫ z in t..s, S.lam s z / S.r s z ^ 2) = (S.r s t)⁻¹ - b⁻¹ := by
  have hseg := h.lemmaA3_out_interior hq
  have hri := positive_ac_inv (h.lemmaA3_radial_ac hq).1 (by
    intro z hz
    rw [uIcc_of_le hq.1.2.2.2] at hz
    exact (hseg (show (s, z) ∈ outSeg s t s from ⟨by simp, hz⟩)).2)
  have hR := intervalPrimitive_ae_hasDerivAt hq.1.2.2.2 (fun z hz =>
    h.equations.radius_t s t z hz.1 (fun q hq' =>
      (hseg ⟨hq'.1, hq'.2.1, hq'.2.2.trans hz.2⟩).1))
  have hh := ac_integral_eq_sub hq.1.2.2.2 (hri.const_mul (-1)) (by
    filter_upwards [hR] with z hz hzI
    have hr := (hseg (show (s, z) ∈ outSeg s t s from ⟨by simp, hzI.1.le, hzI.2.le⟩)).2
    convert ((hz hzI).inv hr.ne').const_mul (-1) using 1)
  have he := hh.2
  dsimp only at he
  simp only [neg_mul, one_mul, neg_div, neg_neg] at he
  rw [(h.boundary_gauge s ⟨hq.1.1, hq.1.2.1⟩).1] at he
  linarith

/-- Weighted Cauchy–Schwarz gives the printed scalar bound, with its sharp
outer-gap coefficient. Paper `e1a0fd5`, `eq:observability-annular-scalar`,
lines 1585–1591. -/
theorem lemmaA3_annular_scalar {s t : ℝ}
    (hq : (s, t) ∈ chartInterior (chartCylinder h.g T) S) :
    (S.zeta s s - S.zeta s t) ^ 2 ≤
      2 * (S.m s s - S.m s t) / (1 - S.mu s s) * ((S.r s t)⁻¹ - b⁻¹) := by
  have hseg := h.lemmaA3_out_interior hq
  let w : ℝ → ℝ := fun z => S.nu s z ^ 2 * S.lam s z /
    ((1 - S.mu s z) * S.r s z ^ 2)
  let f : ℝ → ℝ := fun z => -S.nu s z * S.dvphi s z
  have hcr : ContinuousOn (S.r s) (Icc t s) := h.continuous_r.comp
    (continuous_const.prodMk continuous_id).continuousOn
    (fun z hz => (hseg (show (s, z) ∈ outSeg s t s from ⟨by simp, hz⟩)).1)
  have hcm : ContinuousOn (S.m s) (Icc t s) := h.continuous_m.comp
    (continuous_const.prodMk continuous_id).continuousOn
    (fun z hz => (hseg (show (s, z) ∈ outSeg s t s from ⟨by simp, hz⟩)).1)
  have hcn : ContinuousOn (S.nu s) (Icc t s) := h.continuous_nu.comp
    (continuous_const.prodMk continuous_id).continuousOn
    (fun z hz => (hseg (show (s, z) ∈ outSeg s t s from ⟨by simp, hz⟩)).1)
  have hcl : ContinuousOn (S.lam s) (Icc t s) := h.continuous_lam.comp
    (continuous_const.prodMk continuous_id).continuousOn
    (fun z hz => (hseg (show (s, z) ∈ outSeg s t s from ⟨by simp, hz⟩)).1)
  have hcg : ContinuousOn (fun z => 1 - S.mu s z) (Icc t s) := by
    apply continuousOn_const.sub
    exact (hcm.const_mul 2).div hcr (fun z hz => (hseg (show (s, z) ∈ outSeg s t s from ⟨by simp, hz⟩)).2.ne')
  have hw : ContinuousOn w (Icc t s) :=
    ((hcn.pow 2).mul hcl).div (hcg.mul (hcr.pow 2)) (by
      intro z hz
      exact mul_ne_zero (h.gap_pos (hseg (show (s, z) ∈ outSeg s t s from ⟨by simp, hz⟩)).1).ne'
        (pow_ne_zero _ (hseg (show (s, z) ∈ outSeg s t s from ⟨by simp, hz⟩)).2.ne'))
  have hwp : ∀ z ∈ Icc t s, 0 < w z := by
    intro z hz
    have hm := hseg (show (s, z) ∈ outSeg s t s from ⟨by simp, hz⟩)
    have hn := (h.signs s z hm.1).2.1
    have hl := (h.signs s z hm.1).1
    dsimp [w]
    exact div_pos (mul_pos (sq_pos_of_ne_zero hn.ne) hl)
      (mul_pos (h.gap_pos hm.1) (sq_pos_of_pos hm.2))
  have hf := h.lemmaA3_scalar_primitive hq
  have hM := h.equations.mass_t s t s hq.1.2.2.2 (fun q hq' => (hseg hq').1)
  have heq : ∀ z ∈ uIcc t s, f z ^ 2 / w z = 2 * S.massV s z := by
    intro z hz
    rw [uIcc_of_le hq.1.2.2.2] at hz
    have hm := hseg (show (s, z) ∈ outSeg s t s from ⟨by simp, hz⟩)
    have hn := (h.signs s z hm.1).2.1.ne
    have hl := (h.signs s z hm.1).1.ne'
    have hg := (h.gap_pos hm.1).ne'
    dsimp [f, w]
    unfold SSFields.dvphi SSFields.massV
    field_simp [hn, hl, hg, hm.2.ne']
  have hf2 : IntervalIntegrable (fun z => f z ^ 2 / w z) volume t s :=
    (hM.1.const_mul 2).congr (fun z hz => (heq z (uIoc_subset_uIcc hz)).symm)
  have hcs := lemmaA3_weighted_sq_le hq.1.2.2.2 hf.1 hw hwp hf2
  rw [← hf.2] at hcs
  have hfm : (∫ z in t..s, f z ^ 2 / w z) = 2 * (S.m s s - S.m s t) := by
    rw [intervalIntegral.integral_congr heq, intervalIntegral.integral_const_mul, ← hM.2]
  rw [hfm] at hcs
  have hmajor : IntervalIntegrable (fun z => (1 - S.mu s s)⁻¹ *
      (S.lam s z / S.r s z ^ 2)) volume t s := by
    apply ContinuousOn.intervalIntegrable
    exact (continuousOn_const.mul (hcl.div (hcr.pow 2) (by
      intro z hz
      exact pow_ne_zero _ (hseg (show (s, z) ∈ outSeg s t s from ⟨by simp, hz⟩)).2.ne'))).mono (by rw [uIcc_of_le hq.1.2.2.2])
  have hwb : (∫ z in t..s, w z) ≤ (1 - S.mu s s)⁻¹ * ((S.r s t)⁻¹ - b⁻¹) := by
    have hi := intervalIntegral.integral_mono_on hq.1.2.2.2
      (hw.mono (by rw [uIcc_of_le hq.1.2.2.2])).intervalIntegrable hmajor (by
        intro z hz
        have hm := hseg (show (s, z) ∈ outSeg s t s from ⟨by simp, hz⟩)
        have hl := (h.signs s z hm.1).1
        have he : w z = (S.nu s z ^ 2 / (1 - S.mu s z)) * (S.lam s z / S.r s z ^ 2) := by
          dsimp [w]
          field_simp [(h.gap_pos hm.1).ne', hm.2.ne']
        rw [he]
        exact mul_le_mul_of_nonneg_right (h.lemmaA3_lapse_square_bound hm) (by positivity))
    rw [intervalIntegral.integral_const_mul, h.lemmaA3_inverse_radius_integral hq] at hi
    exact hi
  have hD : 0 ≤ S.m s s - S.m s t := sub_nonneg.mpr (h.mass_le_boundary hq.1)
  have hmul := mul_le_mul_of_nonneg_left hwb (show 0 ≤ 2 * (S.m s s - S.m s t) by positivity)
  calc
    _ ≤ 2 * (S.m s s - S.m s t) * (∫ z in t..s, w z) := hcs
    _ ≤ 2 * (S.m s s - S.m s t) * ((1 - S.mu s s)⁻¹ * ((S.r s t)⁻¹ - b⁻¹)) := hmul
    _ = _ := by ring

end NormalizedChartData

end AcExtensionPrinciple

end
