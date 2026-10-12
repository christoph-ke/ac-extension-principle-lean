module

public import AcExtensionPrinciple.Observability.LemmaA3Calculus

/-!
# Lemma A.3: the annular lapse

Paper `e1a0fd5`, `eq:observability-annular-lapse` and
`eq:observability-annular-lapse-bounds`, lines 1567–1583.
The radial comparison is proved with an AC integrating factor.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory

/-- Positive magnitude of the normalized incoming lapse. Paper `e1a0fd5`,
`eq:observability-annular-lapse`, lines 1570–1574. -/
@[expose] noncomputable def chartLapse (S : SSFields) (s t : ℝ) : ℝ :=
  gammaOf (-S.nu s t) (S.mu s t)

namespace NormalizedChartData

variable {b T K : ℝ} {S : SSFields} (h : NormalizedChartData b T K S)

include h

/-- The segment from a positive-radius point to the cylinder stays off the
axis. Paper `e1a0fd5`, annulus at lines 1567–1568. -/
theorem lemmaA3_out_interior {s t : ℝ}
    (hq : (s, t) ∈ chartInterior (chartCylinder h.g T) S) :
    outSeg s t s ⊆ chartInterior (chartCylinder h.g T) S := by
  intro q hq'
  have hs : s ∈ Icc 0 T := ⟨hq.1.1, hq.1.2.1⟩
  have hm := h.out_subset hs hq.1.2.2.1 le_rfl hq'
  have hx : q.1 = s := by simpa using hq'.1
  have hr := h.radius_t_mono hq'.2.1 (h.out_subset hs hq.1.2.2.1 hq'.2.2)
  refine ⟨hm, ?_⟩
  simpa [hx] using hq.2.trans_le hr

/-- Lapse is strictly positive. Paper `e1a0fd5`,
`eq:observability-annular-lapse`, lines 1570–1574. -/
theorem lemmaA3_lapse_pos {s t : ℝ} (hq : (s, t) ∈ chartCylinder h.g T) :
    0 < chartLapse S s t := by
  unfold chartLapse gammaOf
  exact div_pos (neg_pos.mpr (h.signs s t hq).2.1) (h.gap_pos hq)

/-- Radius, mass, expansion, and lapse are AC on an annular outgoing segment.
Paper `e1a0fd5`, lines 1570–1583, local AC justification at line 1522. -/
theorem lemmaA3_radial_ac {s t : ℝ}
    (hq : (s, t) ∈ chartInterior (chartCylinder h.g T) S) :
    AbsolutelyContinuousOnInterval (S.r s) t s ∧
      AbsolutelyContinuousOnInterval (S.m s) t s ∧
      AbsolutelyContinuousOnInterval (S.nu s) t s ∧
      AbsolutelyContinuousOnInterval (chartLapse S s) t s := by
  have hseg := h.lemmaA3_out_interior hq
  have hsub {z : ℝ} (hz : z ∈ Icc t s) : outSeg s t z ⊆ chartInterior (chartCylinder h.g T) S :=
    fun q hq' => hseg ⟨hq'.1, hq'.2.1, hq'.2.2.trans hz.2⟩
  have hr := intervalPrimitive_ac hq.1.2.2.2 (fun z hz =>
    h.equations.radius_t s t z hz.1 (fun q hq' => (hsub hz hq').1))
  have hm := intervalPrimitive_ac hq.1.2.2.2 (fun z hz =>
    h.equations.mass_t s t z hz.1 (fun q hq' => (hsub hz hq').1))
  have hn := intervalPrimitive_ac hq.1.2.2.2 (fun z hz =>
    h.equations.nu_t s t z hz.1 (hsub hz))
  have hri := positive_ac_inv hr (by
    intro z hz
    rw [uIcc_of_le hq.1.2.2.2] at hz
    exact (hseg (show (s, z) ∈ outSeg s t s from ⟨by simp, hz⟩)).2)
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1 : ℝ)) t s :=
    (LipschitzWith.const _).lipschitzOnWith.absolutelyContinuousOnInterval
  have hg : AbsolutelyContinuousOnInterval (fun z => 1 - S.mu s z) t s := by
    convert hc.sub ((hm.const_mul 2).mul hri) using 1
    funext z
    simp [SSFields.mu, massRatio, div_eq_mul_inv]
  have hgi := positive_ac_inv hg (by
    intro z hz
    rw [uIcc_of_le hq.1.2.2.2] at hz
    exact h.gap_pos (hseg (show (s, z) ∈ outSeg s t s from ⟨by simp, hz⟩)).1)
  refine ⟨hr, hm, hn, ?_⟩
  convert (hn.const_mul (-1)).mul hgi using 1
  funext z
  simp [chartLapse, gammaOf, div_eq_mul_inv]

/-- The lapse has logarithmic derivative `2m_t/(r-2m)`. Paper `e1a0fd5`,
`eq:observability-annular-lapse`, lines 1570–1574. -/
theorem lemmaA3_lapse_ae {s t : ℝ}
    (hq : (s, t) ∈ chartInterior (chartCylinder h.g T) S) :
    ∀ᵐ z, z ∈ Ioo t s → HasDerivAt (chartLapse S s)
      (chartLapse S s z * (2 * S.massV s z / (S.r s z * (1 - S.mu s z)))) z := by
  have hseg := h.lemmaA3_out_interior hq
  have hsub {z : ℝ} (hz : z ∈ Icc t s) : outSeg s t z ⊆ chartInterior (chartCylinder h.g T) S :=
    fun q hq' => hseg ⟨hq'.1, hq'.2.1, hq'.2.2.trans hz.2⟩
  have hr := intervalPrimitive_ae_hasDerivAt hq.1.2.2.2 (fun z hz =>
    h.equations.radius_t s t z hz.1 (fun q hq' => (hsub hz hq').1))
  have hm := intervalPrimitive_ae_hasDerivAt hq.1.2.2.2 (fun z hz =>
    h.equations.mass_t s t z hz.1 (fun q hq' => (hsub hz hq').1))
  have hn := intervalPrimitive_ae_hasDerivAt hq.1.2.2.2 (fun z hz =>
    h.equations.nu_t s t z hz.1 (hsub hz))
  filter_upwards [hr, hm, hn] with z hR hM hN hz
  have hmem := hseg (show (s, z) ∈ outSeg s t s from ⟨by simp, hz.1.le, hz.2.le⟩)
  have hgap := h.gap_pos hmem.1
  have hG := (hasDerivAt_const z (1 : ℝ)).sub (((hM hz).const_mul 2).div (hR hz) hmem.2.ne')
  have hd := (hN hz).neg.div hG hgap.ne'
  dsimp only [Pi.neg_apply, Pi.sub_apply, Pi.div_apply] at hd
  apply hd.congr_deriv
  have hrg : S.r s z * (1 - S.mu s z) = S.r s z - 2 * S.m s z := by
    unfold SSFields.mu massRatio
    field_simp [hmem.2.ne']
  have hden : S.r s z - 2 * S.m s z ≠ 0 := by
    rw [← hrg]
    exact mul_ne_zero hmem.2.ne' hgap.ne'
  unfold chartLapse gammaOf SSFields.massV SSFields.radiusCoeff SSFields.mu massRatio
  field_simp [hmem.2.ne', hden, (h.signs s z hmem.1).1.ne']
  ring

/-- Integral form of the logarithmic annular lapse equation. Paper
`e1a0fd5`, `eq:observability-annular-lapse`, lines 1570–1574.
Division by `r_t` converts this characteristic identity to the radial one. -/
theorem lemmaA3_lapse_log_primitive {s t : ℝ}
    (hq : (s, t) ∈ chartInterior (chartCylinder h.g T) S) :
    IntervalPrimitive (fun z => Real.log (chartLapse S s z))
      (fun z => 2 * S.massV s z / (S.r s z * (1 - S.mu s z))) t s := by
  have hseg := h.lemmaA3_out_interior hq
  have hlog := positive_ac_log (h.lemmaA3_radial_ac hq).2.2.2 (by
    intro z hz
    rw [uIcc_of_le hq.1.2.2.2] at hz
    exact h.lemmaA3_lapse_pos
      (hseg (show (s, z) ∈ outSeg s t s from ⟨by simp, hz⟩)).1)
  apply ac_integral_eq_sub hq.1.2.2.2 hlog
  filter_upwards [h.lemmaA3_lapse_ae hq] with z hz hzI
  have hp := h.lemmaA3_lapse_pos
    (hseg (show (s, z) ∈ outSeg s t s from ⟨by simp, hzI.1.le, hzI.2.le⟩)).1
  apply ((hz hzI).log hp.ne').congr_deriv
  field_simp [hp.ne']

/-- The lapse increases in the outgoing direction. Paper `e1a0fd5`,
`eq:observability-annular-lapse-bounds`, lines 1576–1583. -/
theorem lemmaA3_lapse_le_boundary {s t : ℝ}
    (hq : (s, t) ∈ chartInterior (chartCylinder h.g T) S) :
    chartLapse S s t ≤ (1 - S.mu s s)⁻¹ := by
  have hl := lemmaA3_ac_endpoint_le hq.1.2.2.2 (h.lemmaA3_radial_ac hq).2.2.2 (by
    filter_upwards [h.lemmaA3_lapse_ae hq] with z hz hzI
    rw [(hz hzI).deriv]
    have hmem := (h.lemmaA3_out_interior hq) (show (s, z) ∈ outSeg s t s from ⟨by simp, hzI.1.le, hzI.2.le⟩)
    have hm : 0 ≤ S.massV s z := by
      unfold SSFields.massV
      exact div_nonneg (mul_nonneg (h.gap_pos hmem.1).le (sq_nonneg _))
        (by linarith [(h.signs s z hmem.1).1])
    exact mul_nonneg (h.lemmaA3_lapse_pos hmem.1).le
      (div_nonneg (by positivity) (mul_nonneg hmem.2.le (h.gap_pos hmem.1).le)))
  simpa [chartLapse, gammaOf, (h.boundary_gauge s ⟨hq.1.1, hq.1.2.1⟩).2.1] using hl

/-- The scalar Cauchy–Schwarz weight has its sharp outer-gap bound. Paper
`e1a0fd5`, second part of `eq:observability-annular-lapse-bounds`, lines 1580–1583. -/
theorem lemmaA3_lapse_square_bound {s t : ℝ}
    (hq : (s, t) ∈ chartInterior (chartCylinder h.g T) S) :
    S.nu s t ^ 2 / (1 - S.mu s t) ≤ (1 - S.mu s s)⁻¹ := by
  have hl := h.lemmaA3_lapse_le_boundary hq
  have hn := h.neg_nu_le_one hq
  have hp := h.lemmaA3_lapse_pos hq.1
  have he : S.nu s t ^ 2 / (1 - S.mu s t) = -S.nu s t * chartLapse S s t := by
    unfold chartLapse gammaOf
    ring
  rw [he]
  exact (mul_le_mul_of_nonneg_right hn hp.le).trans (by simpa using hl)

/-- The integrating factor `L⁻¹/(z-2m)` increases along an annular slice.
Paper `e1a0fd5`, first comparison in `eq:observability-annular-lapse-bounds`,
lines 1576–1583. -/
theorem lemmaA3_lapse_factor_le {s t p : ℝ}
    (hq : (s, t) ∈ chartInterior (chartCylinder h.g T) S)
    (hm : ∀ z ∈ Icc t s, S.m s z ≤ p) (hp : 2 * p < S.r s t) :
    (chartLapse S s t)⁻¹ / (S.r s t - 2 * S.m s t) ≤
      (1 - S.mu s s) / (S.r s t - 2 * S.m s s) := by
  have hseg := h.lemmaA3_out_interior hq
  have hac := h.lemmaA3_radial_ac hq
  have hli := positive_ac_inv hac.2.2.2 (by
    intro z hz
    rw [uIcc_of_le hq.1.2.2.2] at hz
    exact h.lemmaA3_lapse_pos (hseg (show (s, z) ∈ outSeg s t s from ⟨by simp, hz⟩)).1)
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => S.r s t) t s :=
    (LipschitzWith.const _).lipschitzOnWith.absolutelyContinuousOnInterval
  have hden : AbsolutelyContinuousOnInterval (fun z => S.r s t - 2 * S.m s z) t s :=
    hc.sub (hac.2.1.const_mul 2)
  have hdp : ∀ z ∈ uIcc t s, 0 < S.r s t - 2 * S.m s z := by
    intro z hz
    rw [uIcc_of_le hq.1.2.2.2] at hz
    linarith [hm z hz]
  have hdi := positive_ac_inv hden hdp
  have hF : AbsolutelyContinuousOnInterval
      (fun z => (chartLapse S s z)⁻¹ / (S.r s t - 2 * S.m s z)) t s := by
    convert hli.mul hdi using 1
    funext z
    simp only [Pi.mul_apply, div_eq_mul_inv]
  have hM := intervalPrimitive_ae_hasDerivAt hq.1.2.2.2 (fun z hz =>
    h.equations.mass_t s t z hz.1 (fun q hq' =>
      (hseg ⟨hq'.1, hq'.2.1, hq'.2.2.trans hz.2⟩).1))
  have hle := lemmaA3_ac_endpoint_le hq.1.2.2.2 hF (by
    filter_upwards [h.lemmaA3_lapse_ae hq, hM] with z hL hM hz
    have hmem := hseg (show (s, z) ∈ outSeg s t s from ⟨by simp, hz.1.le, hz.2.le⟩)
    have hLp := h.lemmaA3_lapse_pos hmem.1
    have hgap := h.gap_pos hmem.1
    have hDp := hdp z (by simpa [uIcc_of_le hq.1.2.2.2] using ⟨hz.1.le, hz.2.le⟩)
    have hR := h.radius_t_mono hz.1.le
      (h.out_subset ⟨hq.1.1, hq.1.2.1⟩ hq.1.2.2.1 hz.2.le)
    have hm0 : 0 ≤ S.massV s z := by
      unfold SSFields.massV
      exact div_nonneg (mul_nonneg hgap.le (sq_nonneg _))
        (by linarith [(h.signs s z hmem.1).1])
    have hd := ((hL hz).inv hLp.ne').div
      ((hasDerivAt_const z (S.r s t)).sub ((hM hz).const_mul 2)) hDp.ne'
    dsimp only [Pi.sub_apply, Pi.div_apply, Pi.inv_apply] at hd
    have hfun : (fun z => (chartLapse S s z)⁻¹ / (S.r s t - 2 * S.m s z)) =
        ((chartLapse S s)⁻¹ / ((fun _ => S.r s t) - fun z => 2 * S.m s z)) := by
      funext x
      rfl
    rw [hfun, hd.deriv]
    have he :
        (- (chartLapse S s z * (2 * S.massV s z / (S.r s z * (1 - S.mu s z)))) /
          chartLapse S s z ^ 2 * (S.r s t - 2 * S.m s z) -
          (chartLapse S s z)⁻¹ * (0 - 2 * S.massV s z)) /
          (S.r s t - 2 * S.m s z) ^ 2 =
        2 * S.massV s z * (S.r s z - S.r s t) /
          (chartLapse S s z * S.r s z * (1 - S.mu s z) *
            (S.r s t - 2 * S.m s z) ^ 2) := by
      have hrg : S.r s z * (1 - S.mu s z) = S.r s z - 2 * S.m s z := by
        unfold SSFields.mu massRatio
        field_simp [hmem.2.ne']
      have hrgp : 0 < S.r s z - 2 * S.m s z := by
        rw [← hrg]
        exact mul_pos hmem.2 hgap
      unfold SSFields.mu massRatio
      field_simp [hLp.ne', hDp.ne', hmem.2.ne', hrgp.ne']
      ring
    rw [he]
    exact div_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr hR))
      (mul_nonneg (mul_nonneg (mul_nonneg hLp.le hmem.2.le) hgap.le) (sq_nonneg _)))
  have hsb : chartLapse S s s = (1 - S.mu s s)⁻¹ := by
    simp [chartLapse, gammaOf, one_div, (h.boundary_gauge s ⟨hq.1.1, hq.1.2.1⟩).2.1]
  simpa only [hsb, inv_inv] using hle

/-- Sharp lapse and speed bounds on an annulus with uniform mass upper bound.
Paper `e1a0fd5`, lines 1567–1583, `eq:observability-annular-lapse-bounds`.
The mass upper bound is discharged by `mass_flux_bounds`. -/
theorem lemmaA3_annular_lapse_bounds {s t p : ℝ}
    (hq : (s, t) ∈ chartInterior (chartCylinder h.g T) S)
    (hm : ∀ z ∈ Icc t s, S.m s z ≤ p) (hp : 2 * p < S.r s t) :
    1 - 2 * p / S.r s t ≤ -S.nu s t ∧
      (1 - S.mu s t) / (-S.nu s t) ≤
        (1 - S.mu s s) / (1 - 2 * p / S.r s t) := by
  have hf := h.lemmaA3_lapse_factor_le hq hm hp
  have hn : 0 < -S.nu s t := neg_pos.mpr (h.signs s t hq.1).2.1
  have hg := h.gap_pos hq.1
  have hgb := h.gap_pos (h.boundary_mem ⟨hq.1.1, hq.1.2.1⟩)
  have hmb := hm s ⟨hq.1.2.2.2, le_rfl⟩
  have hden : 0 < S.r s t - 2 * S.m s s := by linarith
  have hden' : 0 < S.r s t - 2 * S.m s t := by linarith [hm t ⟨le_rfl, hq.1.2.2.2⟩]
  have he : (chartLapse S s t)⁻¹ / (S.r s t - 2 * S.m s t) =
      1 / (S.r s t * (-S.nu s t)) := by
    unfold chartLapse gammaOf SSFields.mu massRatio
    field_simp [hq.2.ne', (h.signs s t hq.1).2.1.ne, hden'.ne']
  rw [he] at hf
  have hf' := (div_le_div_iff₀ (mul_pos hq.2 hn) hden).mp hf
  have hμb : 1 - S.mu s s ≤ 1 := by linarith [(h.signs s s (h.boundary_mem ⟨hq.1.1, hq.1.2.1⟩)).2.2]
  have hd : 0 < 1 - 2 * p / S.r s t := by
    apply sub_pos.mpr
    exact (div_lt_one hq.2).mpr hp
  constructor
  · have hmul := mul_le_mul_of_nonneg_right hμb (mul_pos hq.2 hn).le
    have hnum : S.r s t - 2 * p ≤ S.r s t * (-S.nu s t) := by linarith
    have he' : 1 - 2 * p / S.r s t = (S.r s t - 2 * p) / S.r s t := by field_simp [hq.2.ne']
    rw [he']
    exact (div_le_iff₀ hq.2).mpr (by simpa [mul_comm] using hnum)
  · apply (div_le_div_iff₀ hn hd).mpr
    have hm0 := h.mass_nonneg hq.1
    have hμ : 0 ≤ S.mu s t := (h.signs s t hq.1).2.2
    have hleft : (1 - S.mu s t) * (S.r s t - 2 * p) ≤ S.r s t - 2 * S.m s s := by
      have hmul := mul_le_mul_of_nonneg_right (show S.r s t - 2 * p ≤ S.r s t - 2 * S.m s s by linarith) hg.le
      have hmul' := mul_le_mul_of_nonneg_right (show 1 - S.mu s t ≤ 1 by linarith) hden.le
      linarith
    have hscaled := mul_le_mul_of_nonneg_right hf' hq.2.le
    have he' : ((1 - S.mu s t) * (1 - 2 * p / S.r s t)) * S.r s t =
        (1 - S.mu s t) * (S.r s t - 2 * p) := by field_simp [hq.2.ne']
    apply (mul_le_mul_iff_left₀ hq.2).mp
    nlinarith [he']

end NormalizedChartData

end AcExtensionPrinciple

end
