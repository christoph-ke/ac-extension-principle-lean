module

public import AcExtensionPrinciple.Weighted.ClassDomain

/-!
# Restoration of the geometric weights

Paper `e1a0fd5`, `equations.tex` lines 1137, 1187,
1215 and 1223. All constants are fixed by the original geometry.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory
open scoped ENNReal

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Measurable remainder-weight extension on a proper triangle. The mass
ratio uses the shared `massRatio` definition, including axis values.
Paper `e1a0fd5`, lines 1148–1152, 1215, 1223. -/
theorem weighted_exists_measurable_remainder_density {u₀ U : ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) :
    ∃ ω : ℝ × ℝ → ℝ, Measurable ω ∧
      EqOn (weightedRemainderDensity S) ω (weightedTruncatedDomain u₀ U) := by
  obtain ⟨r, hr, her⟩ := weighted_exists_measurable_geometry hi hU h.regularCenter.continuous_r
  obtain ⟨m, hm, hem⟩ := weighted_exists_measurable_geometry hi hU h.regularCenter.continuous_m
  obtain ⟨l, hl, hel⟩ := weighted_exists_measurable_geometry hi hU h.regularCenter.continuous_lam
  obtain ⟨n, hn, hen⟩ := weighted_exists_measurable_geometry hi hU h.regularCenter.continuous_nu
  let ω := fun p => (-n p) / ((1 - massRatio (r p) (m p)) ^ 2 * l p)
  refine ⟨ω, hn.neg.div (((measurable_const.sub ((hm.const_mul 2).div hr)).pow_const 2).mul hl), ?_⟩
  intro p hp
  simp only [ω, weightedRemainderDensity, SSFields.mu, ← her hp, ← hem hp, ← hel hp, ← hen hp]

/-- Tonelli for weighted remainder powers on the proper triangle.
Paper `e1a0fd5`, `eq:weighted-remainder-norm`, `eq:radial-l1-estimate`,
lines 1150, 1179–1181, 1215, 1223. -/
theorem weighted_remainder_power_eq_iterated {u₀ U : ℝ} {W : ℝ × ℝ → ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hW : Measurable W) (k : ℕ) :
    (∫⁻ p in weightedTruncatedDomain u₀ U,
      ENNReal.ofReal (weightedRemainderDensity S p * |W p| ^ k)) =
      ∫⁻ u in Icc u₀ U, ∫⁻ v in Ioc u 0,
        ENNReal.ofReal (weightedRemainderDensity S (u, v) * |W (u, v)| ^ k) := by
  obtain ⟨ω, hω, heω⟩ := h.weighted_exists_measurable_remainder_density hi hU
  calc
    _ = ∫⁻ p in weightedTruncatedDomain u₀ U, ENNReal.ofReal (ω p * |W p| ^ k) := by
      apply setLIntegral_congr_fun (measurableSet_weightedTruncatedDomain u₀ U)
      intro p hp
      dsimp only
      rw [heω hp]
    _ = ∫⁻ u in Icc u₀ U, ∫⁻ v in Ioc u 0, ENNReal.ofReal (ω (u, v) * |W (u, v)| ^ k) :=
      weighted_triangle_lintegral_eq u₀ U (hω.mul (hW.norm.pow_const k)).ennreal_ofReal
    _ = _ := by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro u hu
      apply setLIntegral_congr_fun measurableSet_Ioc
      intro v hv
      dsimp only
      rw [← heω ⟨hu.1, hu.2, hv.1.le, hv.2⟩]

/-- Restoring the source's inverse squared mass-gap costs a fixed factor.
Paper `e1a0fd5`, lines 1187, 1215. -/
theorem weighted_source_sq_le_base {p : ℝ × ℝ} (hp : p ∈ pastTriangle ui) (F : ℝ) :
    ENNReal.ofReal (weightedSourceDensity S p * |F| ^ 2) ≤
      ENNReal.ofReal ((weightedGapConstant ui S ^ 2)⁻¹) *
        ENNReal.ofReal ((-S.nu p.1 p.2) * S.lam p.1 p.2 * |F| ^ 2) := by
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (weightedGapConstant ui S ^ 2)⁻¹)]
  apply ENNReal.ofReal_le_ofReal
  have hn := (neg_pos.mpr (h.nu_neg hp)).le
  have hl := (h.lam_pos hp).le
  have he : weightedSourceDensity S p * |F| ^ 2 =
      ((-S.nu p.1 p.2) * S.lam p.1 p.2 * |F| ^ 2) * ((1 - S.mu p.1 p.2) ^ 2)⁻¹ := by
    unfold weightedSourceDensity
    ring
  rw [he, mul_comm ((weightedGapConstant ui S ^ 2)⁻¹)]
  exact mul_le_mul_of_nonneg_left (h.weighted_gap_factor_bounds hp).2 (by positivity)

/-- The original remainder weight dominates the weight with the gap removed.
Paper `e1a0fd5`, lines 1187, 1215. -/
theorem weighted_remainder_base_le {p : ℝ × ℝ} (hp : p ∈ pastTriangle ui) (W : ℝ) (k : ℕ) :
    ENNReal.ofReal ((-S.nu p.1 p.2) / S.lam p.1 p.2 * |W| ^ k) ≤
      ENNReal.ofReal (weightedRemainderDensity S p * |W| ^ k) := by
  apply ENNReal.ofReal_le_ofReal
  have hn := (neg_pos.mpr (h.nu_neg hp)).le
  have hl := h.lam_pos hp
  have he : weightedRemainderDensity S p * |W| ^ k =
      ((-S.nu p.1 p.2) / S.lam p.1 p.2 * |W| ^ k) * ((1 - S.mu p.1 p.2) ^ 2)⁻¹ := by
    unfold weightedRemainderDensity
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [he]
  exact le_mul_of_one_le_right (by positivity) (h.weighted_gap_factor_bounds hp).1

/-- The L¹ source weight is bounded by the λ-weighted cone weight, with
fixed global constants. Paper `e1a0fd5`, lines 1217–1223. -/
theorem weighted_source_l1_le_base {p : ℝ × ℝ} (hp : p ∈ pastTriangle ui) (F : ℝ) :
    ENNReal.ofReal ((-S.nu p.1 p.2) / (1 - S.mu p.1 p.2) ^ 2 * |F|) ≤
      ENNReal.ofReal ((weightedGapConstant ui S ^ 2)⁻¹ / Real.exp (-Bstar ui S)) *
        ENNReal.ofReal ((-S.nu p.1 p.2) * S.lam p.1 p.2 * |F|) := by
  have hn := (neg_pos.mpr (h.nu_neg hp)).le
  have hl := h.lam_pos hp
  have hc := Real.exp_pos (-Bstar ui S)
  have hli : (S.lam p.1 p.2)⁻¹ ≤ (Real.exp (-Bstar ui S))⁻¹ :=
    inv_anti₀ hc (h.lam_bounds hp).1
  have hgi := (h.weighted_gap_factor_bounds hp).2
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have he : (-S.nu p.1 p.2) / (1 - S.mu p.1 p.2) ^ 2 * |F| =
      ((-S.nu p.1 p.2) * S.lam p.1 p.2 * |F|) *
        (((1 - S.mu p.1 p.2) ^ 2)⁻¹ * (S.lam p.1 p.2)⁻¹) := by field_simp
  rw [he, div_eq_mul_inv, mul_comm ((weightedGapConstant ui S ^ 2)⁻¹ * _)]
  exact mul_le_mul_of_nonneg_left (mul_le_mul hgi hli (by positivity) (by positivity))
    (by positivity)

/-- The L¹ remainder weight also dominates the weight with λ omitted,
since λ ≤ 1. Paper `e1a0fd5`, lines 1217–1223. -/
theorem weighted_remainder_l1_base_le {p : ℝ × ℝ} (hp : p ∈ pastTriangle ui) (W : ℝ) :
    ENNReal.ofReal ((-S.nu p.1 p.2) * |W|) ≤
      ENNReal.ofReal (weightedRemainderDensity S p * |W|) := by
  have hb := h.weighted_remainder_base_le hp W 1
  simp only [pow_one] at hb
  refine (ENNReal.ofReal_le_ofReal ?_).trans hb
  have hn := (neg_pos.mpr (h.nu_neg hp)).le
  have hl := h.lam_pos hp
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hl).mpr
  exact mul_le_of_le_one_right (by positivity) (h.lam_bounds hp).2

end StandingFull

end AcExtensionPrinciple

end
