module

public import AcExtensionPrinciple.Weighted.ClassConeData

/-!
# Weighted estimates for the actual radial operator on a cone

Paper `e1a0fd5`, `eq:remainder-radial-estimate` and
`eq:radial-l1-estimate`, `equations.tex` lines 1204–1223. No inverse
chart, regularity, or Hardy bound is assumed of the solution.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory
open scoped ENNReal

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The actual cone L² estimate, before restoring the mass-gap factors.
Paper `e1a0fd5`, `eq:remainder-radial-estimate`, lines 1204–1215. -/
theorem weighted_cone_radial_l2_of_smallness {u δ ε : ℝ} {W : ℝ × ℝ → ℝ}
    (hu : ui ≤ u) (hu0 : u < 0) (hW : Measurable W) (hδ : δ < 3) (_hε : 0 ≤ ε)
    (hsmall : ∀ v ∈ Ioc u 0, S.mu u v / (1 - S.mu u v) ≤ δ)
    (hamp : ∀ v ∈ Ioc u 0, |weightedIncomingAmplitude S u v| ≤ ε) :
    (∫⁻ v in Ioc u 0, ENNReal.ofReal
      ((-S.nu u v) * S.lam u v * |weightedRadialOperator S W (u, v)| ^ 2)) ≤
      ENNReal.ofReal ((2 / (3 - δ)) ^ 2 * ε ^ 2) *
        ∫⁻ v in Ioc u 0, ENNReal.ofReal ((-S.nu u v) / S.lam u v * |W (u, v)| ^ 2) := by
  obtain ⟨D⟩ := h.weighted_exists_cone_data hu hu0 hW hsmall
  have hrad := cone_weighted_radial_l2_le (h.r_pos ⟨hu, hu0, hu0.le, le_rfl⟩ hu0)
    D.measurable_f.aemeasurable D.weight_pos D.weight_mono hδ D.weight_growth
  have hl : (∫⁻ v in Ioc u 0, ENNReal.ofReal
      ((-S.nu u v) * S.lam u v * |weightedRadialOperator S W (u, v)| ^ 2)) =
      ∫⁻ x in Ioc 0 (S.r u 0), ENNReal.ofReal (D.w x * |radialOperator D.f x| ^ 2) := by
    rw [← h.weighted_lintegral_radius_pullback hu hu0 ⟨hu0.le, le_rfl⟩]
    apply setLIntegral_congr_fun measurableSet_Ioc
    intro v hv
    dsimp only
    rw [D.weight_eq v hv, D.operator_eq v hv,
      ← ENNReal.ofReal_mul (h.lam_pos (p := (u, v)) ⟨hu, hu0, hv.1.le, hv.2⟩).le]
    congr 1
    ring
  have hr : (∫⁻ x in Ioc 0 (S.r u 0), ENNReal.ofReal (D.w x * |D.f x| ^ 2)) ≤
      ENNReal.ofReal (ε ^ 2) *
        ∫⁻ v in Ioc u 0, ENNReal.ofReal ((-S.nu u v) / S.lam u v * |W (u, v)| ^ 2) := by
    rw [← h.weighted_lintegral_radius_pullback hu hu0 ⟨hu0.le, le_rfl⟩,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply setLIntegral_mono' measurableSet_Ioc
    intro v hv
    have hp : (u, v) ∈ pastTriangle ui := ⟨hu, hu0, hv.1.le, hv.2⟩
    have hlp := h.lam_pos hp
    have hnp := neg_pos.mpr (h.nu_neg hp)
    rw [D.weight_eq v hv, D.datum_eq v hv,
      ← ENNReal.ofReal_mul hlp.le, ← ENNReal.ofReal_mul (sq_nonneg ε)]
    apply ENNReal.ofReal_le_ofReal
    have ha : |weightedIncomingAmplitude S u v| ^ 2 ≤ ε ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) (hamp v hv) 2
    rw [abs_div, abs_mul, abs_of_pos hlp, div_pow, mul_pow]
    have he : S.lam u v * ((-S.nu u v) *
        (|weightedIncomingAmplitude S u v| ^ 2 * |W (u, v)| ^ 2 / S.lam u v ^ 2)) =
        ((-S.nu u v) / S.lam u v * |W (u, v)| ^ 2) *
          |weightedIncomingAmplitude S u v| ^ 2 := by field_simp
    rw [he, mul_comm (ε ^ 2)]
    exact mul_le_mul_of_nonneg_left ha (by positivity)
  rw [hl]
  refine hrad.trans ((mul_le_mul le_rfl hr zero_le zero_le).trans_eq ?_)
  rw [← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg _)]

/-- The λ-weighted L¹ cone estimate. Converting to the paper's du dv
weight uses the uniform λ bounds. Paper `e1a0fd5`,
`eq:radial-l1-estimate`, lines 1217–1223. -/
theorem weighted_cone_radial_l1_of_smallness {u δ ε : ℝ} {W : ℝ × ℝ → ℝ}
    (hu : ui ≤ u) (hu0 : u < 0) (hW : Measurable W) (hδ : δ < 1) (hε : 0 ≤ ε)
    (hsmall : ∀ v ∈ Ioc u 0, S.mu u v / (1 - S.mu u v) ≤ δ)
    (hamp : ∀ v ∈ Ioc u 0, |weightedIncomingAmplitude S u v| ≤ ε) :
    (∫⁻ v in Ioc u 0, ENNReal.ofReal
      ((-S.nu u v) * S.lam u v * |weightedRadialOperator S W (u, v)|)) ≤
      ENNReal.ofReal (ε / (1 - δ)) *
        ∫⁻ v in Ioc u 0, ENNReal.ofReal ((-S.nu u v) * |W (u, v)|) := by
  obtain ⟨D⟩ := h.weighted_exists_cone_data hu hu0 hW hsmall
  have hrad := cone_weighted_radial_l1_le (h.r_pos ⟨hu, hu0, hu0.le, le_rfl⟩ hu0)
    D.measurable_f.aemeasurable D.weight_pos D.weight_mono hδ D.weight_growth
  have hl : (∫⁻ v in Ioc u 0, ENNReal.ofReal
      ((-S.nu u v) * S.lam u v * |weightedRadialOperator S W (u, v)|)) =
      ∫⁻ x in Ioc 0 (S.r u 0), ENNReal.ofReal (D.w x * |radialOperator D.f x|) := by
    rw [← h.weighted_lintegral_radius_pullback hu hu0 ⟨hu0.le, le_rfl⟩]
    apply setLIntegral_congr_fun measurableSet_Ioc
    intro v hv
    dsimp only
    rw [D.weight_eq v hv, D.operator_eq v hv,
      ← ENNReal.ofReal_mul (h.lam_pos (p := (u, v)) ⟨hu, hu0, hv.1.le, hv.2⟩).le]
    congr 1
    ring
  have hr : (∫⁻ x in Ioc 0 (S.r u 0), ENNReal.ofReal (D.w x * |D.f x|)) ≤
      ENNReal.ofReal ε *
        ∫⁻ v in Ioc u 0, ENNReal.ofReal ((-S.nu u v) * |W (u, v)|) := by
    rw [← h.weighted_lintegral_radius_pullback hu hu0 ⟨hu0.le, le_rfl⟩,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply setLIntegral_mono' measurableSet_Ioc
    intro v hv
    have hp : (u, v) ∈ pastTriangle ui := ⟨hu, hu0, hv.1.le, hv.2⟩
    have hlp := h.lam_pos hp
    have hnp := neg_pos.mpr (h.nu_neg hp)
    rw [D.weight_eq v hv, D.datum_eq v hv,
      ← ENNReal.ofReal_mul hlp.le, ← ENNReal.ofReal_mul hε,
      abs_div, abs_mul, abs_of_pos hlp]
    apply ENNReal.ofReal_le_ofReal
    have he : S.lam u v * ((-S.nu u v) *
        (|weightedIncomingAmplitude S u v| * |W (u, v)| / S.lam u v)) =
        ((-S.nu u v) * |W (u, v)|) * |weightedIncomingAmplitude S u v| := by
      field_simp
    rw [he, mul_comm ε]
    exact mul_le_mul_of_nonneg_left (hamp v hv) (by positivity)
  rw [hl]
  refine hrad.trans ((mul_le_mul le_rfl hr zero_le zero_le).trans_eq ?_)
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / (1 - δ))]
  congr 2
  ring

end StandingFull

end AcExtensionPrinciple

end
