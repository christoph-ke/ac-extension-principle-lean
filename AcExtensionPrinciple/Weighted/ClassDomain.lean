module

public import AcExtensionPrinciple.Weighted.ClassNorms
public import AcExtensionPrinciple.GeometricBounds.IncomingFlux

/-!
# Tonelli on the proper triangular domain

Paper `e1a0fd5`, `equations.tex` lines 1148–1181,
1215 and 1223. The inequality version requires no measurability of the
operator's output. The input densities have measurable representatives
from the continuous geometric fields and measurable data.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory
open scoped ENNReal

/-- Write the triangular integral as iterated cone integrals. The lower
integral inequality remains valid for arbitrary integrands.
Paper `e1a0fd5`, `eq:weighted-truncated-domain`, line 1148. -/
theorem weighted_triangle_lintegral_le (u₀ U : ℝ) (F : ℝ × ℝ → ℝ≥0∞) :
    (∫⁻ p in weightedTruncatedDomain u₀ U, F p) ≤
      ∫⁻ u in Icc u₀ U, ∫⁻ v in Ioc u 0, F (u, v) := by
  classical
  let H := (weightedTruncatedDomain u₀ U).indicator F
  have he (u : ℝ) : (∫⁻ v, H (u, v)) =
      (Icc u₀ U).indicator (fun u => ∫⁻ v in Ioc u 0, F (u, v)) u := by
    by_cases hu : u ∈ Icc u₀ U
    · rw [indicator_of_mem hu]
      have he' : (fun v => H (u, v)) = (Icc u 0).indicator (fun v => F (u, v)) := by
        funext v
        simp [H, weightedTruncatedDomain, indicator, hu.1, hu.2]
      rw [he', lintegral_indicator measurableSet_Icc, ← restrict_Ioc_eq_restrict_Icc]
    · rw [indicator_of_notMem hu]
      have he' : (fun v => H (u, v)) = 0 := by
        funext v
        simp [H, weightedTruncatedDomain, indicator]
        tauto
      rw [he']
      change (∫⁻ _v : ℝ, (0 : ℝ≥0∞)) = 0
      simp
  rw [← lintegral_indicator (measurableSet_weightedTruncatedDomain u₀ U),
    Measure.volume_eq_prod]
  refine (lintegral_prod_le H).trans_eq ?_
  simp_rw [he]
  exact lintegral_indicator measurableSet_Icc _

/-- Tonelli equality for a measurable triangular integrand. Paper `e1a0fd5`,
`eq:weighted-truncated-domain`, line 1148, integration at lines 1215, 1223. -/
theorem weighted_triangle_lintegral_eq (u₀ U : ℝ) {F : ℝ × ℝ → ℝ≥0∞}
    (hF : Measurable F) :
    (∫⁻ p in weightedTruncatedDomain u₀ U, F p) =
      ∫⁻ u in Icc u₀ U, ∫⁻ v in Ioc u 0, F (u, v) := by
  classical
  let H := (weightedTruncatedDomain u₀ U).indicator F
  have hH : Measurable H := hF.indicator (measurableSet_weightedTruncatedDomain u₀ U)
  have he (u : ℝ) : (∫⁻ v, H (u, v)) =
      (Icc u₀ U).indicator (fun u => ∫⁻ v in Ioc u 0, F (u, v)) u := by
    by_cases hu : u ∈ Icc u₀ U
    · rw [indicator_of_mem hu]
      have he' : (fun v => H (u, v)) = (Icc u 0).indicator (fun v => F (u, v)) := by
        funext v
        simp [H, weightedTruncatedDomain, indicator, hu.1, hu.2]
      rw [he', lintegral_indicator measurableSet_Icc, ← restrict_Ioc_eq_restrict_Icc]
    · rw [indicator_of_notMem hu]
      have he' : (fun v => H (u, v)) = 0 := by
        funext v
        simp [H, weightedTruncatedDomain, indicator]
        tauto
      rw [he']
      change (∫⁻ _v : ℝ, (0 : ℝ≥0∞)) = 0
      simp
  rw [← lintegral_indicator (measurableSet_weightedTruncatedDomain u₀ U),
    Measure.volume_eq_prod, lintegral_prod _ hH.aemeasurable]
  simp_rw [he]
  exact lintegral_indicator measurableSet_Icc _

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

omit h in
/-- Continuous geometric fields admit measurable extensions from each
proper truncated domain. Paper `e1a0fd5`, lines 1148–1152, 1187, 1215, 1223. -/
theorem weighted_exists_measurable_geometry {u₀ U : ℝ} {f : ℝ × ℝ → ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hf : ContinuousOn f (pastTriangle ui)) :
    ∃ F : ℝ × ℝ → ℝ, Measurable F ∧ EqOn f F (weightedTruncatedDomain u₀ U) := by
  classical
  let D := weightedTruncatedDomain u₀ U
  let F := D.piecewise f (fun _ => 0)
  refine ⟨F, (hf.mono (weightedTruncatedDomain_subset_triangle hi hU)).measurable_piecewise
    continuousOn_const (measurableSet_weightedTruncatedDomain u₀ U), ?_⟩
  intro p hp
  simp [F, D, hp]

/-- The fixed positive mass-gap constant used to restore the weights.
Paper `e1a0fd5`, lines 1137 and 1187; `eq:gap-from-kappa`. -/
@[expose] noncomputable def weightedGapConstant (ui : ℝ) (S : SSFields) : ℝ :=
  initialGap ui S * Real.exp (-Bstar ui S)

/-- The mass-gap constant is positive. Paper `e1a0fd5`,
`eq:gap-from-kappa`, and lines 1137, 1187. -/
theorem weightedGapConstant_pos : 0 < weightedGapConstant ui S :=
  mul_pos h.initialGap_pos (Real.exp_pos _)

/-- The inverse squared gap is bounded by a constant fixed before u₀, ε, U.
Paper `e1a0fd5`, lines 1137, 1187, 1215, 1223. -/
theorem weighted_gap_factor_bounds {p : ℝ × ℝ} (hp : p ∈ pastTriangle ui) :
    1 ≤ ((1 - S.mu p.1 p.2) ^ 2)⁻¹ ∧
      ((1 - S.mu p.1 p.2) ^ 2)⁻¹ ≤ (weightedGapConstant ui S ^ 2)⁻¹ := by
  have hg : 0 < 1 - S.mu p.1 p.2 := sub_pos.mpr (h.mu_bounds hp).2
  have hle : 1 - S.mu p.1 p.2 ≤ 1 := by linarith [(h.mu_bounds hp).1]
  have hl := h.mass_gap_lower hp
  constructor
  · rw [← one_div]
    apply (le_div_iff₀ (sq_pos_of_pos hg)).mpr
    nlinarith [sq_nonneg (1 - (1 - S.mu p.1 p.2))]
  · exact inv_anti₀ (sq_pos_of_pos h.weightedGapConstant_pos)
      (pow_le_pow_left₀ h.weightedGapConstant_pos.le hl 2)

end StandingFull

end AcExtensionPrinciple

end
