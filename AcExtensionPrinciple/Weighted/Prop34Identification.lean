module

public import AcExtensionPrinciple.Weighted.Prop34Measure
public import AcExtensionPrinciple.Weighted.Abstract

/-!
# Identification after finite weighted L¹ absorption

Helpers, paper `e1a0fd5`, `eq:remainder-difference-l1` and
`eq:remainder-difference-kato`, `equations.tex` lines 1292–1318.
The integrated Kato bound is explicit and is not asserted to follow merely
from the pointwise energy identity.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped ENNReal

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- A zero weighted L¹ norm identifies the difference almost everywhere.
Paper `e1a0fd5`, lines 1316–1318. Positivity of the weight is derived
from the standing geometry, including the regular axis. -/
theorem weighted_remainder_eq_zero_ae_of_l1_zero
    {u₀ U : ℝ} {W : ℝ × ℝ → ℝ} (hi : ui ≤ u₀) (hU : U < 0)
    (hW : Measurable W) (hzero : weightedRemainderL1 S u₀ U W = 0) :
    W =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)] 0 := by
  obtain ⟨ω, hω, heω⟩ := h.weighted_exists_measurable_remainder_density hi hU
  have hi0 : (∫⁻ p in weightedTruncatedDomain u₀ U,
      ENNReal.ofReal (ω p * |W p|)) = 0 := by
    rw [← hzero]
    apply setLIntegral_congr_fun (measurableSet_weightedTruncatedDomain u₀ U)
    intro p hp
    dsimp only
    rw [← heω hp]
  have hm : Measurable (fun p => ENNReal.ofReal (ω p * |W p|)) := by
    simpa only [Real.norm_eq_abs, Pi.mul_apply] using (hω.mul hW.norm).ennreal_ofReal
  have he := (lintegral_eq_zero_iff' hm.aemeasurable).mp hi0
  filter_upwards [he, ae_restrict_mem (measurableSet_weightedTruncatedDomain u₀ U)]
    with p hp hpmem
  have hpt := weightedTruncatedDomain_subset_triangle hi hU hpmem
  have hpos : 0 < ω p := by
    rw [← heω hpmem]
    exact div_pos (neg_pos.mpr (h.nu_neg hpt))
      (mul_pos (sq_pos_of_pos (sub_pos.mpr (h.mu_bounds hpt).2)) (h.lam_pos hpt))
  have hn : ω p * |W p| ≤ 0 := ENNReal.ofReal_eq_zero.mp hp
  have ha : |W p| = 0 := by nlinarith [abs_nonneg (W p)]
  exact abs_eq_zero.mp ha

/-- Strict absorption of the finite full-domain L¹ norm identifies the
actual and constructed remainders. Paper `e1a0fd5`, lines 1305–1318.
`hKato` is the integrated inequality after the radial L¹ estimate; its
production is proved by `weighted_global_kato_bound` in `Weighted/Prop34GlobalKato.lean`,
using `frozen_ray_kato_integral_bound` from `Weighted/Prop34KatoIntegral.lean`. -/
theorem weighted_remainder_eq_zero_ae_of_kato_absorption
    {u₀ U C ε δ : ℝ} {W : ℝ × ℝ → ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hW : Measurable W)
    (hfinite : weightedRemainderL1 S u₀ U W < ⊤)
    (hKato : (1 - 3 * δ) * (weightedRemainderL1 S u₀ U W).toReal ≤
      C * ε ^ 2 * (weightedRemainderL1 S u₀ U W).toReal)
    (hsmall : C * ε ^ 2 < 1 - 3 * δ) :
    W =ᵐ[volume.restrict (weightedTruncatedDomain u₀ U)] 0 := by
  have hx := remainder_difference_eq_zero ENNReal.toReal_nonneg hKato hsmall
  have hzero : weightedRemainderL1 S u₀ U W = 0 := by
    rw [← ENNReal.ofReal_toReal hfinite.ne, hx, ENNReal.ofReal_zero]
  exact h.weighted_remainder_eq_zero_ae_of_l1_zero hi hU hW hzero

end StandingFull

end AcExtensionPrinciple

end
