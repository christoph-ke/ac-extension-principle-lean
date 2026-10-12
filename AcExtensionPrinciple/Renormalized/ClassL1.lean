module

public import AcExtensionPrinciple.Renormalized.ClassConeBounds
public import AcExtensionPrinciple.Renormalized.ClassRemainder

/-!
# Renormalized local L¹ bound

Paper `e1a0fd5`, `equations.tex` lines 1072–1078.
The helper takes precisely the two derivative/Hardy majorants used by
the paper. It does not assume square integrability of the initial datum.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- The cubic renormalization has the paper's two L¹ majorants.
Paper `e1a0fd5`, `eq:renormalized-local-l1`, lines 1072–1075. -/
theorem renormalized_derivative_abs_le {mu lam r q A M : ℝ}
    (hmu0 : 0 ≤ mu) (hmu1 : mu < 1) (hl : 0 < lam) (hr : 0 < r)
    (hA : |A| ≤ M) :
    |(1 - mu) * lam * (q - A ^ 3 / r)| ≤
      lam * |q| + M ^ 2 * (lam * |A| / r) := by
  have hM := (abs_nonneg A).trans hA
  have hsq : |A| ^ 2 ≤ M ^ 2 := by
    simpa only [pow_two] using mul_self_le_mul_self (abs_nonneg A) hA
  have hc : |A| ^ 3 ≤ M ^ 2 * |A| := by
    nlinarith [mul_le_mul_of_nonneg_right hsq (abs_nonneg A)]
  calc
    _ = (1 - mu) * lam * |q - A ^ 3 / r| := by
      rw [abs_mul, abs_mul, abs_of_pos (sub_pos.mpr hmu1), abs_of_pos hl]
    _ ≤ lam * |q - A ^ 3 / r| := by
      have hm : (1 - mu) * lam ≤ lam := by nlinarith
      exact mul_le_mul_of_nonneg_right hm (abs_nonneg _)
    _ ≤ lam * (|q| + |A ^ 3 / r|) :=
      mul_le_mul_of_nonneg_left (abs_sub _ _) hl.le
    _ = lam * (|q| + |A| ^ 3 / r) := by rw [abs_div, abs_pow, abs_of_pos hr]
    _ ≤ lam * (|q| + M ^ 2 * |A| / r) := by gcongr
    _ = _ := by ring

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Exact cone L¹ estimate after the Hardy and AC derivative bounds.
Paper `e1a0fd5`, `eq:renormalized-local-l1`, lines 1072–1075.
`hqV` is the integral-of-absolute-derivative bound; `hHardy` is the
Hardy bound pulled back using `dr = λ dv`. Measurability comes from
the AC datum derivative and the continuous expansion. -/
theorem renormalized_local_l1_of_hardy {q : ℝ → ℝ → ℝ} {u M : ℝ}
    (hu : ui ≤ u) (hu0 : u < 0)
    (hA : ∀ v ∈ Ioc u 0, |S.r u v / S.lam u v * S.dvphi u v| ≤ M)
    (hmeas : AEMeasurable (fun v => ENNReal.ofReal (S.lam u v * |q u v|))
      (volume.restrict (Ioc u 0)))
    (hqV : (∫⁻ v in Ioc u 0, ENNReal.ofReal (S.lam u v * |q u v|)) ≤ S.outgoingVariation u)
    (hHardy : (∫⁻ v in Ioc u 0,
      ENNReal.ofReal (S.lam u v * |S.r u v / S.lam u v * S.dvphi u v| / S.r u v)) ≤
        S.outgoingVariation u) :
    (∫⁻ v in Ioc u 0, ENNReal.ofReal |S.renormalizedDerivative q u v|) ≤
      ENNReal.ofReal (1 + M ^ 2) * S.outgoingVariation u := by
  calc
    _ ≤ ∫⁻ v in Ioc u 0,
        ENNReal.ofReal (S.lam u v * |q u v|) + ENNReal.ofReal (M ^ 2) *
          ENNReal.ofReal (S.lam u v * |S.r u v / S.lam u v * S.dvphi u v| / S.r u v) := by
      apply setLIntegral_mono' measurableSet_Ioc
      intro v hv
      have hp : (u, v) ∈ pastTriangle ui := ⟨hu, hu0, hv.1.le, hv.2⟩
      have hl := h.lam_pos hp
      have hr := h.r_pos hp hv.1
      have hb := renormalized_derivative_abs_le (h.mu_bounds hp).1 (h.mu_bounds hp).2
        hl hr (hA v hv) (q := q u v)
      change ENNReal.ofReal |(1 - S.mu u v) * S.lam u v *
        (q u v - (S.r u v / S.lam u v * S.dvphi u v) ^ 3 / S.r u v)| ≤ _
      calc
        _ ≤ ENNReal.ofReal (S.lam u v * |q u v| +
            M ^ 2 * (S.lam u v * |S.r u v / S.lam u v * S.dvphi u v| / S.r u v)) :=
          ENNReal.ofReal_le_ofReal hb
        _ = _ := by rw [ENNReal.ofReal_add (mul_nonneg hl.le (abs_nonneg _))
          (mul_nonneg (sq_nonneg M) (div_nonneg (mul_nonneg hl.le (abs_nonneg _)) hr.le)),
          ENNReal.ofReal_mul (sq_nonneg M)]
    _ = (∫⁻ v in Ioc u 0, ENNReal.ofReal (S.lam u v * |q u v|)) + ENNReal.ofReal (M ^ 2) *
        (∫⁻ v in Ioc u 0,
          ENNReal.ofReal (S.lam u v * |S.r u v / S.lam u v * S.dvphi u v| / S.r u v)) := by
      rw [lintegral_add_left' hmeas, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ S.outgoingVariation u + ENNReal.ofReal (M ^ 2) * S.outgoingVariation u := by gcongr
    _ = _ := by
      rw [ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1) (sq_nonneg M), ENNReal.ofReal_one]
      ring

/-- Finite cone variation converts the renormalized L¹ bound to genuine
Bochner integrability once measurability is known. Paper `e1a0fd5`,
`eq:renormalized-local-l1`, lines 1072–1078. -/
theorem renormalized_integrable_of_l1_bound {q : ℝ → ℝ → ℝ} {u C : ℝ}
    (hu : ui ≤ u) (hu0 : u < 0)
    (hmeas : AEStronglyMeasurable (S.renormalizedDerivative q u) (volume.restrict (Ioc u 0)))
    (hbound : (∫⁻ v in Ioc u 0, ENNReal.ofReal |S.renormalizedDerivative q u v|) ≤
      ENNReal.ofReal C * S.outgoingVariation u) :
    IntegrableOn (S.renormalizedDerivative q u) (Ioc u 0) := by
  refine ⟨hmeas, hasFiniteIntegral_iff_enorm.mpr ?_⟩
  simp only [Real.enorm_eq_ofReal_abs]
  exact hbound.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (lt_top_iff_ne_top.mpr (h.outgoingVariation_ne_top hu hu0)))

end StandingFull

end AcExtensionPrinciple

end
