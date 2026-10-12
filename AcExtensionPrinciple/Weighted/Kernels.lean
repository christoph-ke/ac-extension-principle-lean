module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Tactic

/-!
# Weighted radial kernels

One-cone helpers for paper commit `e1a0fd5`, `equations.tex`
lines 1139–1223.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory
open scoped ENNReal

/-- The upper half of the late radial expansion comparison, in radius coordinates;
paper `e1a0fd5`, `eq:late-radial-expansion-comparison`, lines 1139–1141. -/
@[expose] def RadialWeightGrowth (w : ℝ → ℝ) (R δ : ℝ) : Prop :=
  ∀ ⦃y x : ℝ⦄, 0 < y → y ≤ x → x ≤ R → w x ≤ w y * (x / y) ^ δ

/-- The power kernel beyond a positive radius; paper `e1a0fd5`,
`equations.tex` lines 1192–1195 and 1217–1223. -/
theorem lintegral_rpow_tail {ρ q : ℝ} (hρ : 0 < ρ) (hq : q < -1) :
    (∫⁻ r in Ioi ρ, ENNReal.ofReal (r ^ q)) =
      ENNReal.ofReal (ρ ^ (q + 1) / (-q - 1)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_rpow_of_lt hq hρ)]
  · rw [integral_Ioi_rpow_of_lt hq hρ]
    congr 1
    rw [show -q - 1 = -(q + 1) by ring, div_neg, neg_div]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact Real.rpow_nonneg (hρ.trans hr).le _

/-- A general weighted tail kernel, including the two kernels in Lemma 3.3;
paper `e1a0fd5`, `equations.tex` lines 1192–1195 and 1217–1223. -/
theorem weighted_rpow_kernel_le {w : ℝ → ℝ} {ρ R δ p : ℝ}
    (hρ : 0 < ρ) (hwρ : 0 ≤ w ρ) (hp : δ + 1 < p)
    (hgrowth : RadialWeightGrowth w R δ) :
    (∫⁻ r in Ioc ρ R, ENNReal.ofReal (w r * r ^ (-p))) ≤
      ENNReal.ofReal (w ρ * ρ ^ (1 - p) / (p - δ - 1)) := by
  have hfactor : 0 ≤ w ρ * ρ ^ (-δ) := by positivity
  calc
    _ ≤ ∫⁻ r in Ioc ρ R,
        ENNReal.ofReal (w ρ * ρ ^ (-δ)) * ENNReal.ofReal (r ^ (δ - p)) := by
      apply setLIntegral_mono' measurableSet_Ioc
      intro r hr
      rw [← ENNReal.ofReal_mul hfactor]
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ (w ρ * (r / ρ) ^ δ) * r ^ (-p) :=
          mul_le_mul_of_nonneg_right (hgrowth hρ hr.1.le hr.2)
            (Real.rpow_nonneg (hρ.trans hr.1).le _)
        _ = _ := by
          rw [Real.div_rpow (hρ.trans hr.1).le hρ.le, Real.rpow_neg hρ.le,
            div_eq_mul_inv]
          rw [show δ - p = δ + -p by ring, Real.rpow_add (hρ.trans hr.1)]
          ring
    _ ≤ ∫⁻ r in Ioi ρ,
        ENNReal.ofReal (w ρ * ρ ^ (-δ)) * ENNReal.ofReal (r ^ (δ - p)) :=
      lintegral_mono_set Ioc_subset_Ioi_self
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_rpow_tail hρ (by linarith), ← ENNReal.ofReal_mul hfactor]
      congr 1
      rw [← mul_div_assoc, mul_assoc, ← Real.rpow_add hρ]
      rw [show -δ + (δ - p + 1) = 1 - p by ring,
        show -(δ - p) - 1 = p - δ - 1 by ring]

/-- The inner L¹ kernel has constant `1/(1-δ)`; paper `e1a0fd5`,
`eq:radial-l1-estimate`, `equations.tex` lines 1217–1223. -/
theorem weighted_inv_sq_kernel_le {w : ℝ → ℝ} {ρ R δ : ℝ}
    (hρ : 0 < ρ) (hwρ : 0 ≤ w ρ) (hδ : δ < 1)
    (hgrowth : RadialWeightGrowth w R δ) :
    (∫⁻ r in Ioc ρ R, ENNReal.ofReal (w r / r ^ 2)) ≤
      ENNReal.ofReal (w ρ / ((1 - δ) * ρ)) := by
  have h := weighted_rpow_kernel_le hρ hwρ (by linarith : δ + 1 < 2) hgrowth
  norm_num [Real.rpow_neg, Real.rpow_neg_one, div_eq_mul_inv] at h ⊢
  convert h using 1
  congr 1
  ring

/-- The transported-datum kernel has constant `1/(3-δ)`; paper `e1a0fd5`,
`equations.tex` lines 1192–1195. -/
theorem weighted_transport_kernel_le {w : ℝ → ℝ} {ρ R δ : ℝ}
    (hρ : 0 < ρ) (hwρ : 0 ≤ w ρ) (hδ : δ < 3)
    (hgrowth : RadialWeightGrowth w R δ) :
    (∫⁻ r in Ioc ρ R, ENNReal.ofReal (w r * ρ ^ 2 / r ^ 4)) ≤
      ENNReal.ofReal (w ρ / ((3 - δ) * ρ)) := by
  have h := weighted_rpow_kernel_le hρ hwρ (by linarith : δ + 1 < 4) hgrowth
  have heq (r : ℝ) : w r * ρ ^ 2 / r ^ 4 = ρ ^ 2 * (w r * r ^ (-(4 : ℝ))) := by
    simp [div_eq_mul_inv]
    ring
  simp_rw [heq, ENNReal.ofReal_mul (sq_nonneg ρ)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine (show ENNReal.ofReal (ρ ^ 2) * _ ≤ ENNReal.ofReal (ρ ^ 2) * _ from
    mul_le_mul le_rfl h zero_le zero_le).trans_eq ?_
  rw [← ENNReal.ofReal_mul (sq_nonneg ρ)]
  congr 1
  norm_num [Real.rpow_neg, div_eq_mul_inv]
  field_simp
  ring

end AcExtensionPrinciple

end
