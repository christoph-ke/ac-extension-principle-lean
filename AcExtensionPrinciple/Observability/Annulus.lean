module

public import AcExtensionPrinciple.Observability.Algebra
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Annular travel time and exponent

Computations from paper `e1a0fd5`, `equations.tex` lines 1613–1621,
1631 (`eq:observability-annular-exponent`). The parameter `p` is the
nonnegative mass upper bound `M₊`.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory

/-- Exact annular travel time; paper `e1a0fd5`, `equations.tex` line 1631. -/
theorem annular_travel_integral {p a b : ℝ} (hp : 0 ≤ p) (ha : 2 * p < a)
    (hab : a ≤ b) :
    (∫ r in a..b, 1 / (1 - 2 * p / r)) =
      (b - a) + 2 * p * Real.log ((b - 2 * p) / (a - 2 * p)) := by
  have ha0 : 0 < a := by linarith
  have hder (r : ℝ) (hr : r ∈ uIcc a b) :
      HasDerivAt (fun r ↦ r + 2 * p * Real.log (r - 2 * p))
        (1 / (1 - 2 * p / r)) r := by
    rw [uIcc_of_le hab] at hr
    have hg : 0 < r - 2 * p := by linarith [hr.1]
    have hr0 : 0 < r := ha0.trans_le hr.1
    convert (hasDerivAt_id r).add
      ((((hasDerivAt_id r).sub_const (2 * p)).log hg.ne').const_mul (2 * p)) using 1
    · rfl
    · simp only [id_eq]
      field_simp
      ring
  have hi : IntervalIntegrable (fun r ↦ 1 / (1 - 2 * p / r)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.div
    · exact continuousOn_const.sub (continuousOn_const.div continuousOn_id (by
        intro r hr
        rw [uIcc_of_le hab] at hr
        exact (ha0.trans_le hr.1).ne'))
    · intro r hr
      rw [uIcc_of_le hab] at hr
      have hr0 : 0 < r := ha0.trans_le hr.1
      have hg : 0 < r - 2 * p := by linarith [hr.1]
      have heq : 1 - 2 * p / r = (r - 2 * p) / r := by field_simp
      rw [heq]
      exact (div_pos hg hr0).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder hi,
    Real.log_div (by linarith : b - 2 * p ≠ 0) (by linarith : a - 2 * p ≠ 0)]
  ring

/-- Exact majorant for the annular exponent; paper `e1a0fd5`,
`eq:observability-annular-exponent`, lines 1613–1621. -/
theorem annular_exponent_majorant_integral {p a b : ℝ} (ha : 2 * p < a)
    (hab : a ≤ b) :
    (∫ r in a..b, 1 / (r - 2 * p) + 2 * p / (r - 2 * p) ^ 2) =
      Real.log ((b - 2 * p) / (a - 2 * p)) +
        2 * p * (1 / (a - 2 * p) - 1 / (b - 2 * p)) := by
  have hder (r : ℝ) (hr : r ∈ uIcc a b) :
      HasDerivAt (fun r ↦ Real.log (r - 2 * p) - 2 * p / (r - 2 * p))
        (1 / (r - 2 * p) + 2 * p / (r - 2 * p) ^ 2) r := by
    rw [uIcc_of_le hab] at hr
    have hg : r - 2 * p ≠ 0 := by linarith [hr.1]
    convert (((hasDerivAt_id r).sub_const (2 * p)).log hg).sub
      ((hasDerivAt_const r (2 * p)).div ((hasDerivAt_id r).sub_const (2 * p)) hg)
      using 1
    · rfl
    · simp
      field_simp
      ring
  have hi : IntervalIntegrable
      (fun r ↦ 1 / (r - 2 * p) + 2 * p / (r - 2 * p) ^ 2) volume a b := by
    apply ContinuousOn.intervalIntegrable
    have hn : ∀ r ∈ uIcc a b, r - 2 * p ≠ 0 := by
      intro r hr
      rw [uIcc_of_le hab] at hr
      linarith [hr.1]
    exact (continuousOn_const.div (continuousOn_id.sub continuousOn_const) hn).add
      (continuousOn_const.div ((continuousOn_id.sub continuousOn_const).pow 2)
        (by intro r hr; exact pow_ne_zero _ (hn r hr)))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder hi,
    Real.log_div (by linarith : b - 2 * p ≠ 0) (by linarith : a - 2 * p ≠ 0)]
  ring

/-- Endpoint estimate in the annular exponent, including its logarithmic
coefficient; paper `e1a0fd5`, `eq:observability-annular-exponent`, lines 1613–1621. -/
theorem annular_exponent_endpoint_le {p a b D : ℝ} (hp : 0 ≤ p) (hD : 0 < D)
    (hgap : D ≤ a - 2 * p) (hab : a ≤ b) :
    2 * (∫ r in a..b, 1 / (r - 2 * p) + 2 * p / (r - 2 * p) ^ 2) ≤
      2 * Real.log (b / D) + 4 * p / D := by
  have ha : 2 * p < a := by linarith
  have hb : 0 < b := by linarith
  have hb' : 0 < b - 2 * p := by linarith
  have hquot : (b - 2 * p) / (a - 2 * p) ≤ b / D := by
    calc
      _ ≤ b / (a - 2 * p) := div_le_div_of_nonneg_right (by linarith) (by linarith)
      _ ≤ b / D := div_le_div_of_nonneg_left hb.le hD hgap
  have hlog := Real.log_le_log (div_pos hb' (by linarith)) hquot
  have hinv := one_div_le_one_div_of_le hD hgap
  have hinv' : 0 ≤ 1 / (b - 2 * p) := by positivity
  rw [annular_exponent_majorant_integral ha hab]
  have hm := mul_le_mul_of_nonneg_left hinv hp
  have hm' := mul_nonneg hp hinv'
  simp only [div_eq_mul_inv, one_mul] at *
  nlinarith

/-- Both displayed comparisons of the annular exponent; paper `e1a0fd5`,
`eq:observability-annular-exponent`, lines 1613–1621. Set `D = δ₀M`. -/
theorem annular_exponent_integral_le {p a b D : ℝ} (hp : 0 ≤ p) (hD : 0 < D)
    (hgap : D ≤ a - 2 * p) (hab : a ≤ b) :
    2 * (∫ r in a..b, (r⁻¹ - b⁻¹) / (1 - 2 * p / r) ^ 2) ≤
      2 * (∫ r in a..b, 1 / (r - 2 * p) + 2 * p / (r - 2 * p) ^ 2) ∧
    2 * (∫ r in a..b, (r⁻¹ - b⁻¹) / (1 - 2 * p / r) ^ 2) ≤
      2 * Real.log (b / D) + 4 * p / D := by
  have ha : 2 * p < a := by linarith
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := ha0.trans_le hab
  have hn : ∀ r ∈ uIcc a b, r ≠ 0 := by
    intro r hr
    rw [uIcc_of_le hab] at hr
    exact (ha0.trans_le hr.1).ne'
  have hng : ∀ r ∈ uIcc a b, r - 2 * p ≠ 0 := by
    intro r hr
    rw [uIcc_of_le hab] at hr
    linarith [hr.1]
  have hnd : ∀ r ∈ uIcc a b, 1 - 2 * p / r ≠ 0 := by
    intro r hr
    have heq : 1 - 2 * p / r = (r - 2 * p) / r := by field_simp [hn r hr]
    rw [heq]
    exact div_ne_zero (hng r hr) (hn r hr)
  have hf : IntervalIntegrable
      (fun r ↦ (r⁻¹ - b⁻¹) / (1 - 2 * p / r) ^ 2) volume a b := by
    apply ContinuousOn.intervalIntegrable
    exact ((continuousOn_id.inv₀ hn).sub continuousOn_const).div
      ((continuousOn_const.sub (continuousOn_const.div continuousOn_id hn)).pow 2)
      (by intro r hr; exact pow_ne_zero _ (hnd r hr))
  have hg : IntervalIntegrable
      (fun r ↦ 1 / (r - 2 * p) + 2 * p / (r - 2 * p) ^ 2) volume a b := by
    apply ContinuousOn.intervalIntegrable
    exact (continuousOn_const.div (continuousOn_id.sub continuousOn_const) hng).add
      (continuousOn_const.div ((continuousOn_id.sub continuousOn_const).pow 2)
        (by intro r hr; exact pow_ne_zero _ (hng r hr)))
  have hi := intervalIntegral.integral_mono_on hab hf hg (by
    intro r hr
    exact annular_exponent_pointwise (ha0.trans_le hr.1) hb0 (by linarith [hr.1]))
  have hi2 := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
  exact ⟨hi2, hi2.trans (annular_exponent_endpoint_le hp hD hgap hab)⟩

end AcExtensionPrinciple

end
