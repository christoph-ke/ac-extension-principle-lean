module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic

/-!
# Algebra in boundary observability

Helpers for paper `e1a0fd5`, `equations.tex` lines 1558–1563,
1613–1621, 1642, 1742–1747 and 1915–1930.
-/

public section

namespace AcExtensionPrinciple

/-- The first annular exponent comparison is valid; paper `e1a0fd5`,
`eq:observability-annular-exponent`, lines 1613–1621. -/
theorem annular_exponent_pointwise {r b p : ℝ} (hr : 0 < r) (hb : 0 < b)
    (hgap : 0 < r - 2 * p) :
    (r⁻¹ - b⁻¹) / (1 - 2 * p / r) ^ 2 ≤
      1 / (r - 2 * p) + 2 * p / (r - 2 * p) ^ 2 := by
  have heq : (r⁻¹ - b⁻¹) / (1 - 2 * p / r) ^ 2 =
      r / (r - 2 * p) ^ 2 - r ^ 2 / (b * (r - 2 * p) ^ 2) := by
    field_simp
  have heq' : 1 / (r - 2 * p) + 2 * p / (r - 2 * p) ^ 2 =
      r / (r - 2 * p) ^ 2 := by
    field_simp
    ring
  rw [heq, heq']
  exact sub_le_self _ (by positivity)

/-- The chosen gap contradicts the geometric lower bound; paper `e1a0fd5`,
`equations.tex` line 1642. -/
theorem annular_delta_contradiction {K : ℝ} (hK : 1 ≤ K) :
    1 - (1 - 1 / (8 * K)) / (1 + 1 / (8 * K)) =
      2 * (1 / (8 * K)) / (1 + 1 / (8 * K)) ∧
    2 * (1 / (8 * K)) / (1 + 1 / (8 * K)) < K⁻¹ := by
  have hK0 : 0 < K := by linarith
  constructor
  · field_simp
    ring
  · apply (div_lt_iff₀ (by positivity : 0 < 1 + 1 / (8 * K))).mpr
    field_simp
    nlinarith

/-- The annulus lies inside the outer cylinder; paper `e1a0fd5`,
`equations.tex` line 1558, with `a = 2M(1+1/(8K))`. -/
theorem annular_inner_lt_outer {K M b : ℝ} (hK : 1 ≤ K) (hM : 0 ≤ M)
    (hb : 0 < b) (hratio : 2 * M / b ≤ 1 - K⁻¹) :
    2 * M * (1 + 1 / (8 * K)) < b := by
  have hK0 : 0 < K := by linarith
  have hratio' := (div_le_iff₀ hb).mp hratio
  have hratio'' : 2 * M * K ≤ b * (K - 1) := by
    have := mul_le_mul_of_nonneg_right hratio' hK0.le
    field_simp at this
    nlinarith
  apply (mul_lt_mul_iff_left₀ (show 0 < 8 * K by positivity)).mp
  field_simp
  nlinarith [mul_nonneg hM hK0.le]

/-- Both annular gaps follow from the stated small incoming flux; paper `e1a0fd5`,
`eq:observability-annular-gap`, lines 1560–1563. -/
theorem annular_gap {M J δ c ε : ℝ} (hM : 0 < M) (hδ : 0 < δ)
    (hc : 0 ≤ c) (hcδ : c ≤ δ / 2) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hJ : J ≤ c * ε ^ 2 * M) :
    2 * M * (1 + δ) - 2 * (M + J) ≥ δ * M ∧
    1 - 2 * (M + J) / (2 * M * (1 + δ)) ≥ δ / (2 * (1 + δ)) := by
  have hεsq : ε ^ 2 ≤ 1 := by nlinarith
  have hJ' : J ≤ δ / 2 * M :=
    hJ.trans ((mul_le_mul_of_nonneg_right
      ((mul_le_mul_of_nonneg_left hεsq hc).trans (by nlinarith)) hM.le))
  constructor
  · nlinarith
  · have heq : 1 - 2 * (M + J) / (2 * M * (1 + δ)) =
        (2 * M * (1 + δ) - 2 * (M + J)) / (2 * M * (1 + δ)) := by
      field_simp
    rw [heq]
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * (1 + δ))
      (by positivity : 0 < 2 * M * (1 + δ))).mpr
    nlinarith [mul_nonneg (show 0 ≤ δ * M - 2 * J by nlinarith)
      (show 0 ≤ 1 + δ by positivity)]

/-- Exact weighted operator coefficients; paper `e1a0fd5`,
`eq:observability-power-operator-bound`, lines 1742–1747. -/
theorem observability_operator_coefficients :
    1 / (4 * (2 - (0 : ℝ)) * (1 - 0)) = 1 / 8 ∧
    1 / (4 * (2 - (1 / 2 : ℝ)) * (1 - 1 / 2)) = 1 / 3 ∧
    1 / (4 * (2 - (-1 / 2 : ℝ)) * (1 - -1 / 2)) = 1 / 15 := by
  norm_num

/-- The cutoff `M*/r ≤ 1/32` gives exactly the coefficient printed in the paper;
paper `e1a0fd5`, `eq:observability-power-operator-bound`, lines 1742–1747. -/
theorem observability_operator_coefficient_le {p r q : ℝ} (hr : 0 < r)
    (hq : q < 1) (hcut : p / r ≤ 1 / 32) :
    8 * p / ((2 - q) * (1 - q) * r) ≤ 1 / (4 * (2 - q) * (1 - q)) := by
  have h2 : 0 < 2 - q := by linarith
  have h1 : 0 < 1 - q := by linarith
  have hd : 0 < (2 - q) * (1 - q) := mul_pos h2 h1
  have hp := (div_le_iff₀ hr).mp hcut
  apply (div_le_iff₀ (mul_pos hd hr)).mpr
  have heq : 1 / (4 * (2 - q) * (1 - q)) * ((2 - q) * (1 - q) * r) = r / 4 := by
    field_simp
  rw [heq]
  linarith

/-- Explicit final observation constant; paper `e1a0fd5`, proof of
`prop:boundary-observability`, lines 1915–1930, and Lemma 2.5 lines 762–771.
The choice `σ=c/(K(c+1))` lies in `(0,1]`. -/
theorem observability_assembly {F E m K c : ℝ} (hK : 1 ≤ K) (hc : 0 < c)
    (hF : F ≤ K * E + K * m) (hm : c * m ≤ E) :
    0 < c / (K * (c + 1)) ∧ c / (K * (c + 1)) ≤ 1 ∧
      c / (K * (c + 1)) * F ≤ E := by
  have hK0 : 0 < K := by linarith
  have hd : 0 < K * (c + 1) := by positivity
  refine ⟨div_pos hc hd, (div_le_one hd).mpr ?_, ?_⟩
  · nlinarith
  · have hscaled := mul_le_mul_of_nonneg_left hF hc.le
    have hmass := mul_le_mul_of_nonneg_left hm hK0.le
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hd).mpr
    nlinarith

end AcExtensionPrinciple

end
