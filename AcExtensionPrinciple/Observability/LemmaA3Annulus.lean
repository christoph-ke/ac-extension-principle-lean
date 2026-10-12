module

public import AcExtensionPrinciple.Observability.LemmaA3Constants

/-!
# Lemma A.3: logarithmic annular exponent and travel time

Paper `e1a0fd5`, `eq:observability-annular-exponent`, lines 1613–1621,
and the travel-time estimate at lines 1630–1632.
The numerical premises are supplied by initial mass ratio and small flux.
-/

public section

namespace AcExtensionPrinciple

open MeasureTheory

/-- Both logarithmic annular estimates, retaining coefficient two in the
exponent. Paper `e1a0fd5`, `eq:observability-annular-exponent`, lines 1613–1621,
and lines 1630–1632. The source proof discharges these numerical premises by
`annular_gap`, `μ_b(0) ≥ ε`, and `M₊ ≤ 2M`. -/
theorem lemmaA3_annular_estimates {p M δ ε a b : ℝ}
    (hp : 0 ≤ p) (hM : 0 < M) (hδ : 0 < δ) (hε : 0 < ε)
    (_ha : 0 ≤ a) (hab : a ≤ b) (hgap : δ * M ≤ a - 2 * p)
    (hratio : ε * b ≤ 2 * M) (hpM : p ≤ 2 * M) :
    2 * (∫ r in a..b, (r⁻¹ - b⁻¹) / (1 - 2 * p / r) ^ 2) ≤
      2 * Real.log (2 / (ε * δ)) + 8 / δ ∧
      (∫ r in a..b, 1 / (1 - 2 * p / r)) ≤
        b * (1 + Real.log (2 / (ε * δ))) := by
  have ha' : 2 * p < a := by linarith [mul_pos hδ hM]
  have hb : 0 < b := by linarith
  have hD : 0 < δ * M := mul_pos hδ hM
  have hquot : b / (δ * M) ≤ 2 / (ε * δ) := by
    apply (div_le_div_iff₀ hD (mul_pos hε hδ)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hratio hδ.le]
  have hlog := Real.log_le_log (div_pos hb hD) hquot
  have hmass : 4 * p / (δ * M) ≤ 8 / δ := by
    apply (div_le_div_iff₀ hD hδ).mpr
    nlinarith [mul_le_mul_of_nonneg_right hpM hδ.le]
  have hexp := (annular_exponent_integral_le hp hD hgap hab).2
  constructor
  · linarith
  · have harg : (b - 2 * p) / (a - 2 * p) ≤ 2 / (ε * δ) := by
      apply le_trans _ hquot
      apply (div_le_div_iff₀ (by linarith : 0 < a - 2 * p) hD).mpr
      have hh := mul_le_mul_of_nonneg_left hgap hb.le
      nlinarith
    have hnon : 0 ≤ Real.log ((b - 2 * p) / (a - 2 * p)) := by
      apply Real.log_nonneg
      apply (one_le_div (by linarith : 0 < a - 2 * p)).mpr
      linarith
    have hlog' := Real.log_le_log
      (div_pos (by linarith : 0 < b - 2 * p) (by linarith : 0 < a - 2 * p)) harg
    have hscale := mul_le_mul_of_nonneg_right (show 2 * p ≤ b by linarith) hnon
    have hscale' := mul_le_mul_of_nonneg_left hlog' hb.le
    rw [annular_travel_integral hp ha' hab]
    nlinarith

/-- The duration also dominates `1+|log ε|`, proving the other side of
`H_ε ∼ 1+|log ε|`. Paper `e1a0fd5`, `lem:observability-positive-mass`,
lines 1535–1540, `eq:observability-positive-mass-duration`, lines 1633–1637. -/
theorem lemmaA3_duration_log_lower {K ε : ℝ} (hK : 1 ≤ K) (hε : 0 < ε) (hε1 : ε < 1) :
    1 + |Real.log ε| ≤ lemmaA3Duration K ε := by
  have hK0 : 0 < K := by linarith only [hK]
  have hlog : 0 ≤ Real.log (16 * K) := Real.log_nonneg (by linarith only [hK])
  have he : 2 / (ε * lemmaA3Delta K) = (16 * K) / ε := by
    unfold lemmaA3Delta
    field_simp [hε.ne', hK0.ne']
    ring
  have hmax := le_max_right (K + 1) (1 + Real.log (2 / (ε * lemmaA3Delta K)))
  rw [he, Real.log_div (by positivity : 16 * K ≠ 0) hε.ne'] at hmax
  rw [abs_of_nonpos (Real.log_nonpos hε.le hε1.le)]
  unfold lemmaA3Duration
  rw [he, Real.log_div (by positivity : 16 * K ≠ 0) hε.ne']
  linarith only [hmax, hlog]

end AcExtensionPrinciple

end
