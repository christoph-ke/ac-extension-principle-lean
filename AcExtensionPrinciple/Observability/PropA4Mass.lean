module

public import AcExtensionPrinciple.Observability.PropA4Statements
public import AcExtensionPrinciple.Observability.Algebra

/-!
# Initial and total mass bounds for Proposition A.4

Paper `e1a0fd5`, `equations.tex` lines 1682–1690 and 1915–1920.
These are consequences of normalized chart data and Lemma A.2.
-/

public section

namespace AcExtensionPrinciple
namespace PropA4

open Set

/-- The geometric gap bounds the logarithmic mass energy. Paper `e1a0fd5`,
lines 1683 and 1918–1919. -/
theorem neg_log_gap_le {K μ : ℝ} (hK : 1 ≤ K) (hμ : 0 ≤ μ)
    (hgap : K⁻¹ ≤ 1 - μ) : -Real.log (1 - μ) ≤ K * μ := by
  have hK0 : 0 < K := by linarith
  have hg : 0 < 1 - μ := (inv_pos.mpr hK0).trans_le hgap
  have hrec : (1 - μ)⁻¹ ≤ K := (inv_le_comm₀ hg hK0).mpr hgap
  have hh := Real.log_le_sub_one_of_pos (inv_pos.mpr hg)
  rw [Real.log_inv] at hh
  have heq : (1 - μ)⁻¹ - 1 = μ * (1 - μ)⁻¹ := by
    field_simp
    ring
  rw [heq] at hh
  exact hh.trans (by simpa [mul_comm] using mul_le_mul_of_nonneg_left hrec hμ)

/-- Initial enclosed mass is nonnegative and at most half the radius.
Paper `e1a0fd5`, lines 1677 and 1910. -/
theorem initial_mass_bounds {b T K : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) : 0 ≤ S.m 0 0 ∧ 2 * S.m 0 0 ≤ b := by
  have hs : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, h.T_nonneg⟩
  have hq := h.boundary_mem hs
  have hm := (h.signs 0 0 hq).2.2
  have hg := h.gap_pos hq
  rw [SSFields.mu, (h.boundary_gauge 0 hs).1, massRatio] at hm hg
  constructor
  · have hh := (le_div_iff₀ h.b_pos).mp hm
    linarith
  · have hh := (div_lt_iff₀ h.b_pos).mp (show 2 * S.m 0 0 / b < 1 by linarith)
    linarith

/-- The scalar amplitude and gap control the initial shifted energy.
Paper `e1a0fd5`, lines 1683–1684 and 1915–1920. -/
theorem initial_shiftedEnergy_le {b T K : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hT : K * b ≤ T) :
    chartShiftedEnergy b S 0 ≤ K * chartScalarEnergy S T + K * S.m 0 0 := by
  have hb := h.b_pos
  have hs : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, h.T_nonneg⟩
  have hq := h.boundary_mem hs
  have hμ := (h.signs 0 0 hq).2.2
  have hgap := h.gap 0 0 hq
  rw [SSFields.mu, (h.boundary_gauge 0 hs).1] at hμ hgap
  have hlog := neg_log_gap_le h.K_ge_one hμ hgap
  have hamp := h.axis_amplitude hT
  have hscalar : chartPsi S 0 0 ^ 2 / (2 * b) ≤ K * chartScalarEnergy S T := by
    rw [div_le_iff₀ (show 0 < 2 * b by positivity)]
    simpa only [sq_abs, mul_assoc, mul_left_comm, mul_comm] using hamp
  have hmass : -(b / 2 * Real.log (1 - massRatio b (S.m 0 0))) ≤ K * S.m 0 0 := by
    have hh := mul_le_mul_of_nonneg_left hlog (show 0 ≤ b / 2 by positivity)
    have heq : b / 2 * (K * massRatio b (S.m 0 0)) = K * S.m 0 0 := by
      unfold massRatio
      field_simp [hb.ne']
    rw [heq] at hh
    linarith
  rw [chartShiftedEnergy_eq S 0 h.b_pos]
  linarith

/-- Under small observation, all enclosed masses are bounded by `(K+2)M`
and the shifted energy retains `M-E`. Paper `e1a0fd5`,
`eq:observability-total-mass-bound`, lines 1682–1690. -/
theorem total_mass_bound {b T K δ : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hT : K * b ≤ T)
    (hδ : δ ≤ 1 / (2 * K)) (hE : chartScalarEnergy S T ≤ δ * S.m 0 0)
    {s t : ℝ} (hq : (s, t) ∈ chartCylinder h.g T) :
    0 ≤ S.m s t ∧ S.m s t ≤ chartShiftedEnergy b S s ∧
      chartShiftedEnergy b S s ≤ (K + 2) * S.m 0 0 ∧
      S.m 0 0 - chartScalarEnergy S T ≤ chartShiftedEnergy b S s := by
  have hM := (initial_mass_bounds h).1
  have hK0 : 0 < K := by linarith [h.K_ge_one]
  have hE0 := h.scalar_energy_nonneg
  have hE' : chartScalarEnergy S T ≤ S.m 0 0 / (2 * K) := by
    calc
      _ ≤ δ * S.m 0 0 := hE
      _ ≤ (1 / (2 * K)) * S.m 0 0 := mul_le_mul_of_nonneg_right hδ hM
      _ = _ := by ring
  have hscaled : K * chartScalarEnergy S T ≤ S.m 0 0 / 2 := by
    have hh := mul_le_mul_of_nonneg_left hE' hK0.le
    have heq : K * (S.m 0 0 / (2 * K)) = S.m 0 0 / 2 := by field_simp
    rwa [heq] at hh
  have hEhalf : chartScalarEnergy S T / 2 ≤ S.m 0 0 := by
    nlinarith [h.K_ge_one]
  have hs : s ∈ Icc 0 T := ⟨hq.1, hq.2.1⟩
  have hF := initial_shiftedEnergy_le h hT
  have hstab := h.shifted_stability hs
  have hMle := h.mass_le_shiftedEnergy (h.boundary_mem ⟨le_rfl, h.T_nonneg⟩)
  have hnon : 0 ≤ S.m s t := by
    have hr : 0 ≤ S.r s t := by
      rcases hq.2.2.1.eq_or_lt with heq | hlt
      · change h.g s = t at heq
        rw [← heq, (h.axis_values s hs).1]
      · exact (h.radius_pos hq hlt).le
    by_cases hr0 : S.r s t = 0
    · have ht0 : t = h.g s := by
        by_contra ht0
        have := h.radius_pos hq (lt_of_le_of_ne hq.2.2.1 (Ne.symm ht0))
        linarith
      rw [ht0, (h.axis_values s hs).2]
    · have hμ := (h.signs s t hq).2.2
      change 0 ≤ 2 * S.m s t / S.r s t at hμ
      have hh := (le_div_iff₀ (lt_of_le_of_ne hr (Ne.symm hr0))).mp hμ
      linarith
  exact ⟨hnon, h.mass_le_shiftedEnergy hq, by nlinarith, by linarith⟩

end PropA4
end AcExtensionPrinciple

end
