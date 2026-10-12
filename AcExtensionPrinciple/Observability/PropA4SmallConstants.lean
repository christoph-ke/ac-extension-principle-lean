module

public import AcExtensionPrinciple.Observability.PropA4Constants

/-!
# Simultaneous parameter choices in the small-mass argument

Paper `e1a0fd5`, lines 1906–1909. Choose the scale first, then the outer
mass-ratio threshold, and finally the observation threshold. The constants
are chosen before any chart, radius, mass, or observation duration.
-/

public section

namespace AcExtensionPrinciple
namespace PropA4

/-- All scale, retained-mass, interval-fit and observation budgets can be
met in the printed order, with a single K-only majorant coefficient `C`.
That coefficient majorizes the two proved analytic error constants.
Paper `e1a0fd5`, lines 1906–1909. -/
theorem choose_small_mass_parameters {K C q₀ : ℝ}
    (hK : 1 ≤ K) (hC : 0 ≤ C) (hq₀ : 0 < q₀) :
    ∃ L ε δ : ℝ, 64 ≤ L ∧ 0 < ε ∧ ε < 1 / 2 ∧ 0 < δ ∧ δ ≤ 1 / (2 * K) ∧
      2 * L * (K + 2) * ε ≤ 1 ∧
      2 * positiveMassDuration K (1 / (2 * K * (K + 2) * L)) * L * (K + 2) * ε ≤ 1 ∧
      C * (δ + (K + 2) / L + (K + 2) ^ 2 * ε) ≤ 3 / (4 * K) ∧
      C * positiveMassDuration K (1 / (2 * K * (K + 2) * L)) / L ^ 3 ≤
        (q₀ / (L ^ 2 * (1 + Real.log L) ^ 2)) / 4 ∧
      C * (1 + positiveMassDuration K (1 / (2 * K * (K + 2) * L)) / L ^ 2) * δ ≤
        (q₀ / (L ^ 2 * (1 + Real.log L) ^ 2)) / 4 := by
  have hK0 : 0 < K := by linarith only [hK]
  let D := K + 2 + |Real.log (32 * K ^ 2 * (K + 2))|
  have hD : 0 ≤ D := by dsimp [D]; positivity
  obtain ⟨L, hLB, hscale⟩ := exists_large_scale (C := 4 * C * D) hq₀
    (max 64 (4 * K * C * (K + 2)))
  have hL : 64 ≤ L := (le_max_left _ _).trans hLB
  have hLM : 4 * K * C * (K + 2) ≤ L := (le_max_right _ _).trans hLB
  have hL0 : 0 < L := by linarith only [hL]
  have hL1 : 1 ≤ L := by linarith only [hL]
  have hz : 0 < 1 + Real.log L := by linarith only [Real.log_nonneg hL1]
  let H := positiveMassDuration K (1 / (2 * K * (K + 2) * L))
  have hH0 : 0 ≤ H := by
    unfold H positiveMassDuration
    exact (show 0 ≤ K + 1 by linarith only [hK]).trans (le_max_left _ _)
  have hH : H ≤ D * (1 + Real.log L) := inner_duration_le hK hL1
  have hlimit := (div_lt_iff₀ hL0).mp hscale
  have hHmul := mul_le_mul_of_nonneg_left hH
    (show 0 ≤ 4 * C * (1 + Real.log L) ^ 2 by positivity)
  have hscaled : 4 * C * H * (1 + Real.log L) ^ 2 ≤ q₀ * L := by
    nlinarith only [hHmul, hlimit]
  let q := q₀ / (L ^ 2 * (1 + Real.log L) ^ 2)
  have hq : 0 < q := by dsimp [q]; positivity
  have hobsScale : C * H / L ^ 3 ≤ q / 4 := by
    have heq : q / 4 = q₀ / (4 * (L ^ 2 * (1 + Real.log L) ^ 2)) := by
      dsimp [q]
      rw [div_div]
      congr 1
      ring
    rw [heq, div_le_div_iff₀ (pow_pos hL0 3) (by positivity)]
    have hh := mul_le_mul_of_nonneg_right hscaled (sq_nonneg L)
    convert hh using 1 <;> ring
  have hmassScale : C * (K + 2) / L ≤ 1 / (4 * K) := by
    rw [div_le_div_iff₀ hL0 (by positivity)]
    nlinarith only [hLM]
  obtain ⟨ε, hε, hε1, hεa, hεT, hεM⟩ := choose_outer_threshold hK hL0 hH0 hC
    (show 0 < 1 / (4 * K) by positivity)
  obtain ⟨δ, hδ, hδK, hδM, hδE⟩ := choose_observation_threshold hK hC hH0 hL0
    (show 0 < 1 / (4 * K) by positivity) (show 0 < q / 4 by positivity)
  refine ⟨L, ε, δ, hL, hε, hε1, hδ, hδK, hεa, hεT, ?_, hobsScale, hδE⟩
  have heq : C * (δ + (K + 2) / L + (K + 2) ^ 2 * ε) =
      C * δ + C * (K + 2) / L + C * (K + 2) ^ 2 * ε := by ring
  rw [heq]
  ring_nf at hδM hmassScale hεM ⊢
  linarith only [hδM, hmassScale, hεM]

end PropA4
end AcExtensionPrinciple

end
