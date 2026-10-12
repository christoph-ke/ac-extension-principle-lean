module

public import AcExtensionPrinciple.Observability.InnerChartBoundaryVariation
public import AcExtensionPrinciple.Observability.InnerChartEnergy
public import AcExtensionPrinciple.Observability.PropA4InnerInterface
public import AcExtensionPrinciple.Observability.PropA4Exterior

/-!
# Discharge of the precise A.4 inner-chart interface

Paper `e1a0fd5`, `equations.tex` lines 1877–1907, especially line 1901.
The source mass bound supplies the half-speed estimate. The interval and
both regular inverse coordinates are constructed from the outer chart.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory

namespace InnerCylinder

variable {b T K a s₀ s₁ : ℝ} {S : SSFields} {h : NormalizedChartData b T K S}
variable (c : InnerCylinder h a s₀ s₁)

/-- A mass upper bound and a≥4P give the printed half-speed bound on
the smaller cylinder. `InnerChartStatement` assumes the stronger a≥32P. Paper `e1a0fd5`,
lines 1722–1728 and 1905–1907. -/
theorem half_speed_of_mass_bound {P : ℝ} (hP : 0 < P) (ha : 4 * P ≤ a)
    (hmass : ∀ s t, (s, t) ∈ chartCylinder h.g T → S.m s t ≤ P) :
    ∀ s ∈ Icc s₀ s₁, 1 / 2 ≤ -S.nu s (c.v s) := by
  intro s hs
  have hp := c.source_mem hs
  have hn := PropA4.exterior_neg_nu_lower h hP.le hp
    (by rw [(c.points s hs).2.2]; linarith)
    (fun z hz => hmass s z (h.out_subset ⟨hp.1.1, hp.1.2.1⟩ hp.1.2.2.1 le_rfl
      (show (s, z) ∈ outSeg s (c.v s) s from ⟨by simp, hz⟩)))
  rw [(c.points s hs).2.2] at hn
  have hfrac : 2 * P / a ≤ 1 / 2 := (div_le_iff₀ c.a_pos).mpr (by linarith)
  linarith

/-- The regular inner tangent holds within the closed interval,
including both endpoints. Paper `e1a0fd5`, lines 1887–1891. -/
theorem tangent_within (hstrict : s₀ < s₁) {s : ℝ} (hs : s ∈ Icc s₀ s₁) :
    HasDerivWithinAt c.v (-S.nu s (c.v s) / S.lam s (c.v s)) (Icc s₀ s₁) s := by
  have hl := h.continuous_lam.comp (continuousOn_id.prodMk c.continuous_v)
    (fun _ hz => (c.source_mem hz).1)
  exact cylinder_interval_hasDerivWithinAt hstrict c.continuous_v
    (c.density_continuous_positive.1.div hl
      (fun _ hz => (h.signs _ _ (c.source_mem hz).1).1.ne')) c.tangent hs

/-- A prescribed positive inner-clock duration selects a unique eligible
endpoint by continuity. Paper `e1a0fd5`, lines 1905–1907. -/
theorem exists_clock_endpoint {D : ℝ} (hD : 0 < D) (hfit : D ≤ c.clock s₁) :
    ∃ d ∈ Icc s₀ s₁, s₀ < d ∧ c.clock d = D := by
  have hc : ContinuousOn c.clock (Icc s₀ s₁) := by
    simpa only [uIcc_of_le c.ordered] using c.clock_gauge.continuous
  have hzero : c.clock s₀ = 0 := by simp [clock]
  obtain ⟨d, hd, he⟩ := intermediate_value_Icc c.ordered hc
    (show D ∈ Icc (c.clock s₀) (c.clock s₁) by rw [hzero]; exact ⟨hD.le, hfit⟩)
  refine ⟨d, hd, lt_of_le_of_ne hd.1 ?_, he⟩
  intro hn
  rw [← hn, hzero] at he
  linarith

end InnerCylinder

namespace PropA4

/-- Proof of `InnerChartStatement`: the smaller
cylinder has the same K, exact A.3 duration, increasing C¹ entry labels,
matching earlier-label extension, inherited compact uniform BV, the correct
initial mass ratio, and the printed integrable boundary-energy density.
Paper `e1a0fd5`, `eq:observability-inner-boundary-measure` and
`eq:observability-inner-boundary-lower-bound`, lines 1877–1907. -/
theorem innerChartStatement (K : ℝ) : InnerChartStatement K := by
  intro b T S h P a ε s₀ hP hmass ha hab _hε _hε1 hlate hfit
  have ha0 : 0 < a := by linarith
  let D := positiveMassDuration K ε * a
  have hH : 0 < positiveMassDuration K ε :=
    (show 0 < K + 1 by linarith [h.K_ge_one]).trans_le (le_max_left _ _)
  have hD : 0 < D := mul_pos hH ha0
  have hs : s₀ ≤ s₀ + 2 * D := by linarith
  have hs₀ : K * b ≤ s₀ := by nlinarith [h.b_pos]
  let full := h.innerCylinder ha0 hab hs hs₀ hfit
  have hhalf := full.half_speed_of_mass_bound hP (by linarith) hmass
  have htime : D ≤ full.clock (s₀ + 2 * D) := by
    have he := full.outer_duration_le_twice_clock hhalf
    linarith
  obtain ⟨d, hd, hsd, hclock⟩ := full.exists_clock_endpoint hD htime
  let c := h.innerCylinder ha0 hab hd.1 hs₀ (hd.2.trans hfit)
  have hclock' : c.clock d = D := hclock
  obtain ⟨q⟩ := c.exists_coordinates
    (c.half_speed_of_mass_bound hP (by linarith) hmass)
  refine ⟨d, c.v, q.fields, hd.1, hd.2, ?_, c.continuous_v, c.v_strictMono,
    (fun s hs => c.tangent_within hsd hs), ?_, q.initial_values.2,
    q.observation_integrable, ?_⟩
  · intro s hs
    exact ⟨(c.source_mem hs).1, (c.points s hs).2.2⟩
  · change Nonempty (NormalizedChartData a D K q.fields)
    rw [← hclock']
    exact ⟨q.chart_data⟩
  · simpa only [hclock'] using q.observation_integral_eq

end PropA4

end AcExtensionPrinciple

end
