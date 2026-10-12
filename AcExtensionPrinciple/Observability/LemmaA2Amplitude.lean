module

public import AcExtensionPrinciple.Observability.ChartGeometry

/-!
# Lemma A.2: scalar amplitude controlled by boundary observation

Paper `e1a0fd5`, `eq:observability-axis-amplitude`, lines 1512–1515,
1524–1530. Volterra positivity is applied on compact triangles ending
strictly before the incoming ray reaches the axis. Their minimum radius
is positive; the lower bound is independent of that minimum. Continuity
then passes the lower bound to the zero axis trace.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

namespace NormalizedChartData

variable {b T K : ℝ} {S : SSFields} (h : NormalizedChartData b T K S)

include h

/-- Signed positive boundary data give a uniform lower bound throughout a
pre-axis triangle. Paper `e1a0fd5`, `equations.tex` lines 1524–1530.
The helper premises are the sign choice, positive contradiction margin,
and the pre-axis cutoff, all discharged in `signed_axis_amplitude_le`. -/
theorem signed_volterra_lower {ε c τ : ℝ} (hε : |ε| = 1) (hc : 0 < c)
    (hτ : 0 ≤ τ) (hτT : τ ≤ T) (hτKb : τ ≤ K * b) (hg : h.g τ < 0)
    (hmargin : c ≤ ε * chartPsi S 0 0 - Real.sqrt (2 * K * b * chartScalarEnergy S T)) :
    c ≤ ε * chartPsi S τ 0 := by
  have htridomain := h.triangle_subset le_rfl hτ hτT hg
  obtain ⟨η, hη, hfloor⟩ := h.triangle_radius_floor le_rfl hτ hτT hg
  have htri : chartTriangle 0 τ ⊆ chartInterior (chartCylinder h.g T) S :=
    fun q hq => ⟨(htridomain hq).1, hη.trans_le (hfloor q hq)⟩
  obtain ⟨P, hP, hPeq⟩ := chartTriangle_continuous_extension (h.continuous_potential_on htri)
  have hψcont : ContinuousOn (fun q => ε * chartPsi S q.1 q.2) (chartTriangle 0 τ) :=
    continuousOn_const.mul (h.continuous_psi.mono (fun q hq => (htri hq).1))
  obtain ⟨ψ, hψ, hψeq⟩ := chartTriangle_continuous_extension hψcont
  obtain ⟨p, hp⟩ := (isCompact_chartTriangle 0 τ).exists_bound_of_continuousOn hP.continuousOn
  obtain ⟨B, hB⟩ := (isCompact_chartTriangle 0 τ).exists_bound_of_continuousOn hψ.continuousOn
  let g : ℝ × ℝ → ℝ := fun q =>
    ε * (chartPsi S q.1 q.1 - ∫ σ in q.2..q.1, S.dvpsi σ σ)
  have hk : ∀ s t, 0 ≤ t → t ≤ s → s ≤ τ → 0 ≤ P (s, t) ∧ P (s, t) ≤ p := by
    intro s t ht hts hs
    have hq : (s, t) ∈ chartTriangle 0 τ := ⟨ht, hts, hs⟩
    refine ⟨?_, (le_abs_self _).trans (hp (s, t) hq)⟩
    rw [hPeq (s, t) hq]
    exact h.potential_nonneg (htri hq).1
  have hb : ∃ B : ℝ, ∀ s t, 0 ≤ t → t ≤ s → s ≤ τ → |ψ (s, t)| ≤ B :=
    ⟨B, fun s t ht hts hs => hB (s, t) ⟨ht, hts, hs⟩⟩
  have hgsource : ∀ s t, 0 ≤ t → t ≤ s → s ≤ τ → c ≤ g (s, t) := by
    intro s t ht hts hs
    have hcs := axis_amplitude_cauchy_schwarz ht hts (hs.trans hτT)
      h.boundary_traces_ac.1 h.boundary_dvpsi_integrable h.boundary_scalar_square_integrable.2
      h.boundary_psi_deriv_square_integrable
    have hsq : Real.sqrt (2 * s * chartScalarEnergy S T) ≤
        Real.sqrt (2 * K * b * chartScalarEnergy S T) := by
      apply Real.sqrt_le_sqrt
      nlinarith [mul_le_mul_of_nonneg_right (hs.trans hτKb) h.scalar_energy_nonneg]
    have habs : |ε * ((chartPsi S s s - chartPsi S 0 0) -
        ∫ σ in t..s, S.dvpsi σ σ)| ≤ Real.sqrt (2 * K * b * chartScalarEnergy S T) := by
      rw [abs_mul, hε, one_mul]
      exact (abs_sub _ _).trans (hcs.trans hsq)
    have hh := (abs_le.mp habs).1
    dsimp [g]
    nlinarith
  have heq : ∀ s t, 0 ≤ t → t ≤ s → s ≤ τ →
      ψ (s, t) = g (s, t) + triangleVolterra P ψ s t := by
    intro s t ht hts hs
    have hq : (s, t) ∈ chartTriangle 0 τ := ⟨ht, hts, hs⟩
    have he := chart_triangleVolterra_congr (P := P) (ψ := ψ)
      (Q := fun q => chartPotential S q.1 q.2) (χ := fun q => ε * chartPsi S q.1 q.2)
      ht hts hs (fun q hq => by
      rw [hPeq q hq, hψeq q hq])
    rw [hψeq (s, t) hq, he, chart_triangleVolterra_const_mul]
    have hv := h.volterra ht (htri hq)
    dsimp [g]
    rw [hv]
    ring
  have hpτ := triangleVolterra_positive hP hψ hτ hc hk hb hgsource heq
    τ 0 le_rfl hτ le_rfl
  simpa only [hψeq (τ, 0) ⟨le_rfl, hτ, le_rfl⟩] using hpτ

/-- The ray is strictly above its axis before the arrival time, derived from
the negative incoming expansion. Paper `e1a0fd5`, lines 1451, 1524–1530. -/
theorem before_axis_zero {s s₀ : ℝ} (hs : 0 ≤ s) (hss : s < s₀) (hsT : s₀ ≤ T)
    (haxis : h.g s₀ = 0) : h.g s < 0 := by
  have hseg := h.in_subset hs hsT hs (by simp [haxis])
  have hR := (h.equations.radius_s 0 s s₀ hss.le hseg).2
  have hn : ContinuousOn (fun σ => S.nu σ 0) (Icc s s₀) :=
    h.continuous_nu.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun σ hσ => hseg ⟨hσ, by simp⟩)
  have hpos : 0 < ∫ σ in s..s₀, -S.nu σ 0 := by
    apply intervalIntegral.integral_pos hss hn.neg
    · intro σ hσ
      exact (neg_pos.mpr (h.signs σ 0
        (hseg (show (σ, 0) ∈ inSeg 0 s s₀ from ⟨⟨hσ.1.le, hσ.2⟩, by simp⟩))).2.1).le
    · refine ⟨s, ⟨le_rfl, hss.le⟩, ?_⟩
      exact neg_pos.mpr (h.signs s 0
        (hseg (show (s, 0) ∈ inSeg 0 s s₀ from ⟨⟨le_rfl, hss.le⟩, by simp⟩))).2.1
  rw [intervalIntegral.integral_neg] at hpos
  have hr₀ : S.r s₀ 0 = 0 := by
    simpa [haxis] using (h.axis_values s₀ ⟨hs.trans hss.le, hsT⟩).1
  have hr : 0 < S.r s 0 := by linarith
  have hgs : h.g s ≤ 0 := (hseg
    (show (s, 0) ∈ inSeg 0 s s₀ from ⟨⟨le_rfl, hss.le⟩, by simp⟩)).2.2.1
  rcases hgs.eq_or_lt with he | he
  · have hz := (h.axis_values s ⟨hs, hss.le.trans hsT⟩).1
    rw [he] at hz
    linarith
  · exact he

/-- Either sign of the initial scalar amplitude is bounded by the same square
root. Paper `e1a0fd5`, `eq:observability-axis-amplitude`, lines 1524–1530. -/
theorem signed_axis_amplitude_le {ε : ℝ} (hε : |ε| = 1) (hduration : K * b ≤ T) :
    ε * chartPsi S 0 0 ≤ Real.sqrt (2 * K * b * chartScalarEnergy S T) := by
  obtain ⟨s₀, hs₀, haxis⟩ := h.axis_reached 0 ⟨le_rfl, h.T_nonneg⟩ (by simpa)
  have hsKb : s₀ ≤ K * b := by simpa only [zero_add] using hs₀.2
  have hsT : s₀ ≤ T := hsKb.trans hduration
  have hspos : 0 < s₀ := by
    by_contra hn
    have he : s₀ = 0 := le_antisymm (le_of_not_gt hn) hs₀.1
    have hh := h.axis_before_boundary 0 ⟨le_rfl, h.T_nonneg⟩
    rw [he] at haxis
    linarith
  by_contra hlarge
  let c := ε * chartPsi S 0 0 - Real.sqrt (2 * K * b * chartScalarEnergy S T)
  have hc : 0 < c := sub_pos.mpr (lt_of_not_ge hlarge)
  have hlower : ∀ s, 0 ≤ s → s < s₀ → c ≤ ε * chartPsi S s 0 := by
    intro s hs hss
    exact h.signed_volterra_lower hε hc hs (hss.le.trans hsT) (hss.le.trans hsKb)
      (h.before_axis_zero hs hss hsT haxis) le_rfl
  have hseg := h.in_subset (t := 0) (a := 0) (c := s₀) le_rfl hsT le_rfl (by simp [haxis])
  have hcont : ContinuousOn (fun s => ε * chartPsi S s 0) (Icc 0 s₀) :=
    continuousOn_const.mul (h.continuous_psi.comp
      (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => hseg ⟨hs, by simp⟩))
  have hI : Icc 0 s₀ ∈ 𝓝[Iio s₀] s₀ := by
    exact inter_mem (mem_nhdsWithin_of_mem_nhds (Ici_mem_nhds hspos))
      (Filter.mem_of_superset self_mem_nhdsWithin (fun s hs => hs.le))
  have hzero : ε * chartPsi S s₀ 0 = 0 := by
    rw [chartPsi]
    have hz := (h.axis_values s₀ ⟨hspos.le, hsT⟩).1
    rw [haxis] at hz
    simp [hz]
  have hlim : Tendsto (fun s => ε * chartPsi S s 0) (𝓝[Iio s₀] s₀) (𝓝 0) := by
    simpa only [hzero] using
      ((hcont s₀ ⟨hspos.le, le_rfl⟩).mono_of_mem_nhdsWithin hI).tendsto
  have hh : c ≤ 0 := ge_of_tendsto hlim (by
    filter_upwards [hI, self_mem_nhdsWithin] with s hs hslt
    exact hlower s hs.1 hslt)
  linarith

/-- Lemma A.2's axis amplitude estimate in the abstract normalized chart.
Paper `e1a0fd5`, `lem:observability-axis-amplitude`,
`eq:observability-axis-amplitude`, lines 1512–1515, 1524–1530. -/
theorem axis_amplitude (hduration : K * b ≤ T) :
    |chartPsi S 0 0| ^ 2 ≤ 2 * K * b * chartScalarEnergy S T := by
  have hp := h.signed_axis_amplitude_le (ε := 1) (by norm_num) hduration
  have hn := h.signed_axis_amplitude_le (ε := -1) (by norm_num) hduration
  have habs : |chartPsi S 0 0| ≤ Real.sqrt (2 * K * b * chartScalarEnergy S T) := by
    apply abs_le.mpr
    constructor <;> linarith
  have hnon : 0 ≤ 2 * K * b * chartScalarEnergy S T := by
    have hK : 0 ≤ K := by linarith [h.K_ge_one]
    exact mul_nonneg (mul_nonneg (by positivity) h.b_pos.le) h.scalar_energy_nonneg
  nlinarith [Real.sq_sqrt hnon, Real.sqrt_nonneg (2 * K * b * chartScalarEnergy S T),
    abs_nonneg (chartPsi S 0 0)]

end NormalizedChartData

end AcExtensionPrinciple

end
