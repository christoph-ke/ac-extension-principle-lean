module

public import AcExtensionPrinciple.Observability.LemmaA3TranslationWave

/-!
# Lemma A.3: axis amplitude after constant scalar translation

Paper `e1a0fd5`, `equations.tex` line 1540 and lines 1524–1530, 1650–1663.
The positivity argument is applied directly to `ψ+q r`, without assuming
that translated characteristic expansions have extra BV regularity.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

namespace NormalizedChartData

variable {b T K : ℝ} {S : SSFields} (h : NormalizedChartData b T K S)

include h

/-- The translated amplitude is continuous. Paper `e1a0fd5`, line 1540. -/
theorem lemmaA3_translated_continuous (q : ℝ) :
    ContinuousOn (fun x => chartTranslatedPsi S q x.1 x.2) (chartCylinder h.g T) :=
  h.continuous_psi.add (continuousOn_const.mul h.continuous_r)

/-- Translated observed energy is nonnegative. Paper `e1a0fd5`, line 1540. -/
theorem lemmaA3_translated_energy_nonneg (q : ℝ) : 0 ≤ chartTranslatedEnergy S T q :=
  intervalIntegral.integral_nonneg h.T_nonneg (by intros; positivity)

/-- Cauchy–Schwarz for the translated boundary primitives. Paper `e1a0fd5`,
line 1540 and lines 1524–1528. -/
theorem lemmaA3_translated_cs (q : ℝ) {s t : ℝ}
    (ht : 0 ≤ t) (hts : t ≤ s) (hsT : s ≤ T) :
    |(chartPsi S s s + q * b) - (chartPsi S 0 0 + q * b)| +
      |∫ σ in t..s, S.dvpsi σ σ + q| ≤ Real.sqrt (2 * s * chartTranslatedEnergy S T q) := by
  have hd : deriv (fun s => chartPsi S s s + q * b) = deriv (fun s => chartPsi S s s) := by
    funext s
    exact deriv_add_const (q * b)
  have hi : IntervalIntegrable (fun s => deriv (fun s => chartPsi S s s + q * b) s ^ 2)
      volume 0 T := by rw [hd]; exact h.boundary_psi_deriv_square_integrable
  have hc := axis_amplitude_cauchy_schwarz ht hts hsT (h.lemmaA3_translated_boundary_ac q)
    (h.boundary_dvpsi_integrable.add intervalIntegrable_const)
    (h.lemmaA3_translated_square_integrable q) hi
  rw [hd] at hc
  exact hc

/-- Signed positive boundary data give a uniform lower bound throughout a
pre-axis triangle. Paper `e1a0fd5`, `equations.tex` lines 1524–1530.
The helper premises are the sign choice, positive contradiction margin,
and the pre-axis cutoff, all discharged in `signed_axis_amplitude_le`. -/
theorem lemmaA3_translated_signed_lower (q : ℝ) {ε c τ : ℝ} (hε : |ε| = 1) (hc : 0 < c)
    (hτ : 0 ≤ τ) (hτT : τ ≤ T) (hτKb : τ ≤ K * b) (hg : h.g τ < 0)
    (hmargin : c ≤ ε * (chartPsi S 0 0 + q * b) - Real.sqrt (2 * K * b * chartTranslatedEnergy S T q)) :
    c ≤ ε * chartTranslatedPsi S q τ 0 := by
  have htridomain := h.triangle_subset le_rfl hτ hτT hg
  obtain ⟨η, hη, hfloor⟩ := h.triangle_radius_floor le_rfl hτ hτT hg
  have htri : chartTriangle 0 τ ⊆ chartInterior (chartCylinder h.g T) S :=
    fun q hq => ⟨(htridomain hq).1, hη.trans_le (hfloor q hq)⟩
  obtain ⟨P, hP, hPeq⟩ := chartTriangle_continuous_extension (h.continuous_potential_on htri)
  have hψcont : ContinuousOn (fun x => ε * chartTranslatedPsi S q x.1 x.2) (chartTriangle 0 τ) :=
    continuousOn_const.mul ((h.lemmaA3_translated_continuous q).mono (fun q hq => (htri hq).1))
  obtain ⟨ψ, hψ, hψeq⟩ := chartTriangle_continuous_extension hψcont
  obtain ⟨p, hp⟩ := (isCompact_chartTriangle 0 τ).exists_bound_of_continuousOn hP.continuousOn
  obtain ⟨B, hB⟩ := (isCompact_chartTriangle 0 τ).exists_bound_of_continuousOn hψ.continuousOn
  let g : ℝ × ℝ → ℝ := fun x =>
    ε * ((chartPsi S x.1 x.1 + q * b) - ∫ σ in x.2..x.1, S.dvpsi σ σ + q)
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
    have hcs := h.lemmaA3_translated_cs q ht hts (hs.trans hτT)
    have hsq : Real.sqrt (2 * s * chartTranslatedEnergy S T q) ≤
        Real.sqrt (2 * K * b * chartTranslatedEnergy S T q) := by
      apply Real.sqrt_le_sqrt
      nlinarith [mul_le_mul_of_nonneg_right (hs.trans hτKb) (h.lemmaA3_translated_energy_nonneg q)]
    have habs : |ε * (((chartPsi S s s + q * b) - (chartPsi S 0 0 + q * b)) -
        ∫ σ in t..s, (S.dvpsi σ σ + q))| ≤ Real.sqrt (2 * K * b * chartTranslatedEnergy S T q) := by
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
      (Q := fun x => chartPotential S x.1 x.2) (χ := fun x => ε * chartTranslatedPsi S q x.1 x.2)
      ht hts hs (fun q hq => by
      rw [hPeq q hq, hψeq q hq])
    rw [hψeq (s, t) hq, he, chart_triangleVolterra_const_mul]
    have hv := h.lemmaA3_translated_volterra q ht (htri hq)
    dsimp [g]
    rw [hv]
    ring
  have hpτ := triangleVolterra_positive hP hψ hτ hc hk hb hgsource heq
    τ 0 le_rfl hτ le_rfl
  simpa only [hψeq (τ, 0) ⟨le_rfl, hτ, le_rfl⟩] using hpτ

/-- Either sign of the initial scalar amplitude is bounded by the same square
root. Paper `e1a0fd5`, `eq:observability-axis-amplitude`, lines 1524–1530. -/
theorem lemmaA3_translated_signed_axis (q : ℝ) {ε : ℝ} (hε : |ε| = 1) (hduration : K * b ≤ T) :
    ε * (chartPsi S 0 0 + q * b) ≤ Real.sqrt (2 * K * b * chartTranslatedEnergy S T q) := by
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
  let c := ε * (chartPsi S 0 0 + q * b) - Real.sqrt (2 * K * b * chartTranslatedEnergy S T q)
  have hc : 0 < c := sub_pos.mpr (lt_of_not_ge hlarge)
  have hlower : ∀ s, 0 ≤ s → s < s₀ → c ≤ ε * chartTranslatedPsi S q s 0 := by
    intro s hs hss
    exact h.lemmaA3_translated_signed_lower q hε hc hs (hss.le.trans hsT) (hss.le.trans hsKb)
      (h.before_axis_zero hs hss hsT haxis) le_rfl
  have hseg := h.in_subset (t := 0) (a := 0) (c := s₀) le_rfl hsT le_rfl (by simp [haxis])
  have hcont : ContinuousOn (fun s => ε * chartTranslatedPsi S q s 0) (Icc 0 s₀) :=
    continuousOn_const.mul ((h.lemmaA3_translated_continuous q).comp
      (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => hseg ⟨hs, by simp⟩))
  have hI : Icc 0 s₀ ∈ 𝓝[Iio s₀] s₀ := by
    exact inter_mem (mem_nhdsWithin_of_mem_nhds (Ici_mem_nhds hspos))
      (Filter.mem_of_superset self_mem_nhdsWithin (fun s hs => hs.le))
  have hzero : ε * chartTranslatedPsi S q s₀ 0 = 0 := by
    rw [chartTranslatedPsi, chartPsi]
    have hz := (h.axis_values s₀ ⟨hspos.le, hsT⟩).1
    rw [haxis] at hz
    simp [hz]
  have hlim : Tendsto (fun s => ε * chartTranslatedPsi S q s 0) (𝓝[Iio s₀] s₀) (𝓝 0) := by
    simpa only [hzero] using
      ((hcont s₀ ⟨hspos.le, le_rfl⟩).mono_of_mem_nhdsWithin hI).tendsto
  have hh : c ≤ 0 := ge_of_tendsto hlim (by
    filter_upwards [hI, self_mem_nhdsWithin] with s hs hslt
    exact hlower s hs.1 hslt)
  linarith

/-- Lemma A.2's axis amplitude estimate in the abstract normalized chart.
Paper `e1a0fd5`, `lem:observability-axis-amplitude`,
`eq:observability-axis-amplitude`, lines 1512–1515, 1524–1530. -/
theorem lemmaA3_translated_axis_amplitude (q : ℝ) (hduration : K * b ≤ T) :
    |(chartPsi S 0 0 + q * b)| ^ 2 ≤ 2 * K * b * chartTranslatedEnergy S T q := by
  have hp := h.lemmaA3_translated_signed_axis q (ε := 1) (by norm_num) hduration
  have hn := h.lemmaA3_translated_signed_axis q (ε := -1) (by norm_num) hduration
  have habs : |(chartPsi S 0 0 + q * b)| ≤ Real.sqrt (2 * K * b * chartTranslatedEnergy S T q) := by
    apply abs_le.mpr
    constructor <;> linarith
  have hnon : 0 ≤ 2 * K * b * chartTranslatedEnergy S T q := by
    have hK : 0 ≤ K := by linarith [h.K_ge_one]
    exact mul_nonneg (mul_nonneg (by positivity) h.b_pos.le) (h.lemmaA3_translated_energy_nonneg q)
  nlinarith [Real.sq_sqrt hnon, Real.sqrt_nonneg (2 * K * b * chartTranslatedEnergy S T q),
    abs_nonneg ((chartPsi S 0 0 + q * b))]

end NormalizedChartData

end AcExtensionPrinciple

end
