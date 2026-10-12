module

public import AcExtensionPrinciple.Observability.PropA4
public import AcExtensionPrinciple.Observability.PropA4InnerMass
public import AcExtensionPrinciple.Observability.PropA4InnerEnergy
public import AcExtensionPrinciple.Observability.PropA4SmallConstants

/-!
# Small-mass observation from the re-normalized inner chart

Paper `e1a0fd5`, `prop:boundary-mass-observability`, lines 1675–1909.
Every exterior analytic estimate and parameter choice is discharged here.
The inner-coordinate construction is supplied through `InnerChartStatement`;
it preserves the source chart hypotheses and the exact boundary energy.
-/

public section

namespace AcExtensionPrinciple
namespace PropA4

open Set MeasureTheory

/-- Discharge the small-mass analytic argument once the precise inner-chart
construction is supplied. All helper hypotheses, including the three
retained-mass errors and the two observation errors, are discharged from
normalized chart data. Paper `e1a0fd5`, lines 1675–1909. -/
theorem small_mass_estimate_of_inner_chart {K : ℝ} (hK : 1 ≤ K)
    (hchart : InnerChartStatement K) : SmallMassEstimate K := by
  have hK0 : 0 < K := by linarith only [hK]
  obtain ⟨c₃, hc₃, hobs⟩ := inner_observation_of_chart hK
  have hlog : 0 ≤ Real.log (2 * K * (K + 2)) := Real.log_nonneg (by nlinarith only [hK])
  let q₀ := c₃ / ((2 * K * (K + 2)) ^ 3 * (1 + Real.log (2 * K * (K + 2))) ^ 2)
  have hq₀ : 0 < q₀ := by dsimp [q₀]; positivity
  have hCm : 0 ≤ innerMassErrorConstant K := by
    unfold innerMassErrorConstant exteriorMassConstant amplitudeMassSquareConstant
      amplitudeMassErrorConstant
    positivity
  have hCo : 0 ≤ innerObservationUpperConstant K := by
    unfold innerObservationUpperConstant amplitudeMassSquareConstant amplitudeMassErrorConstant
    positivity
  let C := 1 + innerMassErrorConstant K + innerObservationUpperConstant K
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hCoverM : innerMassErrorConstant K ≤ C := by dsimp [C]; linarith only [hCo]
  have hCoverO : innerObservationUpperConstant K ≤ C := by dsimp [C]; linarith only [hCm]
  obtain ⟨L, ε, δ, hL, hε, hε1, hδ, hδK, hεa, hεT, hmassBudget, hscale, hδObs⟩ :=
    choose_small_mass_parameters hK hC hq₀
  have hL0 : 0 < L := by linarith only [hL]
  have hL1 : 1 ≤ L := by linarith only [hL]
  let εa := 1 / (2 * K * (K + 2) * L)
  let H := positiveMassDuration K εa
  have hεa0 : 0 < εa := by dsimp [εa]; positivity
  have hεa1 : εa < 1 := by
    dsimp [εa]
    rw [div_lt_one₀ (by positivity)]
    have hbase : 6 ≤ 2 * K * (K + 2) := by nlinarith only [hK]
    have hh := mul_le_mul_of_nonneg_right hbase hL0.le
    nlinarith only [hh, hL]
  have hH0 : 0 ≤ H := by
    unfold H positiveMassDuration
    exact (show 0 ≤ K + 1 by linarith only [hK]).trans (le_max_left _ _)
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL1
  let q := q₀ / (L ^ 2 * (1 + Real.log L) ^ 2)
  have hq : 0 < q := by dsimp [q]; positivity
  refine ⟨ε, δ, hε, hε1, hδ, ?_⟩
  intro b S h hM hratio
  have hb := h.b_pos
  have hT : K * b ≤ (K + 4) * b := by nlinarith only [hb]
  let P := (K + 2) * S.m 0 0
  have hP : 0 < P := by dsimp [P]; positivity
  have hMP : S.m 0 0 ≤ P := by dsimp [P]; nlinarith only [hK, hM]
  by_contra hn
  have hE : chartScalarEnergy S ((K + 4) * b) ≤ δ * S.m 0 0 := (lt_of_not_ge hn).le
  have hE0 := h.scalar_energy_nonneg
  have hδ1 : δ ≤ 1 := by
    have hd := (le_div_iff₀ (show 0 < 2 * K by positivity)).mp hδK
    nlinarith only [hd, hK, hδ]
  have hEM : chartScalarEnergy S ((K + 4) * b) ≤ S.m 0 0 :=
    hE.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hδ1 hM.le)
  have hEP := hEM.trans hMP
  have hmass (s t : ℝ) (hp : (s, t) ∈ chartCylinder h.g ((K + 4) * b)) : S.m s t ≤ P := by
    have hh := total_mass_bound h hT hδK hE hp
    exact hh.2.1.trans hh.2.2.1
  obtain ⟨hfitRadius, hfitTime⟩ := inner_interval_fits hK hL0 hH0 hb hεa hεT hratio
  change 2 * (L * P) ≤ b at hfitRadius
  change 2 * H * (L * P) ≤ b at hfitTime
  have hfit : 64 * P ≤ b := by nlinarith only [hL, hfitRadius, hP]
  have hcut : 32 * P ≤ L * P := by nlinarith only [hL, hP]
  have hab : L * P < b := by nlinarith only [hfitRadius, hL0, hP]
  have htime : (K + 2) * b + 2 * (H * (L * P)) ≤ (K + 4) * b := by
    nlinarith only [hfitTime, hb]
  have hsmallM : innerMassErrorConstant K *
      (δ + (K + 2) / L + (K + 2) ^ 2 * ε) ≤ 3 / (4 * K) :=
    (mul_le_mul_of_nonneg_right hCoverM (by positivity)).trans hmassBudget
  have hretained (s t : ℝ) (hs : s ∈ Icc 0 ((K + 4) * b))
      (hlate : (K + 2) * b ≤ s) (hp : (s, t) ∈ chartCylinder h.g ((K + 4) * b))
      (hr : S.r s t = L * P) : S.m 0 0 / (4 * K) ≤ S.m s t := by
    have hretain := (total_mass_bound h hT hδK hE (h.boundary_mem hs)).2.2.2
    have hinner := inner_mass_lower_bound h hP hT hmass hs hlate hfit hEP hL
      hp.2.2.1 hp.2.2.2 hr hretain
    exact retain_inner_mass hK hCm hM.le hE hratio hsmallM hinner
  obtain ⟨v, tₐ, inner, huv, hv, hcurve, hc, hmono, hd, ⟨hi⟩, hμeq, hEi, hEq⟩ :=
    hchart b ((K + 4) * b) S h P (L * P) εa ((K + 2) * b)
      hP hmass hcut hab hεa0 hεa1 le_rfl htime
  have hvT : v ≤ (K + 4) * b := hv.trans htime
  have hstart : (K + 2) * b ∈ Icc ((K + 2) * b) v := ⟨le_rfl, huv⟩
  have hpstart := (hcurve ((K + 2) * b) hstart).1
  have hmstart := hretained ((K + 2) * b) (tₐ ((K + 2) * b))
    ⟨hpstart.1, hpstart.2.1⟩ le_rfl hpstart (hcurve ((K + 2) * b) hstart).2
  have hμ : εa ≤ inner.mu 0 0 := by
    rw [hμeq]
    change εa ≤ massRatio (S.r ((K + 2) * b) (tₐ ((K + 2) * b)))
      (S.m ((K + 2) * b) (tₐ ((K + 2) * b)))
    rw [(hcurve ((K + 2) * b) hstart).2]
    exact inner_mass_ratio hK hL0 hM hmstart
  have hLower := inner_observation_lower_scaled hK hL1 hP.le hc₃.le
    (hobs (L * P) εa inner hεa0 hεa1 hi hμ)
  have hLower' : q * P ≤ chartScalarEnergy inner (H * (L * P)) := by
    convert hLower using 1
    dsimp [q, q₀]
    ring
  have hUpper := inner_boundary_energy_upper_scaled h hP hT hmass hfit hEP hL hH0 le_rfl
    huv hvT (by nlinarith only [hv]) tₐ hcurve hc hmono.monotoneOn hd hEi
  rw [← hEq] at hUpper
  have hUpper' : chartScalarEnergy inner (H * (L * P)) ≤
      C * (chartScalarEnergy S ((K + 4) * b) +
        H * (P / L ^ 3 + chartScalarEnergy S ((K + 4) * b) / L ^ 2)) :=
    hUpper.trans (mul_le_mul_of_nonneg_right hCoverO (by positivity))
  have hEPδ : chartScalarEnergy S ((K + 4) * b) ≤ δ * P :=
    hE.trans (mul_le_mul_of_nonneg_left hMP hδ.le)
  exact inner_energy_contradiction hP hC hH0 hL0 hq hscale hδObs hEPδ hLower' hUpper'

/-- Complete the A.4 statement from the exact inner-coordinate interface.
The analytic small-mass obligation has been discharged. Paper `e1a0fd5`,
`prop:boundary-mass-observability`, lines 1665–1913. -/
theorem of_inner_chart {K : ℝ} (hK : 1 ≤ K) (hchart : InnerChartStatement K) : Statement K :=
  of_small_mass_estimate hK (small_mass_estimate_of_inner_chart hK hchart)

end PropA4
end AcExtensionPrinciple

end
