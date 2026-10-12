module

public import AcExtensionPrinciple.Observability.FromSolution
public import AcExtensionPrinciple.Observability.ChartEquations

/-!
# The exact observability premise and its change of boundary measure

Paper `e1a0fd5`, `prop:boundary-observability`, lines 1453–1456,
`eq:imported-boundary-observability`, lines 762–769, and 1923–1929.
Prop A.1 is an explicit helper premise, proved by `PropA1.of_constructed_inner_chart`
in `Observability/InnerChartObservability.lean`. Its constants precede radii, charts,
and scalar translations. The physical chart interface is proved by
`cylinder_chart_realization` in `Observability/FromSolutionRealization.lean`.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory Filter

/-- Prop A.1 in the normalized chart, for every scalar translation and with
constants chosen from K alone. Along r=b a constant scalar translation
subtracts c from ψ_r and leaves dψ_b/ds unchanged. Paper `e1a0fd5`,
`prop:boundary-observability`, lines 1453–1456, 1475–1480, 1923–1929. -/
@[expose] def PropA1Statement (K : ℝ) : Prop :=
  ∃ H sigma : ℝ, 0 < H ∧ 0 < sigma ∧ sigma ≤ 1 ∧
    ∀ b (S : SSFields), NormalizedChartData b (H * b) K S → ∀ c : ℝ,
      sigma * b / 2 * ((S.phi 0 0 - c) ^ 2 - Real.log (1 - S.mu 0 0)) ≤
        ∫ s in 0..H * b, (S.dvpsi s s - c) ^ 2 +
          deriv (fun s => chartPsi S s s) s ^ 2

/-- The physical observability inequality, with dτ_b=(-ν_b)du. This is
exactly `eq:imported-boundary-observability` in the original parameter,
including every subinterval and every scalar constant. Paper `e1a0fd5`,
lines 762–769 and 1923–1929. -/
@[expose] def CylinderObservabilityBound (ui : ℝ) (S : SSFields) (H sigma : ℝ) : Prop :=
  ∀ b a₀ a₁ (c : DecayCylinder ui S b a₀ a₁) a d,
    a₀ ≤ a → a ≤ d → d ≤ a₁ → c.tau d - c.tau a = H * b → ∀ shift : ℝ,
      sigma * b / 2 * ((cylinderPhi S c a - shift) ^ 2 -
        Real.log (1 - S.mu a (c.v a))) ≤
      ∫ u in a..d, (-S.nu u (c.v u)) * (cylinderDatum S c u - shift) ^ 2 +
        b ^ 2 * deriv (cylinderPhi S c) u ^ 2 / (-S.nu u (c.v u))

/-- Exact conversion of the normalized boundary integral to the u parameter. The gauge segment is
supplied by the clock primitive; the two boundary identifications are the radial identity and AC
inverse-clock chain rule. Paper `e1a0fd5`, `equations.tex` lines 1923–1927. -/
theorem normalized_observation_integral_eq
    {ui b a₀ a₁ a d T : ℝ} {S S' : SSFields}
    (c : DecayCylinder ui S b a₀ a₁) (F w : ℝ → ℝ)
    (hF : GaugeSegment F w a d) (hFa : F a = 0) (hFd : F d = T)
    (hw : ∀ᵐ u ∂volume, u ∈ uIoc a d → w u = -S.nu u (c.v u) ∧ w u ≠ 0)
    (hP : ∀ᵐ u ∂volume, u ∈ uIoc a d → S'.dvpsi (F u) (F u) = cylinderDatum S c u)
    (hpsi : ∀ᵐ u ∂volume, u ∈ uIoc a d →
      deriv (fun s => chartPsi S' s s) (F u) = b * deriv (cylinderPhi S c) u / w u)
    (shift : ℝ) :
    (∫ s in 0..T, (S'.dvpsi s s - shift) ^ 2 + deriv (fun s => chartPsi S' s s) s ^ 2) =
      ∫ u in a..d, (-S.nu u (c.v u)) * (cylinderDatum S c u - shift) ^ 2 +
        b ^ 2 * deriv (cylinderPhi S c) u ^ 2 / (-S.nu u (c.v u)) := by
  have he := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (g := fun s => (S'.dvpsi s s - shift) ^ 2 + deriv (fun s => chartPsi S' s s) s ^ 2)
    hF.continuous hF.hasDeriv hF.nonneg
  simp only [hFa, hFd, Function.comp_apply] at he
  rw [← he]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hw, hP, hpsi] with u hwu hPu hpsiu
  intro hu
  rw [hPu hu, hpsiu hu]
  have hn := (hwu hu).2
  rw [← (hwu hu).1]
  field_simp

/-- For actual inverse coordinates, AC of the original scalar trace suffices for the full
boundary-measure conversion. Clock monotonicity, substitution, and a.e. differentiation are proved
from the class and clock; the remaining premises identify the normalized coordinates and their
inverse Jacobians. Paper `e1a0fd5`, `equations.tex` lines 1460–1465 and 1923–1927. -/
theorem normalized_clock_observation_integral_eq
    {ui b a₀ a₁ a d T : ℝ} {S : SSFields}
    (h : StandingFull ui S) (c : DecayCylinder ui S b a₀ a₁)
    (ha : a₀ ≤ a) (had : a ≤ d) (hd : d ≤ a₁)
    (htime : c.tau d - c.tau a = T)
    (U V dU dV : ℝ → ℝ)
    (hphi : AbsolutelyContinuousOnInterval (cylinderPhi S c) a d)
    (hU : ∀ u ∈ Icc a d, U (normalizedCylinderClock c a u) = u)
    (hUd : ∀ u ∈ Ioo a d,
      HasDerivAt U (-S.nu u (c.v u))⁻¹ (normalizedCylinderClock c a u))
    (hVd : ∀ u ∈ Icc a d,
      dV (normalizedCylinderClock c a u) = (S.lam u (c.v u))⁻¹)
    (hB : ∀ z ∈ Icc 0 T, U z ∈ Icc a₀ a₁ ∧ V z = c.v (U z)) (shift : ℝ) :
    (∫ s in 0..T, ((S.normalizedPullback U V dU dV 0).dvpsi s s - shift) ^ 2 +
      deriv (fun s => chartPsi (S.normalizedPullback U V dU dV 0) s s) s ^ 2) =
      ∫ u in a..d, (-S.nu u (c.v u)) * (cylinderDatum S c u - shift) ^ 2 +
        b ^ 2 * deriv (cylinderPhi S c) u ^ 2 / (-S.nu u (c.v u)) := by
  let F := normalizedCylinderClock c a
  have hFa : F a = 0 := by simp [F, normalizedCylinderClock]
  have hFd : F d = T := htime
  have hF := (normalizedCylinderClock_strictMonoOn h c a).mono (Icc_subset_Icc ha hd)
  have hmem {u : ℝ} (hu : u ∈ Icc a d) : u ∈ Icc a₀ a₁ :=
    ⟨ha.trans hu.1, hu.2.trans hd⟩
  have hp {u : ℝ} (hu : u ∈ Icc a d) : (u, c.v u) ∈ pastTriangle ui :=
    ⟨c.initial_le.trans (hmem hu).1, (hmem hu).2.trans_lt c.terminal_negative,
      (c.points u (hmem hu)).1.le, (c.points u (hmem hu)).2.1⟩
  have hFmem (u : ℝ) (hu : u ∈ Icc a d) : F u ∈ Icc 0 T := by
    rw [← hFa, ← hFd]
    exact ⟨hF.monotoneOn (left_mem_Icc.mpr had) hu hu.1,
      hF.monotoneOn hu (right_mem_Icc.mpr had) hu.2⟩
  apply normalized_observation_integral_eq c F (fun u => -S.nu u (c.v u))
    (normalizedCylinderClock_gaugeSegment h c ha had hd) hFa hFd
  · filter_upwards with u hu
    rw [uIoc_of_le had] at hu
    exact ⟨rfl, (neg_pos.mpr (h.nu_neg (hp ⟨hu.1.le, hu.2⟩))).ne'⟩
  · filter_upwards with u hu
    rw [uIoc_of_le had] at hu
    have huC : u ∈ Icc a d := ⟨hu.1.le, hu.2⟩
    have hb := hB (F u) (hFmem u huC)
    have hUi : U (F u) = u := hU u huC
    have hVi : dV (F u) = (S.lam u (c.v u))⁻¹ := hVd u huC
    simp only [SSFields.normalizedPullback, hb.2, hUi, hVi,
      zero_mul, sub_zero, cylinderDatum, div_eq_mul_inv]
  · have hpsi := normalizedPullback_boundary_psi_ae_deriv c F U V dU dV
      hphi hF hFa hFd hU hUd hB
    filter_upwards [hpsi, show ∀ᵐ u : ℝ, u ≠ d by simp [ae_iff]] with u hu hune huI
    rw [uIoc_of_le had] at huI
    exact hu ⟨huI.1, lt_of_le_of_ne huI.2 hune⟩

/-- Transport one chart estimate to one physical interval. The initial-value identities follow from
`normalizedPullback_initial_energy`; integral equality is proved by
`normalized_observation_integral_eq`. Existence of this chart is supplied by
`normalized_chart_from_solution` in `Observability/FromSolutionChart.lean`. Paper `e1a0fd5`, lines
762–769 and 1923–1929. -/
theorem cylinder_observation_of_normalized
    {ui b a₀ a₁ a d H sigma K : ℝ} {S S' : SSFields}
    (c : DecayCylinder ui S b a₀ a₁)
    (_hchart : NormalizedChartData b (H * b) K S')
    (hobs : ∀ shift : ℝ,
      sigma * b / 2 * ((S'.phi 0 0 - shift) ^ 2 - Real.log (1 - S'.mu 0 0)) ≤
        ∫ s in 0..H * b, (S'.dvpsi s s - shift) ^ 2 + deriv (fun s => chartPsi S' s s) s ^ 2)
    (hphi : S'.phi 0 0 = cylinderPhi S c a)
    (hmu : S'.mu 0 0 = S.mu a (c.v a))
    (hintegral : ∀ shift : ℝ,
      (∫ s in 0..H * b, (S'.dvpsi s s - shift) ^ 2 + deriv (fun s => chartPsi S' s s) s ^ 2) =
        ∫ u in a..d, (-S.nu u (c.v u)) * (cylinderDatum S c u - shift) ^ 2 +
          b ^ 2 * deriv (cylinderPhi S c) u ^ 2 / (-S.nu u (c.v u))) (shift : ℝ) :
    sigma * b / 2 * ((cylinderPhi S c a - shift) ^ 2 - Real.log (1 - S.mu a (c.v a))) ≤
      ∫ u in a..d, (-S.nu u (c.v u)) * (cylinderDatum S c u - shift) ^ 2 +
        b ^ 2 * deriv (cylinderPhi S c) u ^ 2 / (-S.nu u (c.v u)) := by
  simpa only [hphi, hmu, hintegral] using hobs shift

/-- The normalized chart and exact boundary transport on every physical interval.
This internal interface is proved by `cylinder_chart_realization` in
`Observability/FromSolutionRealization.lean`. Paper `e1a0fd5`,
`equations.tex` lines 1460–1473 and 1923–1929. -/
@[expose] def CylinderChartRealization (ui : ℝ) (S : SSFields) (K H : ℝ) : Prop :=
  ∀ b a₀ a₁ (c : DecayCylinder ui S b a₀ a₁) a d,
    a₀ ≤ a → a ≤ d → d ≤ a₁ → c.tau d - c.tau a = H * b →
    ∃ S' : SSFields, Nonempty (NormalizedChartData b (H * b) K S') ∧
      S'.phi 0 0 = cylinderPhi S c a ∧ S'.mu 0 0 = S.mu a (c.v a) ∧
      ∀ shift : ℝ,
        (∫ s in 0..H * b, (S'.dvpsi s s - shift) ^ 2 + deriv (fun s => chartPsi S' s s) s ^ 2) =
          ∫ u in a..d, (-S.nu u (c.v u)) * (cylinderDatum S c u - shift) ^ 2 +
            b ^ 2 * deriv (cylinderPhi S c) u ^ 2 / (-S.nu u (c.v u))

/-- The chart estimate and its boundary measure realization discharge the physical observability
premise. Paper `e1a0fd5`, lines 762–769, 1460–1473 and 1923–1929. -/
theorem cylinder_observability_of_chart_realization {ui K H sigma : ℝ} {S : SSFields}
    (hcharts : CylinderChartRealization ui S K H)
    (hobs : ∀ b (S' : SSFields), NormalizedChartData b (H * b) K S' → ∀ shift : ℝ,
      sigma * b / 2 * ((S'.phi 0 0 - shift) ^ 2 - Real.log (1 - S'.mu 0 0)) ≤
        ∫ s in 0..H * b, (S'.dvpsi s s - shift) ^ 2 + deriv (fun s => chartPsi S' s s) s ^ 2) :
    CylinderObservabilityBound ui S H sigma := by
  intro b a₀ a₁ c a d ha had hd htime shift
  obtain ⟨S', ⟨hchart⟩, hphi, hmu, hi⟩ := hcharts b a₀ a₁ c a d ha had hd htime
  exact cylinder_observation_of_normalized c hchart (hobs b S' hchart) hphi hmu hi shift

end AcExtensionPrinciple

end
