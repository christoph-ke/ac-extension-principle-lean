module

public import AcExtensionPrinciple.Observability.FromSolutionJacobian

/-!
# The incoming inverse coordinate constructed from the source cylinder

Paper `e1a0fd5`, `equations.tex` lines 1460–1473.
Integrating the constantly extended reciprocal expansion gives exactly
the entry labels, with an affine extension of the matching slope.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- A constructed incoming inverse coordinate and its regular Jacobian.
The premises in the constructor below are supplied by the inverse boundary
clock. Paper `e1a0fd5`, lines 1441–1443 and 1460–1473. -/
structure RegularIncomingCoordinate {ui b a₀ a₁ : ℝ} {S : SSFields}
    (c : DecayCylinder ui S b a₀ a₁) (U : ℝ ≃o ℝ) (T : ℝ) where
  V : ℝ ≃o ℝ
  dV : ℝ → ℝ
  derivative : ∀ s, HasDerivAt V (dV s) s
  continuous_jacobian : Continuous dV
  positive_jacobian : ∀ s, 0 < dV s
  boundary : ∀ s ∈ Icc 0 T, V s = c.v (U s)
  boundary_jacobian : ∀ s ∈ Icc 0 T, dV s = (S.lam (U s) (c.v (U s)))⁻¹
  earlier : ∀ s ≤ 0, V s = c.v (U 0) + (S.lam (U 0) (c.v (U 0)))⁻¹ * s
  jacobian_variation : ∀ a d, BoundedVariationOn dV (Icc a d)

/-- Construct the regular incoming coordinate from the physical cylinder
and its inverse boundary clock. Positivity, endpoint matching and Jacobian
BV all follow from the source class. Paper `e1a0fd5`, lines 1460–1473,
regular extension as in line 1422. -/
theorem exists_regularIncomingCoordinate {ui b a₀ a₁ K T : ℝ} {S : SSFields}
    (c : DecayCylinder ui S b a₀ a₁) (h : StandingFull ui S)
    (hK : CylinderKBounds ui S K) (hT : 0 ≤ T) (U : ℝ ≃o ℝ)
    (hmap : MapsTo U (Icc 0 T) (Icc a₀ a₁))
    (hUd : ∀ s ∈ Icc 0 T, HasDerivAt U (-S.nu (U s) (c.v (U s)))⁻¹ s) :
    Nonempty (RegularIncomingCoordinate c U T) := by
  let j := fun s => (S.lam (U s) (c.v (U s)))⁻¹
  have hc := continuousOn_id.prodMk c.smooth_v.continuousOn
  have hLC := h.regularCenter.continuous_lam.comp hc (fun _ hu => c.source_mem hu)
  have hjC : ContinuousOn j (Icc 0 T) :=
    (hLC.comp U.continuous.continuousOn hmap).inv₀
      (fun s hs => (h.lam_pos (c.source_mem (hmap hs))).ne')
  have hjlo : ∀ s ∈ Icc 0 T, (1 : ℝ) ≤ j s := by
    intro s hs
    exact one_le_inv_iff₀.mpr ⟨h.lam_pos (c.source_mem (hmap hs)),
      (h.lam_bounds (c.source_mem (hmap hs))).2⟩
  let e := regularChartClockIso j hT hjC zero_lt_one hjlo
  let V := e.trans (OrderIso.addRight (c.v (U 0)))
  let dV := chartClockDensity j 0 T
  have hVD : ∀ s, HasDerivAt V (dV s) s := by
    intro s
    convert (regularChartClock_hasDerivAt hT hjC s).add_const (c.v (U 0)) using 1
    ext x
    rfl
  have hfC : ContinuousOn (fun s => c.v (U s)) (Icc 0 T) :=
    c.smooth_v.continuousOn.comp U.continuous.continuousOn hmap
  have hfD : ∀ s ∈ Ioo 0 T, HasDerivAt (fun s => c.v (U s)) (j s) s := by
    intro s hs
    have hsC := Ioo_subset_Icc_self hs
    have hsU : U s ∈ Ioo a₀ a₁ :=
      ⟨(hmap (left_mem_Icc.mpr hT)).1.trans_lt (U.strictMono hs.1),
        (U.strictMono hs.2).trans_le (hmap (right_mem_Icc.mpr hT)).2⟩
    have he := (c.tangent (U s) hsU).comp s (hUd s hsC)
    convert he using 1
    · rfl
    · dsimp only [j]
      have hn := (h.nu_neg (c.source_mem (hmap hsC))).ne
      have hl := (h.lam_pos (c.source_mem (hmap hsC))).ne'
      field_simp [hn, hl]
  have hB : ∀ s ∈ Icc 0 T, V s = c.v (U s) := by
    intro s hs
    have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs.1
      (hfC.mono (Icc_subset_Icc le_rfl hs.2))
      (fun x hx => hfD x ⟨hx.1, hx.2.trans_le hs.2⟩)
      ((hjC.mono (Icc_subset_Icc le_rfl hs.2)).intervalIntegrable_of_Icc (μ := volume) hs.1)
    have he : regularChartClock j 0 T s = ∫ x in 0..s, j x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hs.1] at hx
      exact chartClockDensity_eq ⟨hx.1, hx.2.trans hs.2⟩
    change regularChartClock j 0 T s + c.v (U 0) = c.v (U s)
    rw [he, hI]
    ring
  have hBV := c.incoming_jacobian_boundedVariation h hK U (U.monotone.monotoneOn _) hmap
  refine ⟨{
    V := V
    dV := dV
    derivative := hVD
    continuous_jacobian := chartClockDensity_continuous hT hjC
    positive_jacobian := fun s => zero_lt_one.trans_le (chartClockDensity_lower hT hjlo s)
    boundary := hB
    boundary_jacobian := fun _ hs => chartClockDensity_eq hs
    earlier := ?_
    jacobian_variation := fun a d => boundedVariation_chartClockDensity hT hBV }⟩
  intro s hs
  have he : regularChartClock j 0 T s = j 0 * s := by
    unfold regularChartClock
    have heq : (∫ x in 0..s, chartClockDensity j 0 T x) = ∫ _x in 0..s, j 0 := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_ge hs] at hx
      simp only [chartClockDensity, min_eq_left (hx.2.trans hT), max_eq_left hx.2]
    rw [heq]
    simp [mul_comm]
  change regularChartClock j 0 T s + c.v (U 0) = c.v (U 0) + j 0 * s
  rw [he]
  ring

end AcExtensionPrinciple

end
