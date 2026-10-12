module

public import AcExtensionPrinciple.Observability.FromSolutionTerminalPrimitive
public import AcExtensionPrinciple.Observability.FromSolutionJacobian
public import AcExtensionPrinciple.ScalarBound.NuComparison

/-!
# AC of the incoming expansion along a regular cylinder

Paper `e1a0fd5`, `eq:logarithmic-expansions`, lines 1460–1473.
The characteristic identity writes ν_b as ν(u,0) times a regular
integrating factor. The terminal trace is AC in the standing class.
This supplies the BV premise for the inverse outgoing-clock Jacobian.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

namespace DecayCylinder

/-- Interior cylinder points avoid both characteristic edges, including
when the full interval touches those edges. Paper `e1a0fd5`,
lines 664–675 and 1460–1473. -/
theorem source_interior {ui b a₀ a₁ u : ℝ} {S : SSFields}
    (c : DecayCylinder ui S b a₀ a₁) (h : StandingFull ui S)
    (hu : u ∈ Ioo a₀ a₁) : (u, c.v u) ∈ cylinderInterior ui := by
  have hv := (h.cylinderV_spec c.radius_pos
    (h.cylinder_regular_interior (c.regularInterval h) ⟨hu.1.le, hu.2⟩)).1
  rw [c.v_eq_canonical h (Ioo_subset_Icc_self hu)]
  exact ⟨c.initial_le.trans_lt hu.1, hv⟩

/-- The normalized transport factor separates the original outgoing gauge
from a regular function of the physical fields. Paper `e1a0fd5`,
`eq:logarithmic-expansions`, lines 1460–1473. -/
theorem nu_terminal_factor {ui b a₀ a₁ u : ℝ} {S : SSFields}
    (c : DecayCylinder ui S b a₀ a₁) (h : StandingFull ui S)
    (hu : u ∈ Icc a₀ a₁) :
    S.nu u (c.v u) = S.nu u 0 *
      Real.exp (-chartTerminalPrimitive (chartNuCoefficient S) u (c.v u)) := by
  have hp := c.source_mem hu
  have hterminal : (u, 0) ∈ pastTriangle ui :=
    ⟨hp.1, hp.2.1, (c.points u hu).1.le.trans hp.2.2.2, le_rfl⟩
  have hlog := (h.scalar_log_neg_nu_primitive hp.1 hp.2.1
    (c.points u hu).1 (c.points u hu).2.1 (le_refl 0)).2
  have hJ : chartTerminalPrimitive (chartNuCoefficient S) u (c.v u) =
      ∫ s in c.v u..0, S.kappa u s * S.varkappa u s := by
    apply intervalIntegral.integral_congr
    intro s _
    exact chartNuCoefficient_eq S u s
  have he : Real.log (-S.nu u (c.v u)) = Real.log (-S.nu u 0) +
      -chartTerminalPrimitive (chartNuCoefficient S) u (c.v u) := by
    rw [hJ]
    linarith
  have hexp : -S.nu u (c.v u) = -S.nu u 0 *
      Real.exp (-chartTerminalPrimitive (chartNuCoefficient S) u (c.v u)) := by
    rw [← Real.exp_log (neg_pos.mpr (h.nu_neg hp)), he, Real.exp_add,
      Real.exp_log (neg_pos.mpr (h.nu_neg hterminal))]
  linarith

/-- The incoming expansion along the cylinder boundary has bounded variation under the standing
assumptions alone: the terminal trace ν(·,0) is BV by the local BV bounds and the transport factor is
AC. Thus the outgoing inverse-clock Jacobian has BV; no regularity of the original gauge is invented.
Paper `e1a0fd5`, lines 1441–1443 and 1460–1473. -/
theorem negNu_boundedVariation {ui b a₀ a₁ : ℝ} {S : SSFields}
    (c : DecayCylinder ui S b a₀ a₁) (h : StandingFull ui S) :
    BoundedVariationOn (fun u => -S.nu u (c.v u)) (Icc a₀ a₁) := by
  let J := fun u => chartTerminalPrimitive (chartNuCoefficient S) u (c.v u)
  let G := fun u => chartTerminalPrimitive (chartNuCoefficientU S) u (c.v u) -
    chartNuCoefficient S u (c.v u) * (-S.nu u (c.v u) / S.lam u (c.v u))
  have hmap : MapsTo (fun u => (u, c.v u)) (Icc a₀ a₁) (cylinderScalarRegion ui) :=
    fun u hu => ⟨c.initial_le.trans hu.1, (c.points u hu).1, (c.points u hu).2.1⟩
  have hc := continuousOn_id.prodMk c.smooth_v.continuousOn
  have hJC : ContinuousOn J (Icc a₀ a₁) :=
    (chartTerminalPrimitive_continuous h.chart_nuCoefficient_continuous).comp hc hmap
  have hGC : ContinuousOn G (Icc a₀ a₁) :=
    ((chartTerminalPrimitive_continuous h.chart_nuCoefficientU_continuous).comp hc hmap).sub
      ((h.chart_nuCoefficient_continuous.comp hc hmap).mul
        ((c.clock_density_continuous h).div
          (h.regularCenter.continuous_lam.comp hc (fun _ hu => c.source_mem hu))
          (fun _ hu => (h.lam_pos (c.source_mem hu)).ne')))
  have hJD : ∀ u ∈ Ioo a₀ a₁, HasDerivAt J (G u) u := by
    intro u hu
    have hd := chartTerminalPrimitive_hasFDerivAt h.chart_nuCoefficient_continuous
      h.chart_nuCoefficientU_continuous
      (fun _ _ hp hx => h.chart_nuCoefficient_hasDerivAt_in hp hx)
      (c.source_interior h hu)
    have he := hd.comp_hasDerivAt u ((hasDerivAt_id u).prodMk (c.tangent u hu))
    convert he using 1
    · rfl
    · simp only [G, ContinuousLinearMap.coprod_apply, cylinderLinear,
        ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
      ring
  have hAC : AbsolutelyContinuousOnInterval (fun u => Real.exp (-J u)) a₀ a₁ := by
    apply cylinder_ac_of_continuous_derivative (g := fun u => -G u * Real.exp (-J u))
      c.ordered
      (Real.continuous_exp.comp_continuousOn hJC.neg)
      (hGC.neg.mul (Real.continuous_exp.comp_continuousOn hJC.neg))
    intro u hu
    convert (hJD u hu).neg.exp using 1
    · ext x
      simp only [Function.comp_apply, Pi.neg_apply]
    · simp only [Pi.neg_apply, mul_comm]
  have hs := inSeg_subset_triangle c.initial_le c.terminal_negative c.terminal_negative.le le_rfl
  rcases h.regularCenter.localBV.expansion_variation (inSeg 0 a₀ a₁)
    (isCompact_Icc.prod isCompact_singleton) hs with ⟨Cν, _, hνin⟩
  have hterminal : BoundedVariationOn (fun u => S.nu u 0) (Icc a₀ a₁) :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hνin 0 a₀ a₁ c.ordered (Subset.refl _))
  have hneg : BoundedVariationOn (fun u => -S.nu u 0) (Icc a₀ a₁) :=
    (LipschitzWith.id.neg).lipschitzOnWith.comp_boundedVariationOn (mapsTo_univ _ _) hterminal
  have hexp : BoundedVariationOn (fun u => Real.exp (-J u)) (Icc a₀ a₁) := by
    simpa only [uIcc_of_le c.ordered] using hAC.boundedVariationOn
  change eVariationOn _ _ ≠ ⊤
  rw [eVariationOn.congr (g := fun u => -S.nu u 0 * Real.exp (-J u)) (fun u hu => by
    rw [c.nu_terminal_factor h hu]; simp only [J]; ring)]
  exact hneg.fun_mul hexp

/-- The inverse outgoing-clock Jacobian has finite variation after
increasing reparametrization. All regularity premises now come from the
standing source. Paper `e1a0fd5`, lines 1441–1443 and 1460–1473. -/
theorem outgoing_jacobian_boundedVariation {ui b a₀ a₁ K T : ℝ} {S : SSFields}
    (c : DecayCylinder ui S b a₀ a₁) (h : StandingFull ui S)
    (hK : CylinderKBounds ui S K) (U : ℝ → ℝ)
    (hU : MonotoneOn U (Icc 0 T)) (hmap : MapsTo U (Icc 0 T) (Icc a₀ a₁)) :
    BoundedVariationOn (fun s => (-S.nu (U s) (c.v (U s)))⁻¹) (Icc 0 T) := by
  have hBV := c.negNu_boundedVariation h
  have hcomp : BoundedVariationOn (fun s => -S.nu (U s) (c.v (U s))) (Icc 0 T) :=
    ne_top_of_le_ne_top hBV
      (eVariationOn.comp_le_of_monotoneOn (fun u => -S.nu u (c.v u)) U hU hmap)
  apply boundedVariation_chart_reciprocal
    (inv_pos.mpr (zero_lt_one.trans_le hK.1)) hcomp
  intro s hs
  exact c.clock_density_lower hK _ (hmap hs)

end DecayCylinder

end AcExtensionPrinciple

end
