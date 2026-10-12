module

public import AcExtensionPrinciple.Observability.FromSolutionNuPartials

/-!
# Smooth terminal primitives away from the axis

Paper `e1a0fd5`, `eq:logarithmic-expansions`, lines 1460–1473.
Integrating ν_v/ν to the terminal ray isolates the original outgoing
gauge in the AC function ν(u,0).
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- Primitive from a regular outgoing point to the terminal ray. Paper
`e1a0fd5`, `eq:logarithmic-expansions`, lines 1460–1473. -/
@[expose] noncomputable def chartTerminalPrimitive (F : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  ∫ s in v..0, F u s

/-- A continuous coefficient has a continuous terminal primitive over
the entire closed off-axis region. Paper `e1a0fd5`, lines 1460–1473. -/
theorem chartTerminalPrimitive_continuous {ui : ℝ} {F : ℝ → ℝ → ℝ}
    (hf : ContinuousOn (fun p => F p.1 p.2) (cylinderScalarRegion ui)) :
    ContinuousOn (fun p => chartTerminalPrimitive F p.1 p.2) (cylinderScalarRegion ui) := by
  intro p hp
  let U := (p.1 + p.2) / 2
  let a := (U + p.2) / 2
  have huU : p.1 < U := by dsimp [U]; linarith [hp.2.1]
  have hUa : U < a := by dsimp [a, U]; linarith [hp.2.1]
  have hav : a < p.2 := by dsimp [a, U]; linarith [hp.2.1]
  have ha0 : a ≤ 0 := hav.le.trans hp.2.2
  have hrect := cylinder_rectangle_subset_region (ui := ui) hUa (le_refl 0)
  have hc := cylinder_rectangle_primitive_continuous_out (F := F)
    (hp.1.trans huU.le) ha0 (hf.mono hrect)
  have htop : ContinuousOn (fun q : ℝ × ℝ => ∫ s in a..0, F q.1 s)
      (Icc ui U ×ˢ Icc a 0) :=
    hc.comp (continuous_fst.prodMk continuous_const).continuousOn
      (fun q hq => ⟨hq.1, ⟨ha0, le_rfl⟩⟩)
  have hterminal : ContinuousOn (fun q : ℝ × ℝ => chartTerminalPrimitive F q.1 q.2)
      (Icc ui U ×ˢ Icc a 0) := by
    apply (htop.sub hc).congr
    intro q hq
    have hslice : ContinuousOn (F q.1) (Icc a 0) :=
      (hf.mono hrect).comp (continuous_const.prodMk continuous_id).continuousOn
        (fun s hs => ⟨hq.1, hs⟩)
    have he := intervalIntegral.integral_add_adjacent_intervals
      ((hslice.mono (Icc_subset_Icc le_rfl hq.2.2)).intervalIntegrable_of_Icc
        (μ := volume) hq.2.1)
      ((hslice.mono (Icc_subset_Icc hq.2.1 le_rfl)).intervalIntegrable_of_Icc
        (μ := volume) hq.2.2)
    dsimp only [chartTerminalPrimitive, Pi.sub_apply]
    linarith
  apply (hterminal p ⟨⟨hp.1, huU.le⟩, ⟨hav.le, hp.2.2⟩⟩).mono_of_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin,
    ((continuous_fst.tendsto p).eventually (Iio_mem_nhds huU)).filter_mono nhdsWithin_le_nhds,
    ((continuous_snd.tendsto p).eventually (Ioi_mem_nhds hav)).filter_mono nhdsWithin_le_nhds]
    with q hq hqU hqa
  exact ⟨⟨hq.1, hqU.le⟩, ⟨hqa.le, hq.2.2⟩⟩

/-- Differentiation under the terminal integral in the incoming parameter
includes the terminal integration endpoint. Paper `e1a0fd5`, lines 1460–1473. -/
theorem chartTerminalPrimitive_hasDerivAt_in {ui u v : ℝ} {F Fu : ℝ → ℝ → ℝ}
    (hp : (u, v) ∈ cylinderScalarRegion ui) (hu : ui < u)
    (hf : ContinuousOn (fun p => F p.1 p.2) (cylinderScalarRegion ui))
    (hfu : ContinuousOn (fun p => Fu p.1 p.2) (cylinderScalarRegion ui))
    (hd : ∀ x y, (x, y) ∈ cylinderScalarRegion ui → ui < x →
      HasDerivAt (fun x => F x y) (Fu x y) x) :
    HasDerivAt (fun x => chartTerminalPrimitive F x v)
      (chartTerminalPrimitive Fu u v) u := by
  let U := (u + v) / 2
  have huU : u < U := by dsimp [U]; linarith [hp.2.1]
  have hUv : U < v := by dsimp [U]; linarith [hp.2.1]
  have hmap : MapsTo Prod.swap (Icc v 0 ×ˢ Icc ui U) (cylinderScalarRegion ui) :=
    fun p hp' => ⟨hp'.2.1, hp'.2.2.trans_lt (hUv.trans_le hp'.1.1), hp'.1.2⟩
  exact cylinder_rectangle_integral_hasDerivAt (F := fun s x => F x s)
    (Fv := fun s x => Fu x s) hp.2.2 (hu.le.trans huU.le) ⟨hp.2.2, le_rfl⟩
    ⟨hu, huU⟩ (hf.comp (continuous_snd.prodMk continuous_fst).continuousOn hmap)
    (hfu.comp (continuous_snd.prodMk continuous_fst).continuousOn hmap)
    (fun s hs x hx => hd x s
      ⟨hx.1.le, hx.2.trans (hUv.trans_le hs.1), hs.2⟩ hx.1)

/-- The outgoing derivative of a terminal primitive is minus its
integrand. Paper `e1a0fd5`, lines 1460–1473. -/
theorem chartTerminalPrimitive_hasDerivAt_out {ui u v : ℝ} {F : ℝ → ℝ → ℝ}
    (hp : (u, v) ∈ cylinderScalarRegion ui) (hv : v < 0)
    (hf : ContinuousOn (fun p => F p.1 p.2) (cylinderScalarRegion ui)) :
    HasDerivAt (chartTerminalPrimitive F u) (-F u v) v := by
  have hc : ContinuousOn (F u) (Ioc u 0) :=
    hf.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun s hs => ⟨hp.1, hs.1, hs.2⟩)
  exact intervalIntegral.integral_hasDerivAt_left
    ((hc.mono (fun s hs => ⟨hp.2.1.trans_le hs.1, hs.2⟩)).intervalIntegrable_of_Icc
      (μ := volume) hp.2.2)
    ⟨Ioc u 0, Ioc_mem_nhds hp.2.1 hv, hc.aestronglyMeasurable measurableSet_Ioc⟩
    (hc.continuousAt (Ioc_mem_nhds hp.2.1 hv))

/-- The terminal primitive of ν_v/ν has a continuous total derivative at
interior off-axis points. Paper `e1a0fd5`, lines 1460–1473. -/
theorem chartTerminalPrimitive_hasFDerivAt {ui : ℝ} {F Fu : ℝ → ℝ → ℝ}
    (hf : ContinuousOn (fun p => F p.1 p.2) (cylinderScalarRegion ui))
    (hfu : ContinuousOn (fun p => Fu p.1 p.2) (cylinderScalarRegion ui))
    (hd : ∀ x y, (x, y) ∈ cylinderScalarRegion ui → ui < x →
      HasDerivAt (fun x => F x y) (Fu x y) x)
    {p : ℝ × ℝ} (hp : p ∈ cylinderInterior ui) :
    HasFDerivAt (fun p => chartTerminalPrimitive F p.1 p.2)
      ((cylinderLinear (chartTerminalPrimitive Fu p.1 p.2)).coprod
        (cylinderLinear (-F p.1 p.2))) p :=
  (cylinder_strict_derivative_of_partials
    (f := chartTerminalPrimitive F) (fu := chartTerminalPrimitive Fu) (fv := fun u v => -F u v)
    (fun _ hq => chartTerminalPrimitive_hasDerivAt_in
      (cylinderInterior_subset_scalarRegion ui hq) hq.1 hf hfu hd)
    (fun _ hq => chartTerminalPrimitive_hasDerivAt_out
      (cylinderInterior_subset_scalarRegion ui hq) hq.2.2 hf)
    ((chartTerminalPrimitive_continuous hfu).mono (cylinderInterior_subset_scalarRegion ui))
    (hf.neg.mono (cylinderInterior_subset_scalarRegion ui)) hp).hasFDerivAt

end AcExtensionPrinciple

end
