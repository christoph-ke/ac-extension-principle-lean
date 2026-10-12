module

public import AcExtensionPrinciple.Observability.Chart
public import AcExtensionPrinciple.Gauge.Primitive
public import AcExtensionPrinciple.Decay.ClassCylinderStatements
public import AcExtensionPrinciple.Sanity.FlatStanding
public import Mathlib.Analysis.Calculus.Deriv.Abs
public import Mathlib.Tactic

/-!
# Regularity needed for the earlier incoming-label extension

Paper `e1a0fd5`, `equations.tex` line 1460. An increasing extension alone
need not give the continuous expansion required by the normalized-chart
Interface. This explicit corner shows why the extension must have a matching derivative
at the join; a regular extension can still be constructed.
-/

public section

namespace AcExtensionPrinciple

open Set

namespace IncomingExtensionObstruction

/-- An incoming inverse coordinate agreeing with `t-1` for entering rays and
extended increasingly with slope two for earlier rays. Paper `e1a0fd5`,
`equations.tex` line 1460, extension-regularity audit. -/
@[expose] noncomputable def incoming (t : ℝ) : ℝ :=
  3 / 2 * t - 1 / 2 * |t| - 1

/-- The entering-ray labels have the required normalization. Paper `e1a0fd5`,
`equations.tex` lines 1460–1465. -/
theorem incoming_nonneg {t : ℝ} (ht : 0 ≤ t) : incoming t = t - 1 := by
  rw [incoming, abs_of_nonneg ht]
  ring

/-- Earlier labels are still strictly increasing. Paper `e1a0fd5`,
`equations.tex` line 1460, extension-regularity audit. -/
theorem incoming_nonpos {t : ℝ} (ht : t ≤ 0) : incoming t = 2 * t - 1 := by
  rw [incoming, abs_of_nonpos ht]
  ring

/-- The inverse incoming coordinate is continuous and strictly increasing.
Paper `e1a0fd5`, `equations.tex` line 1460, extension-regularity audit. -/
theorem incoming_continuous_strictMono : Continuous incoming ∧ StrictMono incoming := by
  constructor
  · unfold incoming
    fun_prop
  · intro x y hxy
    by_cases hx : 0 ≤ x
    · rw [incoming_nonneg hx, incoming_nonneg (hx.trans hxy.le)]
      linarith
    · by_cases hy : y ≤ 0
      · rw [incoming_nonpos (le_of_not_ge hx), incoming_nonpos hy]
        linarith
      · rw [incoming_nonpos (le_of_not_ge hx), incoming_nonneg (le_of_not_ge hy)]
        linarith

/-- The extension is a total invertible coordinate, not merely an injection.
Paper `e1a0fd5`, `equations.tex` line 1460, extension-regularity audit. -/
theorem incoming_surjective : Function.Surjective incoming := by
  intro v
  by_cases hv : -1 ≤ v
  · refine ⟨v + 1, ?_⟩
    rw [incoming_nonneg (by linarith)]
    ring
  · refine ⟨(v + 1) / 2, ?_⟩
    rw [incoming_nonpos (by linarith)]
    ring

/-- The flat radius after outgoing normalization `u=s-2` and this incoming
extension. Paper `e1a0fd5`, lines 1460–1465, extension-regularity audit. -/
@[expose] noncomputable def radius (s t : ℝ) : ℝ := incoming t - (s - 2)

/-- The outer boundary still has radius one. Paper `e1a0fd5`,
`eq:observability-boundary-gauge`, lines 1460–1465. -/
theorem radius_boundary {s : ℝ} (hs : 0 ≤ s) : radius s s = 1 := by
  rw [radius, incoming_nonneg hs]
  ring

/-- The strictly increasing extension creates a corner on an outgoing slice.
Paper `e1a0fd5`, `equations.tex` line 1460, extension-regularity audit. -/
theorem radius_not_differentiable (s : ℝ) :
    ¬ DifferentiableAt ℝ (radius s) 0 := by
  intro h
  have hd := (differentiableAt_id.const_mul (3 / 2 : ℝ)).sub
    (h.add_const (s - 1))
  have he : (fun t : ℝ => 3 / 2 * t - (radius s t + (s - 1))) =
      (fun t : ℝ => 1 / 2 * |t|) := by
    funext t
    simp only [radius, incoming]
    ring
  change DifferentiableAt ℝ (fun t : ℝ => 3 / 2 * t - (radius s t + (s - 1))) 0 at hd
  rw [he] at hd
  have habs := hd.const_mul (2 : ℝ)
  apply not_differentiableAt_abs_zero
  convert habs using 1
  funext t
  ring

/-- The chart interface forces a differentiable outgoing radius wherever the
incoming label is interior to a slice. Paper `e1a0fd5`, line 1460, audit of
`NormalizedChartData.continuous_lam` and `equations.radius_t`. -/
theorem chart_radius_differentiable {b T K s t : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hs : s ∈ Icc 0 T)
    (htg : h.g s < t) (hts : t < s) : DifferentiableAt ℝ (S.r s) t := by
  have hc : ContinuousOn (S.lam s) (Icc (h.g s) s) :=
    h.continuous_lam.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun z hz => h.out_subset hs le_rfl le_rfl ⟨by simp, hz⟩)
  have hd := hasDerivWithinAt_of_intervalPrimitives
    (fun y hy => h.equations.radius_t s (h.g s) y hy.1
      (h.out_subset hs le_rfl hy.2)) hc ⟨htg.le, hts.le⟩
  exact (hd.hasDerivAt (Icc_mem_nhds htg hts)).differentiableAt

/-- No normalized chart containing `t=0` in the interior of a positive-time
slice can have this radius. The failed fields are continuous λ together with
its radius primitive equation. Paper `e1a0fd5`, lines 1460–1465. -/
theorem no_chart_with_corner {b T K : ℝ} {S : SSFields}
    (hr : S.r = radius) (h : NormalizedChartData b T K S)
    {s : ℝ} (hs : s ∈ Icc 0 T) (hs0 : 0 < s) (hg : h.g s < 0) : False := by
  have hd := chart_radius_differentiable h hs hg hs0
  rw [hr] at hd
  exact radius_not_differentiable s hd

/-- The source of the counterexample satisfies the complete standing class.
Paper `e1a0fd5`, `equations.tex` line 1460, extension-regularity audit. -/
theorem source_standing : StandingFull (-4) (flat 0) :=
  flat_standing_full (-4) 0 (by norm_num)

/-- The strongest possible geometric constant K=1 is available in the
counterexample. Paper `e1a0fd5`, lines 742–749 and 1460. -/
theorem source_K : CylinderKBounds (-4) (flat 0) 1 := by
  simp [CylinderKBounds, flat, scaledFlat, SSFields.mu, massRatio]

/-- A radius-one regular flat cylinder, with boundary clock already anchored
at its initial point. Paper `e1a0fd5`, lines 664–675 and 1460. -/
@[expose] noncomputable def sourceCylinder : DecayCylinder (-4) (flat 0) 1 (-2) (-3 / 2) where
  v u := u + 1
  tau u := u + 2
  radius_pos := by norm_num
  initial_le := by norm_num
  ordered := by norm_num
  terminal_negative := by norm_num
  points u hu := by
    refine ⟨by linarith, by linarith [hu.2], ?_⟩
    simp [flat, scaledFlat]
  smooth_v := by fun_prop
  tangent u _ := by simpa [flat, scaledFlat] using (hasDerivAt_id u).add_const 1
  continuous_tau := by fun_prop
  clock a d _ _ _ := by
    refine ⟨?_, ?_⟩
    · simpa only [flat, scaledFlat, neg_neg] using
        (intervalIntegrable_const :
          IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) MeasureTheory.volume a d)
    · simp [flat, scaledFlat]

/-- The terminal radial margin holds on this source cylinder. Paper `e1a0fd5`, lines 664–675,
extension-regularity audit of line 1460. -/
theorem source_terminal_radius :
    ∀ u ∈ Icc (-2 : ℝ) (-3 / 2), 1 ≤ (flat 0).r u 0 := by
  intro u hu
  simp only [flat, scaledFlat, one_mul, zero_sub]
  linarith [hu.2]

/-- The source boundary duration is one half. Paper `e1a0fd5`, line 1460,
extension-regularity audit. -/
theorem source_duration : sourceCylinder.tau (-3 / 2) - sourceCylinder.tau (-2) = 1 / 2 := by
  norm_num [sourceCylinder]

/-- For entering rays this is precisely the boundary-entry coordinate and
the shifted boundary clock prescribed in the paper. Paper `e1a0fd5`,
`equations.tex` line 1460, extension-regularity audit. -/
theorem source_entry_labels {s : ℝ} (hs : 0 ≤ s) :
    incoming s = sourceCylinder.v (s - 2) ∧
      sourceCylinder.tau (s - 2) - sourceCylinder.tau (-2) = s := by
  rw [incoming_nonneg hs]
  simp [sourceCylinder]
  ring

/-- The radius above is the actual pullback of the standing flat solution,
by U(s)=s-2 and the increasing incoming extension. Paper `e1a0fd5`,
`equations.tex` line 1460, extension-regularity audit. -/
theorem radius_eq_source (s t : ℝ) : radius s t = (flat 0).r (s - 2) (incoming t) := by
  simp [radius, flat, scaledFlat]

/-- A standing solution and a regular cylinder do not make an arbitrary
increasing extension compatible with the chart interface. Even allowing
every derivative field and axis graph to vary cannot repair its radius.
Paper `e1a0fd5`, `equations.tex` lines 1460–1465. -/
theorem no_normalized_chart {K : ℝ} {S : SSFields} (hr : S.r = radius) :
    ¬ Nonempty (NormalizedChartData 1 (1 / 2) K S) := by
  rintro ⟨h⟩
  have hs : (1 / 4 : ℝ) ∈ Icc 0 (1 / 2) := by constructor <;> norm_num
  have hg : h.g (1 / 4) < 0 := by
    by_contra hn
    have ha := (h.axis_values (1 / 4) hs).1
    rw [hr] at ha
    simp only [radius, incoming_nonneg (le_of_not_gt hn)] at ha
    linarith [le_of_not_gt hn]
  exact no_chart_with_corner hr h hs (by norm_num) hg

end IncomingExtensionObstruction

end AcExtensionPrinciple

end
