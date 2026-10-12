module

public import AcExtensionPrinciple.Observability.FromSolution
public import Mathlib.Topology.Order.MonotoneContinuity
public import Mathlib.Topology.Order.ProjIcc

/-!
# A global inverse for the regular boundary clock

Paper `e1a0fd5`, `equations.tex` line 1460 and `eq:cylinder-time`.
The clock density is extended constantly beyond both endpoints. Its
uniform positive lower bound gives an increasing global inverse.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- Constant endpoint extension of a clock density. Paper `e1a0fd5`,
line 1460 and the regular extension at line 1422. -/
@[expose] noncomputable def chartClockDensity (w : ℝ → ℝ) (a d x : ℝ) : ℝ :=
  w (max a (min x d))

/-- A clock with affine extensions on both sides of its physical interval.
Paper `e1a0fd5`, line 1460 and `eq:cylinder-time`, lines 671–673. -/
@[expose] noncomputable def regularChartClock (w : ℝ → ℝ) (a d x : ℝ) : ℝ :=
  ∫ y in a..x, chartClockDensity w a d y

/-- Constant endpoint extension agrees with the original density on its
interval. Paper `e1a0fd5`, line 1460 and `eq:cylinder-time`. -/
theorem chartClockDensity_eq {w : ℝ → ℝ} {a d x : ℝ} (hx : x ∈ Icc a d) :
    chartClockDensity w a d x = w x := by
  simp only [chartClockDensity, min_eq_left hx.2, max_eq_right hx.1]

/-- The density extension is continuous globally, including both joins.
Paper `e1a0fd5`, lines 1422 and 1460. -/
theorem chartClockDensity_continuous {w : ℝ → ℝ} {a d : ℝ} (had : a ≤ d)
    (hw : ContinuousOn w (Icc a d)) : Continuous (chartClockDensity w a d) :=
  hw.comp_continuous (continuous_const.max (continuous_id.min continuous_const))
    (fun _ => ⟨le_max_left _ _, max_le had (min_le_right _ _)⟩)

/-- The clock has the prescribed derivative everywhere, including the
affine joins. Paper `e1a0fd5`, lines 1422, 1460 and 671–673. -/
theorem regularChartClock_hasDerivAt {w : ℝ → ℝ} {a d : ℝ} (had : a ≤ d)
    (hw : ContinuousOn w (Icc a d)) (x : ℝ) :
    HasDerivAt (regularChartClock w a d) (chartClockDensity w a d x) x := by
  have hc := chartClockDensity_continuous had hw
  exact intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable _ _) (hc.stronglyMeasurableAtFilter volume (𝓝 x)) hc.continuousAt

/-- A positive density bound survives the endpoint extension. Paper
`e1a0fd5`, lines 742–749 and 1460. -/
theorem chartClockDensity_lower {w : ℝ → ℝ} {a d c : ℝ} (had : a ≤ d)
    (hw : ∀ x ∈ Icc a d, c ≤ w x) (x : ℝ) :
    c ≤ chartClockDensity w a d x :=
  hw _ ⟨le_max_left _ _, max_le had (min_le_right _ _)⟩

/-- The clock separates distinct labels by the geometric lower bound.
Paper `e1a0fd5`, lines 742–749 and 1460. -/
theorem regularChartClock_increment_lower {w : ℝ → ℝ} {a d c x y : ℝ}
    (had : a ≤ d) (hw : ContinuousOn w (Icc a d))
    (hlo : ∀ x ∈ Icc a d, c ≤ w x) (hxy : x ≤ y) :
    c * (y - x) ≤ regularChartClock w a d y - regularChartClock w a d x := by
  have hc := chartClockDensity_continuous had hw
  have he := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) a x) (hc.intervalIntegrable (μ := volume) x y)
  have hmono : c * (y - x) ≤ ∫ z in x..y, chartClockDensity w a d z := by
    calc
      _ = ∫ _z in x..y, c := by simp [mul_comm]
      _ ≤ _ := intervalIntegral.integral_mono_on hxy intervalIntegrable_const
        (hc.intervalIntegrable x y) (fun z _ => chartClockDensity_lower had hlo z)
  dsimp only [regularChartClock]
  linarith

/-- A strictly positive density gives a strictly increasing extended
clock. Paper `e1a0fd5`, line 1460 and `eq:cylinder-time`. -/
theorem regularChartClock_strictMono {w : ℝ → ℝ} {a d c : ℝ}
    (had : a ≤ d) (hw : ContinuousOn w (Icc a d)) (hc : 0 < c)
    (hlo : ∀ x ∈ Icc a d, c ≤ w x) : StrictMono (regularChartClock w a d) := by
  intro x y hxy
  have hh := regularChartClock_increment_lower had hw hlo hxy.le
  have hp : 0 < c * (y - x) := mul_pos hc (sub_pos.mpr hxy)
  linarith

/-- The affine extensions ensure that every real boundary time has an
inverse label. Paper `e1a0fd5`, lines 1422 and 1460. -/
theorem regularChartClock_surjective {w : ℝ → ℝ} {a d c : ℝ}
    (had : a ≤ d) (hw : ContinuousOn w (Icc a d)) (hc : 0 < c)
    (hlo : ∀ x ∈ Icc a d, c ≤ w x) : Function.Surjective (regularChartClock w a d) := by
  intro s
  let L := (|s| + 1) / c
  have hL : 0 < L := div_pos (by positivity) hc
  have he : c * L = |s| + 1 := by dsimp [L]; field_simp
  have hzero : regularChartClock w a d a = 0 := by simp [regularChartClock]
  have hl := regularChartClock_increment_lower had hw hlo (show a - L ≤ a by linarith)
  have hr := regularChartClock_increment_lower had hw hlo (show a ≤ a + L by linarith)
  have hleft : regularChartClock w a d (a - L) ≤ s := by
    rw [hzero] at hl
    have hm : c * (a - (a - L)) = |s| + 1 := by rw [show a - (a - L) = L by ring, he]
    rw [hm] at hl
    linarith [neg_abs_le s]
  have hright : s ≤ regularChartClock w a d (a + L) := by
    rw [hzero] at hr
    have hm : c * (a + L - a) = |s| + 1 := by rw [show a + L - a = L by ring, he]
    rw [hm] at hr
    linarith [le_abs_self s]
  have hcont : Continuous (regularChartClock w a d) :=
    continuous_iff_continuousAt.mpr (fun x => (regularChartClock_hasDerivAt had hw x).continuousAt)
  obtain ⟨x, _, hx⟩ := intermediate_value_Icc (by linarith : a - L ≤ a + L)
    hcont.continuousOn ⟨hleft, hright⟩
  exact ⟨x, hx⟩

/-- The regular extended clock and its global inverse form an order
isomorphism. All premises are supplied by the source cylinder's continuous
expansion and the K bound. Paper `e1a0fd5`, lines 742–749 and 1460. -/
@[expose] noncomputable def regularChartClockIso (w : ℝ → ℝ) {a d c : ℝ}
    (had : a ≤ d) (hw : ContinuousOn w (Icc a d)) (hc : 0 < c)
    (hlo : ∀ x ∈ Icc a d, c ≤ w x) : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfRightInverse (regularChartClock w a d)
    (regularChartClock_strictMono had hw hc hlo) (Function.invFun (regularChartClock w a d))
    (Function.rightInverse_invFun (regularChartClock_surjective had hw hc hlo))

/-- The inverse clock has exactly the reciprocal boundary Jacobian,
including endpoints. Paper `e1a0fd5`, lines 1460 and 1926–1927. -/
theorem regularChartClockIso_inverse_hasDerivAt {w : ℝ → ℝ} {a d c : ℝ}
    (had : a ≤ d) (hw : ContinuousOn w (Icc a d)) (hc : 0 < c)
    (hlo : ∀ x ∈ Icc a d, c ≤ w x) (s : ℝ) :
    HasDerivAt (regularChartClockIso w had hw hc hlo).symm
      (chartClockDensity w a d ((regularChartClockIso w had hw hc hlo).symm s))⁻¹ s := by
  let e := regularChartClockIso w had hw hc hlo
  apply HasDerivAt.of_local_left_inverse e.symm.continuous.continuousAt
    (regularChartClock_hasDerivAt had hw (e.symm s))
    ((hc.trans_le (chartClockDensity_lower had hlo _)).ne')
  exact Filter.Eventually.of_forall (fun x => e.apply_symm_apply x)

/-- Endpoint extension does not increase the BV of the clock density.
Paper `e1a0fd5`, lines 1441–1443 and 1460. -/
theorem boundedVariation_chartClockDensity {w : ℝ → ℝ} {a d x y : ℝ}
    (had : a ≤ d) (hw : BoundedVariationOn w (Icc a d)) :
    BoundedVariationOn (chartClockDensity w a d) (Icc x y) := by
  apply ne_top_of_le_ne_top hw
  exact eVariationOn.comp_le_of_monotoneOn w _
    (fun _ _ _ _ h => max_le_max_left a (min_le_min_right d h))
    (fun z _ => ⟨le_max_left _ _, max_le had (min_le_right _ _)⟩)

end AcExtensionPrinciple

end
