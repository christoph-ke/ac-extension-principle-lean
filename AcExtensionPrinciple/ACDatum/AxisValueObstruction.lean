module

public import AcExtensionPrinciple.Solution.StandingFull
public import Mathlib.Tactic

/-!
# Axis limits do not determine axis values

Paper commit `e1a0fd5`, `lem:ac-datum-propagation`, lines 562 and 601,
and `eq:regular-axis-scalar-traces`, lines 247–261. The regular-center class identifies axis values
with their limits.
The example below records the distinction between a limit and the value at the axis.
-/

public section

namespace AcExtensionPrinciple.ACDatum

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- Flat zero-scalar fields with a single altered axis value on the triangle.
Paper `e1a0fd5`, lines 222–261 and 562: a representative obstruction. -/
@[expose] noncomputable def axisValueExample : SSFields where
  r u v := v - u
  phi _ _ := 0
  m _ _ := 0
  lam _ _ := 1
  nu _ _ := -1
  dvpsi u v := if u = -1 ∧ v ≤ u then -1 else 0
  dupsi _ _ := 0

/-- The altered datum is zero strictly above the axis.
Paper `e1a0fd5`, lines 247–261 and 601. -/
theorem example_dvpsi_off_axis {u v : ℝ} (huv : u < v) :
    axisValueExample.dvpsi u v = 0 := by
  simp [axisValueExample, not_le.mpr huv]

/-- Off-axis limits alone do not determine stored axis values. The axis value identities
exclude this example from the regular-center class. Paper `e1a0fd5`,
`eq:regular-axis-scalar-traces`, lines 247–261. -/
theorem example_trace_without_axis_value :
    (∀ a, (a, a) ∈ axis (-2) →
      Tendsto (fun p : ℝ × ℝ => axisValueExample.dvpsi p.1 p.2 / axisValueExample.lam p.1 p.2)
        (𝓝[pastTriangle (-2) \ axis (-2)] (a, a)) (𝓝 (axisValueExample.phi a a))) ∧
    axisValueExample.dvpsi (-1) (-1) / axisValueExample.lam (-1) (-1) ≠
      axisValueExample.phi (-1) (-1) := by
  constructor
  · intro a ha
    apply Tendsto.congr' ?_ (tendsto_const_nhds :
      Tendsto (fun _ : ℝ × ℝ => (0 : ℝ))
        (𝓝[pastTriangle (-2) \ axis (-2)] (a, a)) (𝓝 0))
    filter_upwards [self_mem_nhdsWithin] with p hp
    have hpv : p.1 < p.2 := by
      have hne : p.1 ≠ p.2 := by
        intro he
        exact hp.2 ⟨hp.1.1, hp.1.2.1, he.symm⟩
      exact lt_of_le_of_ne hp.1.2.2.1 hne
    change 0 = axisValueExample.dvpsi p.1 p.2 / 1
    rw [example_dvpsi_off_axis hpv]
    simp
  · norm_num [axisValueExample]

end AcExtensionPrinciple.ACDatum

end
