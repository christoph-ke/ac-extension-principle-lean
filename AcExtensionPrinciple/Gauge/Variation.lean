module

public import AcExtensionPrinciple.Gauge.Reparam
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Variation components and an axis-limit obstruction

This module treats variation under the continuation gauge.
Paper commit `e1a0fd5`, `equations.tex` lines 1390–1445.
The continuity of the coordinate derivative alone does not preserve cancellation
of two unbounded expansions at the axis. The counterexample below concerns preservation of
field-level axis cancellation.
It does not belong to the regular-center BV class.
-/

public section

namespace AcExtensionPrinciple

open Set Filter
open scoped Topology ENNReal

/-- Variation is invariant on the image of an increasing reparametrization.
Paper `e1a0fd5`, `equations.tex` lines 1431–1433. -/
theorem variation_comp_monotoneOn (f T : ℝ → ℝ) (s : Set ℝ)
    (hT : MonotoneOn T s) :
    eVariationOn (fun x => f (T x)) s = eVariationOn f (T '' s) :=
  eVariationOn.comp_eq_of_monotoneOn f T hT

/-- Variation is invariant on a closed interval under a continuous increasing map.
Paper `e1a0fd5`, `equations.tex` lines 1431–1433. -/
theorem variation_comp_Icc (f T : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hT : MonotoneOn T (Icc a b)) (hc : ContinuousOn T (Icc a b)) :
    eVariationOn (fun x => f (T x)) (Icc a b) =
      eVariationOn f (Icc (T a) (T b)) := by
  rw [variation_comp_monotoneOn f T _ hT, hc.image_Icc_of_monotoneOn hab hT]

/-- Product variation bound in terms of uniform absolute-value bounds.
Paper `e1a0fd5`, `equations.tex` lines 1441–1443. -/
theorem variation_mul_le (f g : ℝ → ℝ) (s : Set ℝ) {C D : ℝ}
    (hf : ∀ x ∈ s, |f x| ≤ C) (hg : ∀ x ∈ s, |g x| ≤ D) :
    eVariationOn (fun x => f x * g x) s ≤
      ENNReal.ofReal C * eVariationOn g s + ENNReal.ofReal D * eVariationOn f s := by
  apply eVariationOn_fun_mul_le
  · intro x hx
    simpa only [Real.enorm_eq_ofReal_abs] using ENNReal.ofReal_le_ofReal (hf x hx)
  · intro x hx
    simpa only [Real.enorm_eq_ofReal_abs] using ENNReal.ofReal_le_ofReal (hg x hx)

/-- BV is preserved by an increasing pullback followed by multiplication by a
BV Jacobian. Paper `e1a0fd5`, `equations.tex` lines 1390–1422 and 1441–1443. -/
theorem boundedVariation_comp_mul {f T dT : ℝ → ℝ} {s : Set ℝ}
    (hT : MonotoneOn T s) (hf : BoundedVariationOn f (T '' s))
    (hd : BoundedVariationOn dT s) :
    BoundedVariationOn (fun x => f (T x) * dT x) s := by
  have hc : BoundedVariationOn (fun x => f (T x)) s := by
    change eVariationOn (fun x => f (T x)) s ≠ ⊤
    rw [variation_comp_monotoneOn f T s hT]
    exact hf
  exact hc.mul hd

/-- A BV bound and a finite value at one point bound a real field everywhere on
the segment. This supplies local boundedness from the class variation bounds. Paper `e1a0fd5`,
`equations.tex` lines 1390–1422. -/
theorem boundedVariation_abs_bound {f : ℝ → ℝ} {s : Set ℝ}
    (hf : BoundedVariationOn f s) {x x₀ : ℝ} (hx : x ∈ s) (hx₀ : x₀ ∈ s) :
    |f x| ≤ (eVariationOn f s).toReal + |f x₀| := by
  have hdist : |f x - f x₀| ≤ (eVariationOn f s).toReal := by
    simpa only [Real.dist_eq] using hf.dist_le hx hx₀
  have ht := abs_add_le (f x - f x₀) (f x₀)
  have he : f x - f x₀ + f x₀ = f x := by ring
  rw [he] at ht
  linarith

namespace AxisLimitObstruction

/-- Smooth increasing coordinate map on `[0,1]` used to test preservation of axis cancellation.
Paper `e1a0fd5`, `eq:continuation-null-gauge`, lines 1390–1395. -/
@[expose] noncomputable def map (t : ℝ) : ℝ := t + t ^ 2

/-- Derivative of the audit coordinate map. Paper `e1a0fd5`,
`eq:continuation-null-gauge`, lines 1390–1395. -/
@[expose] noncomputable def derivative (t : ℝ) : ℝ := 1 + 2 * t

/-- The audit map has the stated derivative everywhere. Paper `e1a0fd5`,
`eq:continuation-null-gauge`, lines 1390–1395. -/
theorem hasDerivAt_map (t : ℝ) : HasDerivAt map (derivative t) t := by
  convert (hasDerivAt_id t).add ((hasDerivAt_id t).pow 2) using 1
  · ext x
    rfl
  · simp [derivative]

/-- The derivative in the counterexample is continuous. Paper `e1a0fd5`,
`eq:continuation-null-gauge`, lines 1390–1395. -/
theorem continuous_derivative : Continuous derivative := by
  unfold derivative
  fun_prop

/-- The derivative is bounded above and away from zero on the relevant interval.
Paper `e1a0fd5`, `eq:continuation-null-gauge`, lines 1390–1395. -/
theorem derivative_bounds {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    1 ≤ derivative t ∧ derivative t ≤ 3 := by
  dsimp [derivative]
  constructor <;> linarith [ht.1, ht.2]

/-- The audit map is strictly increasing on the relevant interval.
Paper `e1a0fd5`, `eq:continuation-null-gauge`, lines 1390–1395. -/
theorem strictMonoOn_map : StrictMonoOn map (Icc (0 : ℝ) 1) := by
  intro x hx y hy hxy
  dsimp [map]
  nlinarith [hx.1, hy.1]

/-- Field family whose expansion sum vanishes identically, with unbounded
individual expansions near the axis. Paper `e1a0fd5`, `equations.tex`
lines 1390–1395; example of field-level axis cancellation. -/
@[expose] noncomputable def fields : SSFields where
  r _ _ := 0
  phi _ _ := 0
  m _ _ := 0
  lam u v := 1 / (v - u)
  nu u v := -(1 / (v - u))
  dvpsi _ _ := 0
  dupsi _ _ := 0

/-- The original expansion sum is zero on every point of the ray.
Paper `e1a0fd5`, `equations.tex` lines 1390–1395; axis cancellation example. -/
theorem original_sum (t : ℝ) : fields.nu 0 t + fields.lam 0 t = 0 := by
  simp [fields]

/-- The original expansion sum tends to zero from the right at the axis.
Paper `e1a0fd5`, `equations.tex` lines 1390–1395; axis cancellation example. -/
theorem original_limit :
    Tendsto (fun t => fields.nu 0 t + fields.lam 0 t) (𝓝[>] 0) (𝓝 0) := by
  simp only [original_sum]
  exact tendsto_const_nhds

/-- The derivative mismatch destroys cancellation in the pullback.
Paper `e1a0fd5`, `equations.tex` lines 1390–1395; axis cancellation example. -/
theorem pullback_sum {t : ℝ} (ht : 0 < t) :
    (fields.pullback map derivative).nu 0 t +
      (fields.pullback map derivative).lam 0 t = 2 / (1 + t) := by
  simp only [SSFields.pullback, fields, map, derivative]
  have ht0 : t ≠ 0 := ne_of_gt ht
  have ht1 : 1 + t ≠ 0 := by positivity
  have ht2 : t + t ^ 2 ≠ 0 := by positivity
  field_simp
  nlinarith

/-- The transformed expansion sum tends to two, despite the increasing smooth coordinate map. Paper
`e1a0fd5`, `equations.tex` lines 1390–1395. -/
theorem pullback_limit :
    Tendsto (fun t => (fields.pullback map derivative).nu 0 t +
      (fields.pullback map derivative).lam 0 t) (𝓝[>] 0) (𝓝 2) := by
  have h : Tendsto (fun t : ℝ => 2 / (1 + t)) (𝓝[>] 0) (𝓝 (2 / (1 + 0))) :=
    tendsto_const_nhds.div (tendsto_const_nhds.add nhdsWithin_le_nhds)
      (by norm_num)
  have h' : Tendsto (fun t : ℝ => 2 / (1 + t)) (𝓝[>] 0) (𝓝 2) := by
    simpa using h
  apply h'.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (pullback_sum ht).symm

/-- Preservation of field-level axis cancellation is false without a bound
on the individual expansions. Paper `e1a0fd5`, `equations.tex` lines 1390–1395. -/
theorem not_pullback_zero_limit :
    ¬ Tendsto (fun t => (fields.pullback map derivative).nu 0 t +
      (fields.pullback map derivative).lam 0 t) (𝓝[>] 0) (𝓝 0) := by
  intro h
  have heq : (2 : ℝ) = 0 := tendsto_nhds_unique pullback_limit h
  norm_num at heq

end AxisLimitObstruction
end AcExtensionPrinciple

end
