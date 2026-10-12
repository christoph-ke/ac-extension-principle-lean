module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Normed.Operator.Completeness
public import Mathlib.Topology.Algebra.InfiniteSum.ContinuousEval
public import Mathlib.Tactic

/-!
# Positive Neumann resolvents

Abstract step for paper `e1a0fd5`, `equations.tex` lines 1747–1755.
-/

public section

namespace AcExtensionPrinciple

open scoped Topology BoundedContinuousFunction

/-- Neumann series in operator norm; paper `e1a0fd5`, `equations.tex`
lines 1747–1755. -/
@[expose] noncomputable def observationResolvent {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (K : X →L[ℝ] X) : X →L[ℝ] X := ∑' n : ℕ, K ^ n

/-- The series is a two-sided inverse; paper `e1a0fd5`, `equations.tex`
lines 1747–1755. -/
theorem observationResolvent_inverse {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [CompleteSpace X] (K : X →L[ℝ] X) (hK : ‖K‖ < 1) :
    (1 - K) * observationResolvent K = 1 ∧ observationResolvent K * (1 - K) = 1 := by
  exact ⟨mul_neg_geom_series K hK, geom_series_mul_neg K hK⟩

/-- Even the larger cutoff `1/2` gives inverse norm at most `2`; paper
`e1a0fd5`, `equations.tex` lines 1747–1755. -/
theorem observationResolvent_norm_le_two {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (K : X →L[ℝ] X) (hK : ‖K‖ ≤ 1 / 2) :
    ‖observationResolvent K‖ ≤ 2 := by
  have hlt : ‖K‖ < 1 := by linarith
  have hgeom := hasSum_geometric_of_norm_lt_one
    (show ‖(‖K‖ : ℝ)‖ < 1 by simpa using hlt)
  have hb : ‖observationResolvent K‖ ≤ (1 - ‖K‖)⁻¹ :=
    tsum_of_norm_bounded hgeom (fun n ↦ by
      cases n with
      | zero =>
        simp only [pow_zero]
        change ‖ContinuousLinearMap.id ℝ X‖ ≤ 1
        exact ContinuousLinearMap.norm_id_le
      | succ n => exact norm_pow_le' K (Nat.succ_pos n))
  have hden : 0 < 1 - ‖K‖ := by linarith
  have htwo : (1 - ‖K‖)⁻¹ ≤ 2 := by
    rw [← one_div, div_le_iff₀ hden]
    linarith
  exact hb.trans htwo

/-- A positive operator applied to the positive unit has a Neumann solution
between `1` and `2`; paper `e1a0fd5`, `equations.tex` line 1755. -/
theorem observation_unit_solution_bounds {α : Type*} [TopologicalSpace α]
    (K : (α →ᵇ ℝ) →L[ℝ] (α →ᵇ ℝ)) (hK : ‖K‖ ≤ 1 / 2)
    (hpos : ∀ f : α →ᵇ ℝ, (∀ a, 0 ≤ f a) → ∀ a, 0 ≤ K f a) (a : α) :
    1 ≤ observationResolvent K (BoundedContinuousFunction.const α 1) a ∧
      observationResolvent K (BoundedContinuousFunction.const α 1) a ≤ 2 := by
  let e : α →ᵇ ℝ := BoundedContinuousFunction.const α 1
  have hlt : ‖K‖ < 1 := by linarith
  have hs := summable_geometric_of_norm_lt_one hlt
  have happly : observationResolvent K e a = ∑' n : ℕ, (K ^ n) e a := by
    rw [observationResolvent, tsum_apply hs]
    exact (BoundedContinuousFunction.evalCLM ℝ a).map_tsum
      (summable_apply hs e)
  have hp (n : ℕ) : ∀ a, 0 ≤ (K ^ n) e a := by
    induction n with
    | zero => simp [e]
    | succ n ih =>
      rw [pow_succ']
      exact hpos _ ih
  have hscalar : Summable (fun n : ℕ ↦ (K ^ n) e a) := by
    exact (BoundedContinuousFunction.evalCLM ℝ a).summable
      (summable_apply hs e)
  constructor
  · rw [happly]
    have hh := hscalar.le_tsum 0 (fun n _ ↦ hp n a)
    simpa [e] using hh
  · calc
      _ ≤ ‖observationResolvent K e‖ := BoundedContinuousFunction.apply_le_norm _ a
      _ ≤ ‖observationResolvent K‖ * ‖e‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 2 * 1 := mul_le_mul (observationResolvent_norm_le_two K hK)
        (by simpa [e] using BoundedContinuousFunction.norm_const_le (α := α) (1 : ℝ))
        (norm_nonneg _) (by norm_num)
      _ = 2 := by norm_num

end AcExtensionPrinciple

end
