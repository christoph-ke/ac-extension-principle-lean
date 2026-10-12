module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic

/-!
# Unbounded cylinder time increments relative to a dyadic radius

Internal helper for paper commit `e1a0fd5`, `equations.tex`
lines 877–882 (`eq:long-cylinder-times`). Here `b n = (1/2)^n b₀`,
equivalently `b n = 2^{-n} b₀`.
-/

public section

namespace AcExtensionPrinciple

open Filter
open scoped Topology

/-- An eventual increment bound implies a bound on the remaining time;
paper `e1a0fd5`, `equations.tex` lines 877–882 (`eq:long-cylinder-times`). -/
theorem remaining_time_le_of_dyadic_increment_bound {b0 A : ℝ} {u b : ℕ → ℝ}
    (_hb0 : 0 < b0) (_hA : 0 < A) (hb : ∀ n, b n = (1 / 2 : ℝ) ^ n * b0)
    (hu : Tendsto u atTop (𝓝 0)) {N : ℕ}
    (hinc : ∀ n ≥ N, u (n + 1) - u n ≤ A * b n) :
    ∀ n ≥ N, -u n ≤ 2 * A * b n := by
  have hpow (n k : ℕ) : b (n + k) = (1 / 2 : ℝ) ^ k * b n := by
    rw [hb, hb, pow_add]
    ring
  have hgeom : Tendsto (fun k : ℕ ↦ (1 / 2 : ℝ) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  intro n hn
  have hsum (k : ℕ) : u (n + k) ≤ u n + 2 * A * b n * (1 - (1 / 2 : ℝ) ^ k) := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hi := hinc (n + k) (by omega)
      rw [hpow] at hi
      rw [show n + (k + 1) = (n + k) + 1 by omega, pow_succ]
      linarith
  have hleft : Tendsto (fun k : ℕ ↦ u (n + k)) atTop (𝓝 0) :=
    hu.comp (by simpa [Nat.add_comm] using tendsto_add_atTop_nat n)
  have hright : Tendsto
      (fun k : ℕ ↦ u n + 2 * A * b n * (1 - (1 / 2 : ℝ) ^ k))
      atTop (𝓝 (u n + 2 * A * b n)) := by
    simpa using ((tendsto_const_nhds (x := u n)).add
      ((tendsto_const_nhds (x := 2 * A * b n)).mul
        ((tendsto_const_nhds (x := (1 : ℝ))).sub hgeom)))
  have hle := le_of_tendsto_of_tendsto hleft hright (Eventually.of_forall hsum)
  linarith

/-- Infinitely often, a cylinder lasts longer than any fixed multiple of its
dyadic radius; paper `e1a0fd5`, `equations.tex` lines 877–882
(`eq:long-cylinder-times`). -/
theorem frequently_dyadic_increment_gt {b0 : ℝ} {u b : ℕ → ℝ}
    (hb0 : 0 < b0) (hb : ∀ n, b n = (1 / 2 : ℝ) ^ n * b0)
    (_hmono : Monotone u) (huneg : ∀ n, u n < 0)
    (hu : Tendsto u atTop (𝓝 0))
    (hratio : Tendsto (fun n ↦ b n / (-u n)) atTop (𝓝 0)) (A : ℝ) :
    ∃ᶠ n in atTop, u (n + 1) - u n > A * b n := by
  by_contra hnot
  have hevent : ∀ᶠ n in atTop, u (n + 1) - u n ≤ A * b n := by
    simpa only [not_frequently, not_lt] using hnot
  let B : ℝ := max A 1
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  have hbound : ∀ n ≥ N, -u n ≤ 2 * B * b n := by
    apply remaining_time_le_of_dyadic_increment_bound hb0 hB hb hu
    intro n hn
    apply (hN n hn).trans
    have hbn : 0 ≤ b n := by rw [hb]; positivity
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hbn
  have hsmall := hratio.eventually (gt_mem_nhds (show 0 < 1 / (2 * B) by positivity))
  obtain ⟨n, hn, hs⟩ := ((eventually_ge_atTop N).and hsmall).exists
  have htime : 0 < -u n := neg_pos.mpr (huneg n)
  have hquot := (div_lt_iff₀ htime).mp hs
  have hmul := (lt_div_iff₀ (show 0 < 2 * B by positivity)).mp
    (show b n < (-u n) / (2 * B) by simpa [div_eq_mul_inv, mul_comm] using hquot)
  linarith [hbound n hn]

end AcExtensionPrinciple

end
