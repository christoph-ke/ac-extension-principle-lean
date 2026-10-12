module

public import AcExtensionPrinciple.Decay.FirstTime
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Dyadic cylinder selection

Helpers for paper `e1a0fd5`, `equations.tex` lines 871–877
(`eq:dyadic-cylinder-selection`). Times are nondecreasing; strict increase is
not needed and fails at downward jumps, as checked in `SelectionCounterexample`.
-/

public section

namespace AcExtensionPrinciple

open Set Filter
open scoped Topology

/-- The positive dyadic cylinder radius; paper `e1a0fd5`,
`equations.tex` line 871. -/
@[expose] noncomputable def envelopeDyadicLevel (b0 : ℝ) (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ n * b0

/-- First time at the nth dyadic radius; paper `e1a0fd5`,
`equations.tex` lines 871–876. -/
@[expose] noncomputable def envelopeDyadicTime (b : ℝ → ℝ) (u0 b0 : ℝ) (n : ℕ) : ℝ :=
  envelopeFirstTime b u0 (envelopeDyadicLevel b0 n)

/-- Dyadic levels are positive, at most the initial radius, and halve;
paper `e1a0fd5`, `equations.tex` lines 871–876. -/
theorem envelopeDyadicLevel_properties {b0 : ℝ} (hb0 : 0 < b0) (n : ℕ) :
    0 < envelopeDyadicLevel b0 n ∧ envelopeDyadicLevel b0 n ≤ b0 ∧
    envelopeDyadicLevel b0 (n + 1) = envelopeDyadicLevel b0 n / 2 := by
  refine ⟨by dsimp [envelopeDyadicLevel]; positivity, ?_, ?_⟩
  · simpa [envelopeDyadicLevel] using mul_le_mul_of_nonneg_right
      (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)) hb0.le
  · simp only [envelopeDyadicLevel, pow_succ]
    ring

/-- First dyadic times are nondecreasing; paper `e1a0fd5`,
`equations.tex` lines 871–876. -/
theorem envelopeDyadicTime_monotone {b : ℝ → ℝ} {u0 b0 : ℝ}
    (hu0 : u0 < 0) (hb0 : 0 < b0) (hlim : Tendsto b (𝓝[<] 0) (𝓝 0)) :
    Monotone (envelopeDyadicTime b u0 b0) := by
  apply monotone_nat_of_le_succ
  intro n
  apply envelopeFirstTime_antitone_level hu0
    (envelopeDyadicLevel_properties hb0 (n + 1)).1 hlim
  rw [(envelopeDyadicLevel_properties hb0 n).2.2]
  linarith [(envelopeDyadicLevel_properties hb0 n).1]

/-- Attainment and both dyadic cylinder bounds, including possible empty
intervals when consecutive first times coincide; paper `e1a0fd5`,
`equations.tex` lines 871–876 (`eq:dyadic-cylinder-selection`). -/
theorem envelope_dyadic_selection {b : ℝ → ℝ} {u0 b0 : ℝ}
    (hu0 : u0 < 0) (hb0 : 0 < b0) (hinit : b0 < b u0)
    (hlim : Tendsto b (𝓝[<] 0) (𝓝 0))
    (hright : ∀ u ∈ Ico u0 0, ContinuousWithinAt b (Ici u) u)
    (hmono : AntitoneOn b (Ico u0 0)) (n : ℕ) :
    u0 < envelopeDyadicTime b u0 b0 n ∧ envelopeDyadicTime b u0 b0 n < 0 ∧
    b (envelopeDyadicTime b u0 b0 n) ≤ envelopeDyadicLevel b0 n ∧
    (∀ u ∈ Ico u0 0, envelopeDyadicTime b u0 b0 n ≤ u → b u ≤ envelopeDyadicLevel b0 n) ∧
    (∀ u, envelopeDyadicTime b u0 b0 n ≤ u → u < envelopeDyadicTime b u0 b0 (n + 1) →
      envelopeDyadicLevel b0 n / 2 < b u) := by
  have hlevel := envelopeDyadicLevel_properties hb0 n
  have ht := envelopeFirstTime_bounds hu0 hlevel.1 hlim hright
  have hgt : u0 < envelopeDyadicTime b u0 b0 n := by
    change u0 < envelopeFirstTime b u0 (envelopeDyadicLevel b0 n)
    apply lt_of_le_of_ne ht.1.1
    intro heq
    rw [← heq] at ht
    linarith [hlevel.2.1, ht.2]
  refine ⟨hgt, ht.1.2, ht.2, ?_, ?_⟩
  · intro u hu hafter
    exact envelope_bound_after_firstTime hu0 hlevel.1 hlim hright hmono hu hafter
  · intro u hafter hbefore
    have htNext := envelopeFirstTime_bounds hu0
      (envelopeDyadicLevel_properties hb0 (n + 1)).1 hlim hright
    have hudom : u ∈ Ico u0 0 := ⟨hgt.le.trans hafter, hbefore.trans htNext.1.2⟩
    have hh := envelope_bound_before_firstTime hudom hbefore
    rwa [(envelopeDyadicLevel_properties hb0 n).2.2] at hh

/-- Positive envelopes force the first dyadic times to tend to zero;
paper `e1a0fd5`, `equations.tex` lines 871–876. -/
theorem envelopeDyadicTime_tendsto_zero {b : ℝ → ℝ} {u0 b0 : ℝ}
    (hu0 : u0 < 0) (hb0 : 0 < b0)
    (hlim : Tendsto b (𝓝[<] 0) (𝓝 0))
    (hright : ∀ u ∈ Ico u0 0, ContinuousWithinAt b (Ici u) u)
    (hmono : AntitoneOn b (Ico u0 0)) (hpos : ∀ u ∈ Ico u0 0, 0 < b u) :
    Tendsto (envelopeDyadicTime b u0 b0) atTop (𝓝 0) := by
  have hlevels : Tendsto (envelopeDyadicLevel b0) atTop (𝓝 0) := by
    change Tendsto (fun n : ℕ ↦ (1 / 2 : ℝ) ^ n * b0) atTop (𝓝 0)
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).mul_const b0
  apply tendsto_order.mpr
  constructor
  · intro z hz
    by_cases hzu : z < u0
    · exact Eventually.of_forall (fun n ↦ hzu.trans_le
        (envelopeFirstTime_bounds hu0 (envelopeDyadicLevel_properties hb0 n).1 hlim hright).1.1)
    · have hzdom : z ∈ Ico u0 0 := ⟨not_lt.mp hzu, hz⟩
      filter_upwards [hlevels.eventually (gt_mem_nhds (hpos z hzdom))] with n hn
      by_contra hnot
      have hbound := envelope_bound_after_firstTime hu0
        (envelopeDyadicLevel_properties hb0 n).1 hlim hright hmono hzdom (not_lt.mp hnot)
      exact (not_le.mpr hn) hbound
  · intro z hz
    exact Eventually.of_forall (fun n ↦
      (envelopeFirstTime_bounds hu0
        (envelopeDyadicLevel_properties hb0 n).1 hlim hright).1.2.trans hz)

/-- Taking the left limit of a continuous majorant bounds each dyadic radius
at its first time; paper `e1a0fd5`, `equations.tex` line 877 (`eq:bad-radius-scale`). -/
theorem envelope_dyadic_level_le_majorant {b g : ℝ → ℝ} {u0 b0 : ℝ}
    (hu0 : u0 < 0) (hb0 : 0 < b0) (hinit : b0 < b u0)
    (hlim : Tendsto b (𝓝[<] 0) (𝓝 0))
    (hright : ∀ u ∈ Ico u0 0, ContinuousWithinAt b (Ici u) u)
    (hmono : AntitoneOn b (Ico u0 0))
    (hmajor : ∀ u ∈ Ico u0 0, b u ≤ g u) (hg : ContinuousOn g (Ico u0 0)) (n : ℕ) :
    envelopeDyadicLevel b0 n ≤ g (envelopeDyadicTime b u0 b0 n) := by
  have hsel := envelope_dyadic_selection hu0 hb0 hinit hlim hright hmono n
  apply envelope_level_le_majorant_at_firstTime hsel.1 hmajor hsel.2.1
  apply hg.continuousAt
  exact mem_of_superset (Ioo_mem_nhds hsel.1 hsel.2.1) Ioo_subset_Ico_self

end AcExtensionPrinciple

end
