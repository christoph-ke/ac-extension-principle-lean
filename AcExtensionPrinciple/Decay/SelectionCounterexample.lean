module

public import Mathlib.Topology.Order.Monotone
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Tactic

/-!
# First dyadic times need not be strictly increasing

Audit: paper `e1a0fd5`, `equations.tex` lines 871–876,
`eq:dyadic-cylinder-selection`. A right-continuous downward jump can cross
several dyadic levels simultaneously.
-/

public section

namespace AcExtensionPrinciple

open Set Filter
open scoped Topology

/-- A positive decreasing envelope with a downward jump at -1;
paper `e1a0fd5`, `equations.tex` lines 871–876 (audit example). -/
@[expose] noncomputable def jumpingEnvelope (u : ℝ) : ℝ :=
  if u < -1 then 2 else -u / 4

/-- The example obeys all the envelope assumptions in the selection argument;
paper `e1a0fd5`, `equations.tex` lines 865–871. -/
theorem jumpingEnvelope_properties :
    AntitoneOn jumpingEnvelope (Ico (-2) 0) ∧
    (∀ u ∈ Ico (-2) 0, 0 < jumpingEnvelope u) ∧
    (∀ u ∈ Ico (-2) 0, ContinuousWithinAt jumpingEnvelope (Ici u) u) ∧
    Tendsto jumpingEnvelope (𝓝[<] 0) (𝓝 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u hu w hw huw
    simp only [jumpingEnvelope]
    split_ifs <;> linarith [hu.1, hu.2, hw.1, hw.2]
  · intro u hu
    simp only [jumpingEnvelope]
    split_ifs <;> linarith [hu.2]
  · intro u _hu
    by_cases hu : u < -1
    · have heq : jumpingEnvelope =ᶠ[𝓝[≥] u] fun _ ↦ (2 : ℝ) := by
        filter_upwards [(gt_mem_nhds hu : Iio (-1 : ℝ) ∈ 𝓝 u).filter_mono
          nhdsWithin_le_nhds] with w hw
        simp [jumpingEnvelope, hw]
      change Tendsto jumpingEnvelope (𝓝[≥] u) (𝓝 (jumpingEnvelope u))
      rw [show jumpingEnvelope u = 2 by simp [jumpingEnvelope, hu]]
      exact tendsto_const_nhds.congr' heq.symm
    · have heq : jumpingEnvelope =ᶠ[𝓝[≥] u] fun w ↦ -w / 4 := by
        filter_upwards [self_mem_nhdsWithin] with w hw
        change u ≤ w at hw
        simp [jumpingEnvelope, show ¬w < -1 by linarith [hw, not_lt.mp hu]]
      have hcont : ContinuousWithinAt (fun w : ℝ ↦ -w / 4) (Ici u) u := by fun_prop
      exact hcont.congr_of_eventuallyEq heq (by simp [jumpingEnvelope, hu])
  · have heq : jumpingEnvelope =ᶠ[𝓝[<] 0] fun w ↦ -w / 4 := by
      filter_upwards [(lt_mem_nhds (show (-1 : ℝ) < 0 by norm_num)).filter_mono
        nhdsWithin_le_nhds] with w hw
      simp [jumpingEnvelope, not_lt.mpr hw.le]
    have hlim : Tendsto (fun w : ℝ ↦ -w / 4) (𝓝[<] 0) (𝓝 0) := by
      have hid : Tendsto (fun w : ℝ ↦ w) (𝓝[<] 0) (𝓝 0) :=
        tendsto_id'.mpr nhdsWithin_le_nhds
      simpa using hid.neg.div_const (4 : ℝ)
    exact hlim.congr' heq.symm

/-- Both levels 1 and 1/2 are first attained at -1, despite a valid positive
initial level `1 < b(-2)`. Thus strict increase is false;
paper `e1a0fd5`, `equations.tex` lines 871–876. -/
theorem dyadic_first_times_can_coincide :
    0 < (1 : ℝ) ∧ 1 < jumpingEnvelope (-2) ∧
    sInf {u : ℝ | u ∈ Ico (-2) 0 ∧ jumpingEnvelope u ≤ 1} = -1 ∧
    sInf {u : ℝ | u ∈ Ico (-2) 0 ∧ jumpingEnvelope u ≤ 1 / 2} = -1 := by
  have hleast (ell : ℝ) (hlo : 1 / 4 ≤ ell) (hhi : ell < 2) :
      IsLeast {u : ℝ | u ∈ Ico (-2) 0 ∧ jumpingEnvelope u ≤ ell} (-1) := by
    constructor
    · norm_num [jumpingEnvelope]
      exact hlo
    · intro u hu
      change u ∈ Ico (-2) 0 ∧ jumpingEnvelope u ≤ ell at hu
      by_contra hnot
      have hlt : u < -1 := lt_of_not_ge hnot
      have hv : jumpingEnvelope u = 2 := by simp [jumpingEnvelope, hlt]
      rw [hv] at hu
      exact (not_le.mpr hhi) hu.2
  refine ⟨by norm_num, by norm_num [jumpingEnvelope], ?_, ?_⟩
  · exact (hleast 1 (by norm_num) (by norm_num)).csInf_eq
  · exact (hleast (1 / 2) (by norm_num) (by norm_num)).csInf_eq

end AcExtensionPrinciple

end
