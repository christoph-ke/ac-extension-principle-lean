module

public import Mathlib.Topology.Order.Monotone
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Tactic

/-!
# Right continuity of the bad-radius envelope

Paper `e1a0fd5`, `equations.tex` lines 859–869,
`eq:bad-radius-envelope`. Finite nonempty suprema and persistence of each
strict sublevel witness at a later time make the argument precise.
-/

public section

namespace AcExtensionPrinciple

open Set Filter
open scoped Topology

/-- Future radii used in the envelope; paper `e1a0fd5`, `equations.tex`
lines 861–864 (`eq:bad-radius-envelope`). -/
@[expose] def futureRadii {V : Type*} (B : Set (ℝ × V)) (rho : ℝ × V → ℝ)
    (u : ℝ) : Set ℝ := rho '' {p | p ∈ B ∧ u ≤ p.1}

/-- The supremum envelope of future radii; paper `e1a0fd5`, `equations.tex`
lines 861–864 (`eq:bad-radius-envelope`). -/
@[expose] noncomputable def badRadiusEnvelope {V : Type*} (B : Set (ℝ × V))
    (rho : ℝ × V → ℝ) (u : ℝ) : ℝ := sSup (futureRadii B rho u)

/-- Removing earlier times can only decrease a finite nonempty envelope;
paper `e1a0fd5`, `equations.tex` line 865. -/
theorem badRadiusEnvelope_antitoneOn {V : Type*} {B : Set (ℝ × V)}
    {rho : ℝ × V → ℝ} {u0 : ℝ}
    (hne : ∀ u ∈ Ico u0 0, (futureRadii B rho u).Nonempty)
    (hbd : ∀ u ∈ Ico u0 0, BddAbove (futureRadii B rho u)) :
    AntitoneOn (badRadiusEnvelope B rho) (Ico u0 0) := by
  intro u hu w hw huw
  apply csSup_le (hne w hw)
  rintro _ ⟨p, ⟨hp, hwp⟩, rfl⟩
  exact le_csSup (hbd u hu) ⟨p, ⟨hp, huw.trans hwp⟩, rfl⟩

/-- Precise persistence criterion: any radius strictly below a contributing
radius is still exceeded by a bad point at a strictly later time. In the paper,
off-axis continuity of μ and r and room to move to later outgoing times supply
this property. Paper `e1a0fd5`, `equations.tex` line 869. -/
theorem badRadiusEnvelope_right_continuous {V : Type*} {B : Set (ℝ × V)}
    {rho : ℝ × V → ℝ} {u0 u : ℝ}
    (hne : ∀ w ∈ Ico u0 0, (futureRadii B rho w).Nonempty)
    (hbd : ∀ w ∈ Ico u0 0, BddAbove (futureRadii B rho w))
    (hu : u ∈ Ico u0 0)
    (hpersist : ∀ p ∈ B, u ≤ p.1 → ∀ z < rho p,
      ∃ q ∈ B, u < q.1 ∧ q.1 < 0 ∧ z < rho q) :
    ContinuousWithinAt (badRadiusEnvelope B rho) (Ici u) u := by
  have hmono := badRadiusEnvelope_antitoneOn hne hbd
  apply tendsto_order.mpr
  constructor
  · intro z hz
    obtain ⟨_, ⟨p, ⟨hp, hup⟩, rfl⟩, hzp⟩ := exists_lt_of_lt_csSup (hne u hu) hz
    obtain ⟨q, hq, huq, hq0, hzq⟩ := hpersist p hp hup z hzp
    have hqdom : q.1 ∈ Ico u0 0 := ⟨hu.1.trans huq.le, hq0⟩
    have hqbound : z < badRadiusEnvelope B rho q.1 :=
      hzq.trans_le (le_csSup (hbd q.1 hqdom) ⟨q, ⟨hq, le_rfl⟩, rfl⟩)
    filter_upwards [Ico_mem_nhdsGE huq] with w hw
    have hwdom : w ∈ Ico u0 0 := ⟨hu.1.trans hw.1, hw.2.trans hq0⟩
    exact hqbound.trans_le (hmono hwdom hqdom hw.2.le)
  · intro z hz
    filter_upwards [Ico_mem_nhdsGE hu.2] with w hw
    have hwdom : w ∈ Ico u0 0 := ⟨hu.1.trans hw.1, hw.2⟩
    exact (hmono hu hwdom hw.1).trans_lt hz

/-- A singleton at the initial time shows that the raw supremum construction
alone gives no right continuity. Paper `e1a0fd5`, `equations.tex` line 869. -/
theorem envelope_without_persistence_jumps :
    badRadiusEnvelope ({((-1 : ℝ), ())} : Set (ℝ × Unit)) (fun _ ↦ (1 : ℝ)) (-1) = 1 ∧
    ∀ u : ℝ, -1 < u →
      badRadiusEnvelope ({((-1 : ℝ), ())} : Set (ℝ × Unit)) (fun _ ↦ (1 : ℝ)) u = 0 := by
  constructor
  · have hs : futureRadii ({((-1 : ℝ), ())} : Set (ℝ × Unit))
        (fun _ ↦ (1 : ℝ)) (-1) = {1} := by
      ext z
      simp [futureRadii, eq_comm]
    simp [badRadiusEnvelope, hs]
  · intro u hu
    have hs : futureRadii ({((-1 : ℝ), ())} : Set (ℝ × Unit))
        (fun _ ↦ (1 : ℝ)) u = ∅ := by
      ext z
      simp [futureRadii, not_le.mpr hu]
    simp [badRadiusEnvelope, hs, Real.sSup_empty]

/-- Without a positive dyadic starting level, even `b(u)=-u` has no threshold
in the stated domain. Paper `e1a0fd5`, `equations.tex` line 871 explicitly
supplies the required condition `b₀>0`. -/
theorem negative_level_has_no_first_time :
    (-1 : ℝ) < -(-2 : ℝ) ∧
    {u : ℝ | u ∈ Ico (-2) 0 ∧ -u ≤ -1} = ∅ := by
  constructor
  · norm_num
  · ext u
    simp only [mem_ofPred_eq, mem_Ico, mem_empty_iff_false, iff_false]
    rintro ⟨⟨_, hu⟩, hb⟩
    linarith

end AcExtensionPrinciple

end
