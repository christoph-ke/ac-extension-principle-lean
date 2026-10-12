module

public import Mathlib.Topology.Order.Monotone
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Tactic

/-!
# First times for a right-continuous envelope

Helpers for paper `e1a0fd5`, `equations.tex` lines 871–877
(`eq:dyadic-cylinder-selection`). Positive levels, supplied by paper line 871,
make the threshold sets nonempty.
-/

public section

namespace AcExtensionPrinciple

open Set Filter
open scoped Topology

/-- Times at which an envelope is below a level; paper `e1a0fd5`,
`equations.tex` lines 871–876. -/
@[expose] def envelopeLevelSet (b : ℝ → ℝ) (u0 ell : ℝ) : Set ℝ :=
  {u | u ∈ Ico u0 0 ∧ b u ≤ ell}

/-- The first threshold time, defined by an infimum; paper `e1a0fd5`,
`equations.tex` lines 871–876. -/
@[expose] noncomputable def envelopeFirstTime (b : ℝ → ℝ) (u0 ell : ℝ) : ℝ :=
  sInf (envelopeLevelSet b u0 ell)

/-- The initial time is a lower bound for the threshold set; paper `e1a0fd5`,
`equations.tex` line 871. -/
theorem envelopeLevelSet_bddBelow (b : ℝ → ℝ) (u0 ell : ℝ) :
    BddBelow (envelopeLevelSet b u0 ell) := ⟨u0, fun _ hu ↦ hu.1.1⟩

/-- Every positive level is reached before zero when the envelope tends to zero;
paper `e1a0fd5`, `equations.tex` lines 865–871. -/
theorem envelopeLevelSet_nonempty {b : ℝ → ℝ} {u0 ell : ℝ}
    (hu0 : u0 < 0) (hell : 0 < ell)
    (hlim : Tendsto b (𝓝[<] 0) (𝓝 0)) : (envelopeLevelSet b u0 ell).Nonempty := by
  have htimes : ∀ᶠ u : ℝ in 𝓝[<] 0, u ∈ Ioo u0 0 := Ioo_mem_nhdsLT hu0
  obtain ⟨u, hu, hb⟩ := (htimes.and (hlim.eventually (gt_mem_nhds hell))).exists
  exact ⟨u, ⟨hu.1.le, hu.2⟩, hb.le⟩

/-- Right continuity attains the infimum; paper `e1a0fd5`, `equations.tex`
lines 871–876 (`eq:dyadic-cylinder-selection`). -/
theorem envelopeFirstTime_bounds {b : ℝ → ℝ} {u0 ell : ℝ}
    (hu0 : u0 < 0) (hell : 0 < ell)
    (hlim : Tendsto b (𝓝[<] 0) (𝓝 0))
    (hright : ∀ u ∈ Ico u0 0, ContinuousWithinAt b (Ici u) u) :
    envelopeFirstTime b u0 ell ∈ Ico u0 0 ∧ b (envelopeFirstTime b u0 ell) ≤ ell := by
  let S := envelopeLevelSet b u0 ell
  have hne : S.Nonempty := envelopeLevelSet_nonempty hu0 hell hlim
  have hbd : BddBelow S := envelopeLevelSet_bddBelow b u0 ell
  have hlo : u0 ≤ sInf S := le_csInf hne (fun _ hu ↦ hu.1.1)
  have hclosure : sInf S ∈ closure S := csInf_mem_closure hne hbd
  obtain ⟨w, hw⟩ := hne
  have hneg : sInf S < 0 := (csInf_le hbd hw).trans_lt hw.1.2
  have : NeBot (𝓝[S] (sInf S)) := mem_closure_iff_nhdsWithin_neBot.mp hclosure
  have hsub : S ⊆ Ici (sInf S) := fun _ hu ↦ csInf_le hbd hu
  have hcont := (hright (sInf S) ⟨hlo, hneg⟩).mono hsub
  have hle : b (sInf S) ≤ ell := by
    apply le_of_tendsto hcont
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact hu.2
  exact ⟨⟨hlo, hneg⟩, hle⟩

/-- Every point below the threshold level is at or after the first time;
paper `e1a0fd5`, `equations.tex` lines 871–876. -/
theorem envelopeFirstTime_le_of_bound {b : ℝ → ℝ} {u0 ell u : ℝ}
    (hu : u ∈ Ico u0 0) (hb : b u ≤ ell) : envelopeFirstTime b u0 ell ≤ u :=
  csInf_le (envelopeLevelSet_bddBelow b u0 ell) ⟨hu, hb⟩

/-- Before the first time the level is strictly exceeded; paper `e1a0fd5`,
`equations.tex` lines 871–876 (`eq:dyadic-cylinder-selection`). -/
theorem envelope_bound_before_firstTime {b : ℝ → ℝ} {u0 ell u : ℝ}
    (hu : u ∈ Ico u0 0) (hbefore : u < envelopeFirstTime b u0 ell) : ell < b u := by
  by_contra hnot
  exact (not_le.mpr hbefore) (envelopeFirstTime_le_of_bound hu (not_lt.mp hnot))

/-- Smaller positive levels have later first times; paper `e1a0fd5`,
`equations.tex` lines 871–876. -/
theorem envelopeFirstTime_antitone_level {b : ℝ → ℝ} {u0 ell1 ell2 : ℝ}
    (hu0 : u0 < 0) (hell2 : 0 < ell2)
    (hlim : Tendsto b (𝓝[<] 0) (𝓝 0)) (hle : ell2 ≤ ell1) :
    envelopeFirstTime b u0 ell1 ≤ envelopeFirstTime b u0 ell2 := by
  apply csInf_le_csInf (envelopeLevelSet_bddBelow b u0 ell1)
    (envelopeLevelSet_nonempty hu0 hell2 hlim)
  intro u hu
  exact ⟨hu.1, hu.2.trans hle⟩

/-- Monotonicity preserves the level bound after its first time;
paper `e1a0fd5`, `equations.tex` lines 871–876. -/
theorem envelope_bound_after_firstTime {b : ℝ → ℝ} {u0 ell u : ℝ}
    (hu0 : u0 < 0) (hell : 0 < ell) (hlim : Tendsto b (𝓝[<] 0) (𝓝 0))
    (hright : ∀ w ∈ Ico u0 0, ContinuousWithinAt b (Ici w) w)
    (hmono : AntitoneOn b (Ico u0 0))
    (hu : u ∈ Ico u0 0) (hafter : envelopeFirstTime b u0 ell ≤ u) : b u ≤ ell := by
  have ht := envelopeFirstTime_bounds hu0 hell hlim hright
  exact (hmono ht.1 hu hafter).trans ht.2

/-- A continuous majorant controls the level at a first time strictly after
u₀, even if the envelope jumps down there; paper `e1a0fd5`, `equations.tex`
line 877 (`eq:bad-radius-scale`). -/
theorem envelope_level_le_majorant_at_firstTime {b g : ℝ → ℝ} {u0 ell : ℝ}
    (hafter : u0 < envelopeFirstTime b u0 ell)
    (hmajor : ∀ u ∈ Ico u0 0, b u ≤ g u)
    (hneg : envelopeFirstTime b u0 ell < 0)
    (hg : ContinuousAt g (envelopeFirstTime b u0 ell)) :
    ell ≤ g (envelopeFirstTime b u0 ell) := by
  have ht : Tendsto g (𝓝[<] (envelopeFirstTime b u0 ell))
      (𝓝 (g (envelopeFirstTime b u0 ell))) := hg.tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto_of_tendsto tendsto_const_nhds ht
  filter_upwards [Ioo_mem_nhdsLT hafter] with u hu
  have hudom : u ∈ Ico u0 0 := ⟨hu.1.le, hu.2.trans hneg⟩
  exact (envelope_bound_before_firstTime hudom hu.2).le.trans (hmajor u hudom)

end AcExtensionPrinciple

end
