module

public import AcExtensionPrinciple.Frozen.AdjacentAxis
public import AcExtensionPrinciple.Frozen.AxisDiagonal
public import AcExtensionPrinciple.Frozen.ChrAxisVanishingVariation
public import AcExtensionPrinciple.Frozen.ChrBVBoundsOn
public import AcExtensionPrinciple.Frozen.ChrBVCore
public import AcExtensionPrinciple.Frozen.ChristodoulouBV
public import AcExtensionPrinciple.Frozen.DomainOfDevelopment
public import AcExtensionPrinciple.Frozen.LocalChristodoulouBV
public import AcExtensionPrinciple.Frozen.PastSet
public import AcExtensionPrinciple.Solution.Fields

/-!
# Christodoulou BV class

Paper `e1a0fd5`, `equations.tex`
lines 220–275, `lem:small-bv-existence`, and lines 1406–1412. Source: Christodoulou,
CPAM 46 (1993), definition on pp. 1146–1147, equations (1.7), (1.14),
(1.15), (1.18); characteristic integral interpretation: author ruling Q8.
The axis is a boundary of D, not part of D. Bounds control whole portions
of characteristic lines in K ∩ D.
The frozen declarations of this file live in `AcExtensionPrinciple/Frozen/` (one per file).
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- Trapezoid used for terminal-ray uniqueness. Paper `e1a0fd5`, lines 1406–1412;
Christodoulou p. 1146, J⁻(a,b), with 0 ≤ a < b in the application. -/
@[expose] def trapezoid (a b : ℝ) : Set (ℝ × ℝ) := pastSet a b

/-- Bounds decrease when the portion K ∩ D decreases. Encoding sanity check
for paper `e1a0fd5`, lines 220–275; Christodoulou pp. 1146–1147, items 1/3/5. -/
theorem ChrBVBoundsOn.mono_inter {K L D : Set (ℝ × ℝ)} {S : SSFields}
    (h : ChrBVBoundsOn L D S) (hKL : K ∩ D ⊆ L ∩ D) : ChrBVBoundsOn K D S := by
  rcases h with ⟨⟨c, N, hc, hbound⟩, ⟨C, hout, hin⟩⟩
  refine ⟨⟨c, N, hc, fun p hp => hbound p (hKL hp)⟩, C, ?_, ?_⟩
  · intro u
    have hslice : {v | (u, v) ∈ K ∩ D} ⊆ {v | (u, v) ∈ L ∩ D} :=
      fun _ hv => hKL hv
    exact ⟨(eVariationOn.mono _ hslice).trans (hout u).1,
      (eVariationOn.mono _ hslice).trans (hout u).2.1,
      (eVariationOn.mono _ hslice).trans (hout u).2.2⟩
  · intro v
    have hslice : {u | (u, v) ∈ K ∩ D} ⊆ {u | (u, v) ∈ L ∩ D} :=
      fun _ hu => hKL hu
    exact ⟨(eVariationOn.mono _ hslice).trans (hin v).1,
      (eVariationOn.mono _ hslice).trans (hin v).2.1,
      (eVariationOn.mono _ hslice).trans (hin v).2.2⟩

/-- Monotonicity in K. Encoding sanity check for paper `e1a0fd5`,
lines 220–275; Christodoulou pp. 1146–1147, items 1/3/5. -/
theorem ChrBVBoundsOn.mono {K L D : Set (ℝ × ℝ)} {S : SSFields}
    (h : ChrBVBoundsOn L D S) (hKL : K ⊆ L) : ChrBVBoundsOn K D S :=
  h.mono_inter (inter_subset_inter_left D hKL)

/-- Globally uniform bounds imply compact localization. Encoding sanity check
for paper `e1a0fd5`, lines 220–275; Christodoulou pp. 1146–1147
and Luk–Oh Def. 2.1, p. 1611. -/
theorem ChristodoulouBV.local {D : Set (ℝ × ℝ)} {A : Set ℝ} {S : SSFields}
    (h : ChristodoulouBV D A S) : LocalChristodoulouBV D A S :=
  ⟨h.1, fun K _ _ => h.2.mono (subset_univ K)⟩

/-- Compact closure supplies global bounds when all missing boundary points
are regular axis points. Encoding sanity check;
paper `e1a0fd5`, lines 220–275, Q6; Christodoulou pp. 1146–1147. -/
theorem LocalChristodoulouBV.global_of_compact_closure
    {D : Set (ℝ × ℝ)} {A : Set ℝ} {S : SSFields}
    (h : LocalChristodoulouBV D A S) (hcompact : IsCompact (closure D))
    (hclosure : closure D ⊆ D ∪ axisDiagonal A) : ChristodoulouBV D A S := by
  refine ⟨h.1, (h.2 (closure D) hcompact hclosure).mono_inter ?_⟩
  intro p hp
  exact ⟨subset_closure hp.2, hp.2⟩

/-- Every causal past is a domain of development (also in degenerate cases).
Encoding sanity check for paper `e1a0fd5`, lines 1406–1412;
Christodoulou p. 1146, J⁻ and domain definition. -/
theorem pastSet_domainOfDevelopment (a b : ℝ) : domainOfDevelopment (pastSet a b) := by
  constructor
  · intro p hp
    exact ⟨hp.1.1, hp.2.1⟩
  · intro p hp q hq
    exact ⟨⟨hq.1.1, hq.1.2.trans hp.1.2⟩, ⟨hq.2.1, hq.2.2.trans hp.2.2⟩⟩

/-- Trapezoids satisfy the uniqueness input's domain condition.
Paper `e1a0fd5`, lines 1406–1412; Christodoulou p. 1146, J⁻(a,b). -/
theorem trapezoid_domainOfDevelopment (a b : ℝ) : domainOfDevelopment (trapezoid a b) :=
  pastSet_domainOfDevelopment a b

end AcExtensionPrinciple

end
