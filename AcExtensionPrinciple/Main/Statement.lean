module

public import AcExtensionPrinciple.External.BVUniqueness
public import AcExtensionPrinciple.External.SmallBVExistence
public import AcExtensionPrinciple.Frozen.ContinuationDomain
public import AcExtensionPrinciple.Frozen.FieldsAgreeAt
public import AcExtensionPrinciple.Frozen.MainTheoremStatement
public import AcExtensionPrinciple.Solution.Standing

/-!
# Statement of Theorem 1

Paper `e1a0fd5`, `equations.tex`
`thm:main`, lines 112–146; author rulings Q2 and Q5–Q8.
The standing hypothesis is the minimal class (author ruling Q1; axis traces Q10).
E1 and E2 are explicit proposition hypotheses. This file states the target
and verifies its continuation-domain geometry; it does not prove Theorem 1.
The frozen declarations of this file live in `AcExtensionPrinciple/Frozen/` (one per file).
-/

public section

namespace AcExtensionPrinciple

open Set Filter
open scoped Topology ENNReal

/-- Continuation points stay above ui and strictly off the axis.
Encoding sanity check for paper `e1a0fd5`, `thm:main`, lines 133–138;
author ruling Q2. -/
theorem continuationDomain_coordinates {ui ū : ℝ} (hū : ū ∈ Ioo ui 0)
    {p : ℝ × ℝ} (hp : p ∈ continuationDomain ui ū) : ui ≤ p.1 ∧ p.1 < p.2 := by
  rcases hp with ⟨htri, haxis⟩ | hlate
  · have hne : p.1 ≠ p.2 := by
      intro heq
      exact haxis ⟨htri.1, htri.2.1, heq.symm⟩
    exact ⟨htri.1, lt_of_le_of_ne htri.2.2.1 hne⟩
  · exact ⟨hū.1.le.trans hlate.1, hlate.2⟩

/-- Every a ≥ ui has an outgoing one-sided neighborhood in the continuation.
This includes the former endpoint 0 and all later axis parameters.
Paper `e1a0fd5`, `thm:main`, lines 133–138, author ruling Q2;
Christodoulou pp. 1146–1147, axis boundary convention. -/
theorem continuationDomain_outgoing_neighborhood {ui ū a : ℝ}
    (hū : ū ∈ Ioo ui 0) (ha : ui ≤ a) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε ∈ Ioo 0 δ, (a, a + ε) ∈ continuationDomain ui ū := by
  by_cases hlate : ū ≤ a
  · refine ⟨1, zero_lt_one, ?_⟩
    intro ε hε
    exact Or.inr ⟨hlate, by linarith [hε.1]⟩
  · have ha0 : a < 0 := (lt_of_not_ge hlate).trans hū.2
    refine ⟨-a, by linarith, ?_⟩
    intro ε hε
    refine Or.inl ⟨⟨ha, ha0, by linarith [hε.1], by linarith [hε.2]⟩, ?_⟩
    intro haxis
    have heq : a + ε = a := haxis.2.2
    linarith [hε.1]

/-- Exactly Ici ui is the regular-axis boundary of the continuation; no
parameter is removed at the former endpoint. Encoding sanity check for
paper `e1a0fd5`, `thm:main`, lines 133–138, author ruling Q2;
Christodoulou pp. 1146–1147, boundary Γ. -/
theorem continuationDomain_adjacentAxis {ui ū : ℝ} (hū : ū ∈ Ioo ui 0) :
    adjacentAxis (continuationDomain ui ū) = Ici ui := by
  ext a
  constructor
  · intro ha
    have hsub : continuationDomain ui ū ⊆ {p : ℝ × ℝ | ui ≤ p.1} :=
      fun _ hp => (continuationDomain_coordinates hū hp).1
    exact (closure_minimal hsub (isClosed_le continuous_const continuous_fst)) ha
  · intro ha
    rcases continuationDomain_outgoing_neighborhood hū ha with ⟨δ, hδ, hray⟩
    have hcont : Continuous (fun ε : ℝ => (a, a + ε)) := by fun_prop
    have ht : Tendsto (fun ε : ℝ => (a, a + ε)) (𝓝[>] 0) (𝓝 (a, a)) := by
      simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    apply mem_closure_of_tendsto ht
    filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
    exact hray ε hε

end AcExtensionPrinciple

end
