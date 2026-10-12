module

public import AcExtensionPrinciple.Sanity.FlatFields

/-!
# Non-vacuity of the standing and continuation hypotheses

Sanity checks, paper `e1a0fd5`, `equations.tex` `thm:main`, lines 112–146 and 220–275. These
explicit flat examples establish satisfiability; they do not prove the universal main theorem.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- Flat space in the original radius gauge, with arbitrary scalar value.
Paper `e1a0fd5`, `eq:initial-radius-gauge`, lines 121–127. -/
@[expose] noncomputable def flat (c : ℝ) : SSFields := scaledFlat 1 c

/-- Every positive-scale flat solution has the regular-center AC/BV
properties. Paper `e1a0fd5`, lines 220–275, `eq:regular-axis-scalar-traces`. -/
theorem scaledFlat_regularCenter_full (q c ui : ℝ) (hq : 0 < q) :
    RegularCenterFull ui (scaledFlat q c) := by
  refine ⟨scaledFlat_localBV_full q c hq _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change ContinuousOn (fun p : ℝ × ℝ => q * (p.2 - p.1)) _
    exact (continuous_const.mul (continuous_snd.sub continuous_fst)).continuousOn
  · exact continuous_const.continuousOn
  · exact continuous_const.continuousOn
  · exact continuous_const.continuousOn
  · exact continuous_const.continuousOn
  · intro u a b _ _
    exact flat_ac_const q a b
  · intro a _
    rfl
  · intro a _
    simpa [scaledFlat, hq.ne'] using (tendsto_const_nhds :
      Tendsto (fun _ : ℝ × ℝ => c) _ (𝓝 c))
  · intro a _
    simpa [scaledFlat, hq.ne'] using (tendsto_const_nhds :
      Tendsto (fun _ : ℝ × ℝ => c) _ (𝓝 c))
  · intro a _
    simp [scaledFlat, hq.ne']
  · intro a _
    simp [scaledFlat, hq.ne']

/-- The complete blueshift supremum is zero in flat space.
Paper `e1a0fd5`, `eq:uniform-blueshift`, lines 129–132. -/
@[simp] theorem scaledFlat_blueshiftSup (q c ui : ℝ) :
    blueshiftSup ui (scaledFlat q c) = 0 := by
  simp [blueshiftSup, scaledFlat, SSFields.gamma, SSFields.varkappa,
    SSFields.mu, massRatio, gammaOf, varkappaOf]

/-- All standing hypotheses hold for every negative ui and constant scalar c. Paper `e1a0fd5`,
`thm:main`, lines 112–132. -/
theorem flat_standing_full (ui c : ℝ) (hui : ui < 0) :
    StandingFull ui (flat c) := by
  refine ⟨hui, scaledFlat_regularCenter_full 1 c ui zero_lt_one, ?_, ?_, ?_, ?_⟩
  · intro p _ _
    norm_num [flat, scaledFlat, SSFields.mu, massRatio]
  · intro v _
    simp [flat, scaledFlat]
  · simpa [flat, scaledFlat] using flat_ac_const c ui 0
  · simp [flat]

/-- The original-gauge flat solution belongs to the globally uniform Christodoulou class on the
complete small-BV domain. Paper `e1a0fd5`, `lem:small-bv-existence`, lines 1364–1388. -/
theorem flat_smallBVDomain (c : ℝ) :
    ChristodoulouBV smallBVDomain (Ici 0) (flat c) :=
  scaledFlat_christodoulouBV 1 c zero_lt_one _ _ (fun _ hp => hp.2)

/-- Flat space lies in the local Christodoulou class on the original chart continuation. Paper
`e1a0fd5`, `thm:main`, line 133, lines 1411–1422. -/
theorem flat_continuation (ui ū c : ℝ) (hū : ū ∈ Ioo ui 0) :
    LocalChristodoulouBV (continuationDomain ui ū) (Ici ui) (flat c) :=
  (scaledFlat_christodoulouBV 1 c zero_lt_one _ _
    (fun _ hp => (continuationDomain_coordinates hū hp).2)).local

/-- Every conclusion of the main theorem holds directly for flat space, with Splus = flat. Paper
`e1a0fd5`, `thm:main`, lines 133–146, `eq:terminal-bv-bound`. This does not assume or prove E1, E2,
or the main theorem. -/
theorem flat_main_conclusions (ui c : ℝ) (hui : ui < 0) :
    (∃ ū ∈ Ioo ui 0, ∃ Splus : SSFields,
      LocalChristodoulouBV (continuationDomain ui ū) (Ici ui) Splus ∧
      ∀ p ∈ pastTriangle ui \ axis ui, FieldsAgreeAt Splus (flat c) p) ∧
    eVariationOn (fun u => (flat c).dupsi u 0 / (flat c).nu u 0) (Ico ui 0) ≠ ⊤ ∧
    eVariationOn (fun u => (flat c).phi u 0) (Ico ui 0) ≠ ⊤ ∧
    eVariationOn (fun u => Real.log (-(flat c).nu u 0)) (Ico ui 0) ≠ ⊤ ∧
    eVariationOn (fun u => (flat c).nu u 0) (Ico ui 0) ≠ ⊤ ∧
    eVariationOn (fun u => (flat c).dupsi u 0) (Ico ui 0) ≠ ⊤ := by
  have hū : ui / 2 ∈ Ioo ui 0 := by constructor <;> linarith
  refine ⟨⟨ui / 2, hū, flat c, flat_continuation ui (ui / 2) c hū, ?_⟩, ?_⟩
  · intro p _
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp [flat, scaledFlat]

/-- Flat solutions belong to the minimal regular-center source class.
Paper `e1a0fd5`, lines 220–275, `eq:regular-axis-scalar-traces`. -/
theorem scaledFlat_regularCenter (q c ui : ℝ) (hq : 0 < q) :
    RegularCenterLocalACBV ui (scaledFlat q c) :=
  (scaledFlat_regularCenter_full q c ui hq).toMinimal

/-- The minimal standing hypotheses are satisfiable by every original-gauge flat solution.
Paper `e1a0fd5`, `thm:main`, lines 112–132. -/
theorem flat_standing (ui c : ℝ) (hui : ui < 0) :
    StandingAssumptions ui (flat c) :=
  (flat_standing_full ui c hui).toMinimal

end AcExtensionPrinciple

end
