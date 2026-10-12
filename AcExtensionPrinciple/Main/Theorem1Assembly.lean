module

public import AcExtensionPrinciple.Main.AssemblyBounds
public import AcExtensionPrinciple.Minimal.Restore

/-!
# Theorem 1 assembled from the small outgoing cones and E1/E2

Paper `e1a0fd5`, `equations.tex` `thm:main`, lines 112–146 and 1390–1445.
Proposition 3.5 supplies the explicit small-cone premise.
This assembly takes that conclusion as an input. No standing or external input is strengthened.
-/

public section

namespace AcExtensionPrinciple

open Set
open scoped ENNReal

/-- Full local class membership of the representative-preserving continuation.
Paper `e1a0fd5`, `thm:main`, line 133 and lines 1411–1422. All gauge and
compact gluing premises are discharged from the selected E1 development. -/
theorem StandingFull.continuationFields_local_chr
    {ui ū Co Ci : ℝ} {S Sdev : SSFields} (h : StandingFull ui S)
    (hū : ū ∈ Ioo ui 0) {T : ℝ ≃o ℝ} (hv : T ū = 0)
    (hd : ∀ x, HasDerivAt (T : ℝ → ℝ) (selectedJacobian S ū x) x)
    (hc : Continuous (selectedJacobian S ū))
    (hp : ∃ c : ℝ, 0 < c ∧ ∀ x, c ≤ selectedJacobian S ū x)
    (hBV : BoundedVariationOn (selectedJacobian S ū) (Icc ū 0))
    (hdev : ChristodoulouBV smallBVDomain (Ici 0) Sdev) (hg : SmallBVGeometry Sdev)
    (hdata : ∀ v > 0, Sdev.dvpsi 0 v = selectedInitialDatum S ū T v)
    (hout : ∀ u ≥ 0, smallBVOutgoingTV Sdev u < ENNReal.ofReal Co)
    (hin : ∀ v > 0, smallBVIncomingTV Sdev v < ENNReal.ofReal Ci)
    (he : ∀ u v, ū ≤ u → u < v → v ≤ 0 →
      FieldsAgreeAt S (Sdev.pullback T (selectedJacobian S ū)) (u, v)) :
    LocalChristodoulouBV (continuationDomain ui ū) (Ici ui)
      (continuationFields ui S Sdev T (selectedJacobian S ū)) := by
  let P := continuationFields ui S Sdev T (selectedJacobian S ū)
  let N := Sdev.pullback T (selectedJacobian S ū)
  have hold : FieldsAgreeOn (pastTriangle ui \ axis ui) P S :=
    fun p hp => fieldsAgreeAt_iff_values.mp (continuationFields_agree ui S Sdev T _ hp)
  have hnew : FieldsAgreeOn (lateContinuationDomain ū) P N :=
    fun p hp => continuationFields_values_late he hp
  have hcoreN := selected_development_pullback_core h hū hv hd hc hp hdev hg hdata hout hin
  refine ⟨h.continuationFields_core hū he hcoreN, ?_⟩
  intro K hK _
  obtain ⟨B₀, hB₀⟩ := hK.exists_bound_of_continuousOn
    (continuous_snd.continuousOn : ContinuousOn (fun p : ℝ × ℝ => p.2) K)
  let B := max 0 B₀
  have hB : 0 ≤ B := le_max_left _ _
  have hKB : ∀ p ∈ K, p.2 ≤ B := by
    intro p hp
    have hh : |p.2| ≤ B₀ := by simpa only [Real.norm_eq_abs] using hB₀ p hp
    exact (le_abs_self _).trans (hh.trans (le_max_right _ _))
  have hb₁ : ChrBVBoundsOn univ (earlyContinuationDomain ui ū) S := by
    apply (h.proper_triangle_bounds (ū := ui) le_rfl hū.2).restrict
    intro p hp
    exact ⟨⟨hp.1, hp.2.1⟩, hp.2.2.1.le, hp.2.2.2⟩
  have hb₂ := selected_development_pullback_bounds (B := B) h hū hv hc hp hBV
    hdev hg hdata hout hin
  apply (continuation_bounds_union hū hB hold hnew hb₁ hb₂).mono_portions
  intro p hp
  refine ⟨mem_univ _, ?_⟩
  by_cases hu : ū ≤ p.1
  · exact Or.inr ⟨⟨hu, (continuationDomain_coordinates hū hp.2).2⟩, hKB p hp.1⟩
  · have ho := continuation_point_old hp.2 (not_le.mp hu)
    exact Or.inl ⟨ho.1.1, (not_le.mp hu).le,
      (continuationDomain_coordinates hū hp.2).2, ho.1.2.2.2⟩

/-- Theorem 1 from exactly E1, E2, the standing class and Proposition 3.5's
small-cone conclusion. The conclusion is `MainTheoremStatement`. Paper `e1a0fd5`, `thm:main`, lines
112–146,
`eq:terminal-bv-bound`, and the proof at lines 1390–1445. -/
theorem main_of_small_cones (hE1 : SmallBVExistence) (hE2 : BVUniqueness)
    (ui : ℝ) (S : SSFields) (h : StandingFull ui S)
    (hcones : SmallOutgoingConesStatement ui S) :
    (∃ ū ∈ Ioo ui 0, ∃ Splus : SSFields,
      LocalChristodoulouBV (continuationDomain ui ū) (Ici ui) Splus ∧
      ∀ p ∈ pastTriangle ui \ axis ui, FieldsAgreeAt Splus S p) ∧
    eVariationOn (fun u => S.dupsi u 0 / S.nu u 0) (Ico ui 0) ≠ ⊤ ∧
    eVariationOn (fun u => S.phi u 0) (Ico ui 0) ≠ ⊤ ∧
    eVariationOn (fun u => Real.log (-S.nu u 0)) (Ico ui 0) ≠ ⊤ ∧
    eVariationOn (fun u => S.nu u 0) (Ico ui 0) ≠ ⊤ ∧
    eVariationOn (fun u => S.dupsi u 0) (Ico ui 0) ≠ ⊤ := by
  obtain ⟨ū, hū, T, Sdev, hT, hv, ht, hd, hc, hp, hBV, hdev, hg, hdata,
    ⟨Co, hout⟩, ⟨Ci, hin⟩, _, _, _⟩ := selected_small_bv_development hE1 hE2 h hcones
  have hr : ∀ t ∈ Icc ū 0, T t = 2 * S.r ū t := by
    intro t htt
    rw [hT]
    exact radialChartMap_on_interval hū.2.le
      (h.regularCenter.localBV.axis_values ū
        (axis_subset_pastTriangle ui ⟨hū.1.le, hū.2, rfl⟩)).1 t htt
  have he := h.selected_full_agreement hū hE2 hv ht hd hc hp hBV hr hdev hg hdata
  have hclass := h.continuationFields_local_chr hū hv hd hc hp hBV hdev hg
    (fun v hv => (hdata v hv).2) hout hin he
  exact ⟨⟨ū, hū, continuationFields ui S Sdev T (selectedJacobian S ū), hclass,
    fun p hp => continuationFields_agree ui S Sdev T _ hp⟩,
    terminal_bv_of_small_cones hE1 hE2 h hcones⟩

/-- The exact main statement follows once the small-cone proposition has
been discharged from the standing class. Paper `e1a0fd5`, `thm:main` and
`prop:small-outgoing-bv-cones`, lines 1324–1330 and 1390–1445. -/
theorem main_statement_of_small_cones
    (hcones : ∀ ui S, StandingFull ui S → SmallOutgoingConesStatement ui S) :
    MainTheoremStatement := by
  intro hE1 hE2 ui S h
  exact main_of_small_cones hE1 hE2 ui S h.toFull (hcones ui S h.toFull)

end AcExtensionPrinciple

end
