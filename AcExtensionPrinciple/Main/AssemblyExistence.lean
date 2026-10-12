module

public import AcExtensionPrinciple.Main.AssemblyData
public import AcExtensionPrinciple.Continuation.PointwiseDevelopment

/-!
# Existence and identification from a selected small cone

Paper `e1a0fd5`, `equations.tex` lines 1390–1422.
The inputs are exactly E1, E2, the standing assumptions and Proposition 3.5.
This module retains the incoming estimate as well as the exact chart.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- E1 applied to the extended radial-gauge datum, with E2 identification on
the late triangle, including its terminal ray. Paper `e1a0fd5`,
`eq:continuation-initial-datum`, lines 1390–1422. Incoming derivative
identification includes the terminal ray and the
initial incoming endpoint by the right-continuous BV convention. -/
theorem selected_small_bv_development (hE1 : SmallBVExistence) (hE2 : BVUniqueness)
    {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
    (hcones : SmallOutgoingConesStatement ui S) :
    ∃ ū ∈ Ioo ui 0, ∃ T : ℝ ≃o ℝ, ∃ Sdev : SSFields,
      (T : ℝ → ℝ) = radialChartMap (S.r ū) (S.lam ū) ū ∧
      T ū = 0 ∧ T 0 = 2 * S.r ū 0 ∧
      (∀ x, HasDerivAt (T : ℝ → ℝ) (selectedJacobian S ū x) x) ∧
      Continuous (selectedJacobian S ū) ∧
      (∃ c : ℝ, 0 < c ∧ ∀ x, c ≤ selectedJacobian S ū x) ∧
      BoundedVariationOn (selectedJacobian S ū) (Icc ū 0) ∧
      ChristodoulouBV smallBVDomain (Ici 0) Sdev ∧ SmallBVGeometry Sdev ∧
      (∀ v > 0, Sdev.r 0 v = v / 2 ∧
        Sdev.dvpsi 0 v = selectedInitialDatum S ū T v) ∧
      (∃ C : ℝ, ∀ u ≥ 0, smallBVOutgoingTV Sdev u < ENNReal.ofReal C) ∧
      (∃ C : ℝ, ∀ v > 0, smallBVIncomingTV Sdev v < ENNReal.ofReal C) ∧
      (∀ u v, ū ≤ u → u < v → v ≤ 0 →
        S.r u v = Sdev.r (T u) (T v) ∧ S.phi u v = Sdev.phi (T u) (T v) ∧
          S.m u v = Sdev.m (T u) (T v)) ∧
      let Sbar := S.pullback T.symm (inverseJacobian T (selectedJacobian S ū))
      (∀ u ∈ Ico 0 (2 * S.r ū 0), ∀ v ∈ Ioo u (2 * S.r ū 0),
        Sbar.lam u v = Sdev.lam u v ∧ Sbar.dvpsi u v = Sdev.dvpsi u v) ∧
      (∀ v ∈ Ioc 0 (2 * S.r ū 0), ∀ u ∈ Ico 0 v,
        Sbar.nu u v = Sdev.nu u v ∧ Sbar.dupsi u v = Sdev.dupsi u v) := by
  rcases hE1 with ⟨ε₀, hε₀, C₀, _, hex⟩
  have hε : ε₀ / 2 ∈ Ioo 0 ε₀ := ⟨by positivity, by linarith⟩
  obtain ⟨ū, hū, hsmall⟩ := hcones.choose hε.1
  obtain ⟨T, hT, hv, ht, hd, hc, hp, hBV⟩ := h.selected_chart hū
  have hdataC := h.selectedInitialDatum_continuous hū hv
  have hdataSmall : eVariationOn (selectedInitialDatum S ū T) (Ioi 0) <
      ENNReal.ofReal (ε₀ / 2) := by
    rw [h.selectedInitialDatum_variation hū hv]
    exact hsmall
  obtain ⟨Sdev, hdev, hdata, hgeom, hout, hin⟩ := hex (ε₀ / 2) hε
    (selectedInitialDatum S ū T)
    (fun v hv => (hdataC v hv).mono (Ici_subset_Ici.mpr hv)) hdataSmall
  have hrad : ∀ t ∈ Icc ū 0, T t = 2 * S.r ū t := by
    intro t htt
    rw [hT]
    exact radialChartMap_on_interval hū.2.le
      (h.regularCenter.localBV.axis_values ū
        (axis_subset_pastTriangle ui ⟨hū.1.le, hū.2, rfl⟩)).1 t htt
  have hsource := h.chr_in_selected_chart hū hv ht hd hc hp hBV
  have hb : 0 < 2 * S.r ū 0 := mul_pos (by norm_num)
    (h.r_pos ⟨hū.1.le, hū.2, hū.2.le, le_rfl⟩ hū.2)
  have hinit := h.selected_initial_data hū hrad
  have hinitdev : ∀ v ∈ Ioc 0 (2 * S.r ū 0),
      Sdev.r 0 v = v / 2 ∧ Sdev.dvpsi 0 v =
        1 / 2 * (S.dvpsi ū (T.symm v) / S.lam ū (T.symm v)) := by
    intro v hvi
    refine ⟨(hdata v hvi.1).1, ?_⟩
    rw [(hdata v hvi.1).2]
    exact selectedInitialDatum_on_segment S ū T (by simpa only [ht] using hvi.2)
  have he := uniqueness_on_late_triangle_of_bv hb hE2 hsource hdev
    (fun v hv => (hinit v hv).1) (fun v hv => (hinitdev v hv).1)
    (fun v hv => (hinit v hv).2.trans (hinitdev v hv).2.symm)
  exact ⟨ū, hū, T, Sdev, hT, hv, ht, hd, hc, hp, hBV, hdev, hgeom, hdata, ⟨C₀ * (ε₀ / 2), hout⟩,
    ⟨C₀ * (ε₀ / 2), hin⟩, h.selected_agreement_original_coordinates hū hrad he,
    late_triangle_derivatives_agree hsource hdev
      (fun p hu huv hv => ⟨(he p hu huv hv).1, (he p hu huv hv).2.1⟩)⟩

end AcExtensionPrinciple

end
