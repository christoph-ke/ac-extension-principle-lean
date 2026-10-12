module

public import AcExtensionPrinciple.Continuation.SelectedChart
public import AcExtensionPrinciple.Continuation.RayAgreement

/-!
# Identification with the new development

Paper `e1a0fd5`, `equations.tex` lines 1390–1422. Original class membership, domain restriction and
scalar reconstruction are assembled with the explicit E2 input. The result covers the terminal ray
and records a.e. derivative agreement. The pointwise upgrade using the BV convention is in
PointwiseDevelopment.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory

/-- Coordinate identities for the transformed original data. Paper `e1a0fd5`,
`eq:continuation-initial-datum`, lines 1396–1400. -/
theorem StandingFull.selected_initial_data {ui ū : ℝ} {S : SSFields}
    (h : StandingFull ui S) (hū : ū ∈ Ioo ui 0) {T : ℝ ≃o ℝ}
    (hT : ∀ t ∈ Icc ū 0, T t = 2 * S.r ū t) :
    ∀ v ∈ Ioc 0 (2 * S.r ū 0),
      (S.pullback T.symm (inverseJacobian T (selectedJacobian S ū))).r 0 v = v / 2 ∧
      (S.pullback T.symm (inverseJacobian T (selectedJacobian S ū))).dvpsi 0 v =
        1 / 2 * (S.dvpsi ū (T.symm v) / S.lam ū (T.symm v)) := by
  have hg0 := (h.regularCenter.localBV.axis_values ū
    (axis_subset_pastTriangle ui ⟨hū.1.le, hū.2, rfl⟩)).1
  have hvertex : T ū = 0 := by rw [hT ū ⟨le_rfl, hū.2.le⟩, hg0]; ring
  have hterminal : T 0 = 2 * S.r ū 0 := hT 0 ⟨hū.2.le, le_rfl⟩
  have hU0 : T.symm 0 = ū := by rw [← hvertex, T.symm_apply_apply]
  have hUb : T.symm (2 * S.r ū 0) = 0 := by rw [← hterminal, T.symm_apply_apply]
  intro v hv
  have hx : T.symm v ∈ Icc ū 0 :=
    ⟨by simpa only [hU0] using (T.symm.strictMono hv.1).le,
      by simpa only [hUb] using T.symm.monotone hv.2⟩
  have hrad : 2 * S.r ū (T.symm v) = v := (hT _ hx).symm.trans (T.apply_symm_apply v)
  have hlam : S.lam ū (T.symm v) ≠ 0 := ne_of_gt
    (h.lam_pos (p := (ū, T.symm v)) ⟨hū.1.le, hū.2, hx.1, hx.2⟩)
  constructor
  · change S.r (T.symm 0) (T.symm v) = v / 2
    rw [hU0]
    linarith
  · simp only [SSFields.pullback, inverseJacobian, selectedJacobian,
      radialChartDerivative_on_interval hx, hU0]
    field_simp [hlam]

/-- Agreement in the radial chart gives agreement with the original primitive
fields on the whole late triangle, including v = 0. Paper `e1a0fd5`,
lines 1411–1422. -/
theorem StandingFull.selected_agreement_original_coordinates
    {ui ū : ℝ} {S Sdev : SSFields} {T : ℝ ≃o ℝ} {dU : ℝ → ℝ}
    (h : StandingFull ui S) (hū : ū ∈ Ioo ui 0)
    (hT : ∀ t ∈ Icc ū 0, T t = 2 * S.r ū t)
    (he : ∀ p : ℝ × ℝ, 0 ≤ p.1 → p.1 < p.2 → p.2 ≤ 2 * S.r ū 0 →
      (S.pullback T.symm dU).r p.1 p.2 = Sdev.r p.1 p.2 ∧
      (S.pullback T.symm dU).phi p.1 p.2 = Sdev.phi p.1 p.2 ∧
      (S.pullback T.symm dU).m p.1 p.2 = Sdev.m p.1 p.2) :
    ∀ u v, ū ≤ u → u < v → v ≤ 0 →
      S.r u v = Sdev.r (T u) (T v) ∧ S.phi u v = Sdev.phi (T u) (T v) ∧
        S.m u v = Sdev.m (T u) (T v) := by
  have hg0 := (h.regularCenter.localBV.axis_values ū
    (axis_subset_pastTriangle ui ⟨hū.1.le, hū.2, rfl⟩)).1
  have hvertex : T ū = 0 := by rw [hT ū ⟨le_rfl, hū.2.le⟩, hg0]; ring
  have hterminal : T 0 = 2 * S.r ū 0 := hT 0 ⟨hū.2.le, le_rfl⟩
  intro u v hu huv hv
  have hu' : 0 ≤ T u := by rw [← hvertex]; exact T.monotone hu
  have hv' : T v ≤ 2 * S.r ū 0 := by rw [← hterminal]; exact T.monotone hv
  simpa only [SSFields.pullback, T.symm_apply_apply]
    using he (T u, T v) hu' (T.strictMono huv) hv'

/-- The selected inverse chart identifies every development from the extended normalized derivative
datum with the original solution, on the late triangle minus Γ and on its terminal ray. All four
derivative fields agree a.e. on each complete characteristic portion. Paper `e1a0fd5`, lines
1404–1422. E2 is an explicit hypothesis; a separate mass ODE is unnecessary. -/
theorem StandingFull.selected_development_agreement {ui ū : ℝ} {S : SSFields}
    (h : StandingFull ui S) (hū : ū ∈ Ioo ui 0) (hE2 : BVUniqueness) :
    ∃ T : ℝ ≃o ℝ, (∀ t ∈ Icc ū 0, T t = 2 * S.r ū t) ∧
      ∀ Sdev : SSFields, ChristodoulouBV smallBVDomain (Ici 0) Sdev →
        (∀ v ∈ Ioc 0 (2 * S.r ū 0), Sdev.r 0 v = v / 2 ∧
          Sdev.dvpsi 0 v = 1 / 2 * (S.dvpsi ū (T.symm v) / S.lam ū (T.symm v))) →
        let Sbar := S.pullback T.symm (inverseJacobian T (selectedJacobian S ū))
        (∀ p : ℝ × ℝ, 0 ≤ p.1 → p.1 < p.2 → p.2 ≤ 2 * S.r ū 0 →
          Sbar.r p.1 p.2 = Sdev.r p.1 p.2 ∧ Sbar.phi p.1 p.2 = Sdev.phi p.1 p.2 ∧
            Sbar.m p.1 p.2 = Sdev.m p.1 p.2) ∧
        (∀ u v, ū ≤ u → u < v → v ≤ 0 →
          S.r u v = Sdev.r (T u) (T v) ∧ S.phi u v = Sdev.phi (T u) (T v) ∧
            S.m u v = Sdev.m (T u) (T v)) ∧
        (∀ u ∈ Ico 0 (2 * S.r ū 0), ∀ᵐ v, v ∈ Ioc u (2 * S.r ū 0) →
          Sbar.lam u v = Sdev.lam u v ∧ Sbar.dvpsi u v = Sdev.dvpsi u v) ∧
        (∀ v ∈ Ioc 0 (2 * S.r ū 0), ∀ᵐ u, u ∈ Ico 0 v →
          Sbar.nu u v = Sdev.nu u v ∧ Sbar.dupsi u v = Sdev.dupsi u v) := by
  obtain ⟨T, hT, hsource⟩ := h.exists_selected_chart_bv hū
  refine ⟨T, hT, ?_⟩
  intro Sdev hdev hdata
  have hb : 0 < 2 * S.r ū 0 := mul_pos (by norm_num)
    (h.r_pos ⟨hū.1.le, hū.2, hū.2.le, le_rfl⟩ hū.2)
  have hinit := h.selected_initial_data hū hT
  have he := uniqueness_on_late_triangle_of_bv hb hE2 hsource hdev
    (fun v hv => (hinit v hv).1) (fun v hv => (hdata v hv).1)
    (fun v hv => (hinit v hv).2.trans (hdata v hv).2.symm)
  exact ⟨he, h.selected_agreement_original_coordinates hū hT he,
    late_triangle_derivatives_agree_ae hsource hdev
    (fun p hu huv hv => ⟨(he p hu huv hv).1, (he p hu huv hv).2.1⟩)⟩

end AcExtensionPrinciple

end
