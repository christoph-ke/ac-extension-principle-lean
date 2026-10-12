module

public import AcExtensionPrinciple.Continuation.Agreement
public import AcExtensionPrinciple.Continuation.PointwiseAgreement

/-!
# Pointwise identification with the selected development

Paper `e1a0fd5`, `equations.tex` lines 1404–1422. The BV representative
convention upgrades the outgoing agreement before the final endpoint and
the incoming agreement on every ray, including the terminal ray.
-/

public section

namespace AcExtensionPrinciple

open Set

/-- Development identification with pointwise BV derivative agreement on the common right intervals.
The terminal incoming ray is included; outgoing derivatives at the last endpoint are left to the
a.e. theorem. Paper `e1a0fd5`, `equations.tex` lines 222 and 1404–1422. E2 remains the same explicit
input. -/
theorem StandingFull.selected_development_pointwise_agreement
    {ui ū : ℝ} {S : SSFields}
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
        (∀ u ∈ Ico 0 (2 * S.r ū 0), ∀ v ∈ Ioo u (2 * S.r ū 0),
          Sbar.lam u v = Sdev.lam u v ∧ Sbar.dvpsi u v = Sdev.dvpsi u v) ∧
        (∀ v ∈ Ioc 0 (2 * S.r ū 0), ∀ u ∈ Ico 0 v,
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
    late_triangle_derivatives_agree hsource hdev
      (fun p hu huv hv => ⟨(he p hu huv hv).1, (he p hu huv hv).2.1⟩)⟩

end AcExtensionPrinciple

end
