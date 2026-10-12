module

public import AcExtensionPrinciple.Weighted.RadialL2
public import Mathlib.Order.Monotone.Extension
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Radial estimates for measurable equivalence classes on a cone

Statements for paper commit `e1a0fd5`, `equations.tex` lines 1139–1223.
These wrappers need measurability of the datum only on the cone; measurability
of the weight follows from its monotonicity.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory
open scoped ENNReal

/-- Extend the monotone cone weight measurably without changing its values on
the cone; paper `e1a0fd5`, `eq:late-radial-expansion-comparison`, lines 1139–1141. -/
theorem exists_measurable_cone_weight {w : ℝ → ℝ} {R : ℝ} (hR : 0 < R)
    (hpos : ∀ s ∈ Ioc 0 R, 0 ≤ w s) (hmono : MonotoneOn w (Ioc 0 R)) :
    ∃ W : ℝ → ℝ, Measurable W ∧ EqOn w W (Ioc 0 R) := by
  have hl : BddBelow (w '' Ioc 0 R) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    exact hpos s hs
  have hu : BddAbove (w '' Ioc 0 R) := by
    refine ⟨w R, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    exact hmono hs ⟨hR, le_rfl⟩ hs.2
  obtain ⟨W, hW, heq⟩ := hmono.exists_monotone_extension hl hu
  exact ⟨W, hW.measurable, heq⟩

/-- A change of representative preserves every radial primitive on the cone;
paper `e1a0fd5`, `equations.tex` lines 1204–1223. -/
theorem radialOperator_congr_ae_on_cone {f F : ℝ → ℝ} {R : ℝ}
    (heq : f =ᵐ[volume.restrict (Ioc 0 R)] F) :
    EqOn (radialOperator f) (radialOperator F) (Ioc 0 R) := by
  intro r hr
  have hsubset : Ioo 0 r ⊆ Ioc 0 R := fun s hs ↦ ⟨hs.1, hs.2.le.trans hr.2⟩
  have heq' := heq.filter_mono (ae_mono (Measure.restrict_mono hsubset le_rfl))
  have hi : (∫ s in Ioo 0 r, s * f s) = ∫ s in Ioo 0 r, s * F s := by
    apply integral_congr_ae
    filter_upwards [heq'] with s hs
    rw [hs]
  simp only [radialOperator, hi]

/-- Weighted radial integrals do not depend on the representative of the
datum or on the extension of the cone weight; paper `e1a0fd5`,
`equations.tex` lines 1204–1223. -/
theorem weighted_radial_integral_congr {w W f F : ℝ → ℝ} {R : ℝ} (p : ℕ)
    (hw : EqOn w W (Ioc 0 R)) (hf : f =ᵐ[volume.restrict (Ioc 0 R)] F) :
    (∫⁻ r in Ioc 0 R, ENNReal.ofReal (w r * |radialOperator f r| ^ p)) =
      ∫⁻ r in Ioc 0 R, ENNReal.ofReal (W r * |radialOperator F r| ^ p) := by
  apply setLIntegral_congr_fun measurableSet_Ioc
  intro r hr
  dsimp only
  rw [hw hr, radialOperator_congr_ae_on_cone hf hr]

/-- Weighted datum integrals do not depend on the representative or on the
weight extension; paper `e1a0fd5`, `equations.tex` lines 1204–1223. -/
theorem weighted_datum_integral_congr {w W f F : ℝ → ℝ} {R : ℝ} (p : ℕ)
    (hw : EqOn w W (Ioc 0 R)) (hf : f =ᵐ[volume.restrict (Ioc 0 R)] F) :
    (∫⁻ s in Ioc 0 R, ENNReal.ofReal (w s * |f s| ^ p)) =
      ∫⁻ s in Ioc 0 R, ENNReal.ofReal (W s * |F s| ^ p) := by
  apply lintegral_congr_ae
  filter_upwards [hf, ae_restrict_mem measurableSet_Ioc] with s hs hmem
  rw [hs, hw hmem]

/-- The cone L² estimate for a measurable equivalence class, with no separate
measurability assumption on the weight; paper `e1a0fd5`,
`eq:remainder-radial-estimate`, `equations.tex` lines 1204–1215. -/
theorem cone_weighted_radial_l2_le {w f : ℝ → ℝ} {R δ : ℝ}
    (hR : 0 < R) (hf : AEMeasurable f (volume.restrict (Ioc 0 R)))
    (hwpos : ∀ s ∈ Ioc 0 R, 0 < w s) (hmono : MonotoneOn w (Ioc 0 R))
    (hδ : δ < 3) (hgrowth : RadialWeightGrowth w R δ) :
    (∫⁻ r in Ioc 0 R, ENNReal.ofReal (w r * |radialOperator f r| ^ 2)) ≤
      ENNReal.ofReal ((2 / (3 - δ)) ^ 2) *
        ∫⁻ s in Ioc 0 R, ENNReal.ofReal (w s * |f s| ^ 2) := by
  obtain ⟨W, hW, heq⟩ := exists_measurable_cone_weight hR (fun s hs ↦ (hwpos s hs).le) hmono
  have hWpos : ∀ s ∈ Ioc 0 R, 0 ≤ W s := by
    intro s hs
    rw [← heq hs]
    exact (hwpos s hs).le
  have hWgrowth : RadialWeightGrowth W R δ := by
    intro y x hy hyx hxR
    rw [← heq ⟨hy.trans_le hyx, hxR⟩, ← heq ⟨hy, hyx.trans hxR⟩]
    exact hgrowth hy hyx hxR
  rw [weighted_radial_integral_congr 2 heq hf.ae_eq_mk,
    weighted_datum_integral_congr 2 heq hf.ae_eq_mk]
  exact weighted_radial_l2_le hW hf.measurable_mk hWpos hδ hWgrowth

/-- The cone L¹ estimate for a measurable equivalence class, with the paper's
inner-kernel constant; paper `e1a0fd5`, `eq:radial-l1-estimate`,
`equations.tex` lines 1217–1223. -/
theorem cone_weighted_radial_l1_le {w f : ℝ → ℝ} {R δ : ℝ}
    (hR : 0 < R) (hf : AEMeasurable f (volume.restrict (Ioc 0 R)))
    (hwpos : ∀ s ∈ Ioc 0 R, 0 < w s) (hmono : MonotoneOn w (Ioc 0 R))
    (hδ : δ < 1) (hgrowth : RadialWeightGrowth w R δ) :
    (∫⁻ r in Ioc 0 R, ENNReal.ofReal (w r * |radialOperator f r|)) ≤
      ENNReal.ofReal (1 / (1 - δ)) *
        ∫⁻ s in Ioc 0 R, ENNReal.ofReal (w s * |f s|) := by
  obtain ⟨W, hW, heq⟩ := exists_measurable_cone_weight hR (fun s hs ↦ (hwpos s hs).le) hmono
  have hWpos : ∀ s ∈ Ioc 0 R, 0 ≤ W s := by
    intro s hs
    rw [← heq hs]
    exact (hwpos s hs).le
  have hWgrowth : RadialWeightGrowth W R δ := by
    intro y x hy hyx hxR
    rw [← heq ⟨hy.trans_le hyx, hxR⟩, ← heq ⟨hy, hyx.trans hxR⟩]
    exact hgrowth hy hyx hxR
  have hrad := weighted_radial_integral_congr 1 heq hf.ae_eq_mk
  have hdatum := weighted_datum_integral_congr 1 heq hf.ae_eq_mk
  simp only [pow_one] at hrad hdatum
  rw [hrad, hdatum]
  exact weighted_radial_l1_le hW hf.measurable_mk hWpos hδ hWgrowth

end AcExtensionPrinciple

end
