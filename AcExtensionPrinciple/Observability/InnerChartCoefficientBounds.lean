module

public import AcExtensionPrinciple.Observability.InnerChartAnnulus

/-!
# Characteristic Lipschitz control of logarithmic coefficients

Paper `e1a0fd5`, `equations.tex` line 1522 and lines 1460–1473, 1901.
Only primitive identities and bounded mass densities are used.
-/

public section

namespace AcExtensionPrinciple.NormalizedChartData

open Set MeasureTheory
open scoped NNReal

variable {b T K : ℝ} {S : SSFields} (h : NormalizedChartData b T K S)

/-- Both logarithmic coefficients have uniform annular bounds and
uniform Lipschitz constants in their transverse characteristic variable.
Paper `e1a0fd5`, `eq:logarithmic-expansions`, lines 1460–1473 and 1901. -/
theorem inner_coefficient_controls {δ : ℝ} (hδ : 0 < δ) :
    ∃ C L : ℝ≥0,
      (∀ p ∈ h.innerAnnulus δ,
        |innerNuCoefficient S p.1 p.2| ≤ C ∧ |innerLamCoefficient S p.1 p.2| ≤ C) ∧
      (∀ t x y, x ≤ y → inSeg t x y ⊆ h.innerAnnulus δ →
        LipschitzOnWith L (fun s => innerNuCoefficient S s t) (Icc x y)) ∧
      (∀ s x y, x ≤ y → outSeg s x y ⊆ h.innerAnnulus δ →
        LipschitzOnWith L (innerLamCoefficient S s) (Icc x y)) := by
  obtain ⟨B, hB, hb⟩ := h.inner_annular_bounds hδ
  have hK : 0 < K := zero_lt_one.trans_le h.K_ge_one
  obtain ⟨L, hL⟩ := innerExpansionCoefficient_lipschitz (B := B) hδ (div_pos hδ hK)
  let C : ℝ≥0 := ⟨B, hB⟩
  refine ⟨C, L * C, ?_, ?_, ?_⟩
  · intro p hp
    exact ⟨(hb p hp).2.2.2.2.2.2.2.1, (hb p hp).2.2.2.2.2.2.2.2⟩
  · intro t x y hxy hseg
    have hsmall {l r : ℝ} (hl : l ∈ Icc x y) (hr : r ∈ Icc x y) :
        inSeg t l r ⊆ h.innerAnnulus δ := by
      rintro ⟨s, z⟩ ⟨hs, hz⟩
      exact hseg ⟨⟨hl.1.trans hs.1, hs.2.trans hr.2⟩, hz⟩
    have hr : LipschitzOnWith C (fun s => S.r s t) (Icc x y) := by
      apply inner_primitive_lipschitz hB
      · intro l hl r hr hlr
        exact h.equations.radius_s t l r hlr (fun p hp => (hsmall hl hr hp).1)
      · intro s hs
        exact (hb (s, t) (hseg ⟨hs, by simp⟩)).2.2.2.1
    have hm : LipschitzOnWith C (fun s => S.m s t) (Icc x y) := by
      apply inner_primitive_lipschitz hB
      · intro l hl r hr hlr
        exact h.equations.mass_s t l r hlr (fun p hp => (hsmall hl hr hp).1)
      · intro s hs
        exact (hb (s, t) (hseg ⟨hs, by simp⟩)).2.2.2.2.1
    have hl : LipschitzOnWith C (fun s => S.lam s t) (Icc x y) := by
      apply inner_primitive_lipschitz hB
      · intro l hl r hr hlr
        exact h.equations.lam_s t l r hlr ((hsmall hl hr).trans (h.innerAnnulus_subset hδ))
      · intro s hs
        exact (hb (s, t) (hseg ⟨hs, by simp⟩)).2.2.2.2.2.2.1
    have hp : LipschitzOnWith C (fun s => (S.r s t, S.m s t, S.lam s t)) (Icc x y) := by
      simpa only [max_self] using hr.prodMk (hm.prodMk hl)
    exact hL.comp hp (fun s hs =>
      h.inner_coefficient_box_mem hδ (hseg ⟨hs, by simp⟩)
        (hb (s, t) (hseg ⟨hs, by simp⟩)).1
        (hb (s, t) (hseg ⟨hs, by simp⟩)).2.1
        (hb (s, t) (hseg ⟨hs, by simp⟩)).2.2.1)
  · intro s x y hxy hseg
    have hsmall {l r : ℝ} (hl : l ∈ Icc x y) (hr : r ∈ Icc x y) :
        outSeg s l r ⊆ h.innerAnnulus δ := by
      rintro ⟨z, t⟩ ⟨hz, ht⟩
      exact hseg ⟨hz, hl.1.trans ht.1, ht.2.trans hr.2⟩
    have hr : LipschitzOnWith C (S.r s) (Icc x y) := by
      apply inner_primitive_lipschitz hB
      · intro l hl r hr hlr
        exact h.equations.radius_t s l r hlr (fun p hp => (hsmall hl hr hp).1)
      · intro t ht
        exact (hb (s, t) (hseg ⟨by simp, ht⟩)).2.2.1
    have hm : LipschitzOnWith C (S.m s) (Icc x y) := by
      apply inner_primitive_lipschitz hB
      · intro l hl r hr hlr
        exact h.equations.mass_t s l r hlr (fun p hp => (hsmall hl hr hp).1)
      · intro t ht
        exact (hb (s, t) (hseg ⟨by simp, ht⟩)).2.2.2.2.2.1
    have hn : LipschitzOnWith C (S.nu s) (Icc x y) := by
      apply inner_primitive_lipschitz hB
      · intro l hl r hr hlr
        exact h.equations.nu_t s l r hlr ((hsmall hl hr).trans (h.innerAnnulus_subset hδ))
      · intro t ht
        exact (hb (s, t) (hseg ⟨by simp, ht⟩)).2.2.2.2.2.2.1
    have hp : LipschitzOnWith C (fun t => (S.r s t, S.m s t, S.nu s t)) (Icc x y) := by
      simpa only [max_self] using hr.prodMk (hm.prodMk hn)
    exact hL.comp hp (fun t ht =>
      h.inner_coefficient_box_mem hδ (hseg ⟨by simp, ht⟩)
        (hb (s, t) (hseg ⟨by simp, ht⟩)).1
        (hb (s, t) (hseg ⟨by simp, ht⟩)).2.1
        (hb (s, t) (hseg ⟨by simp, ht⟩)).2.2.2.1)

end AcExtensionPrinciple.NormalizedChartData

end
