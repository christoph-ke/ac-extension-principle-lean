module

public import AcExtensionPrinciple.Continuation.Uniqueness

/-!
# Agreement almost everywhere on complete characteristic portions

Paper `e1a0fd5`, `equations.tex` lines 1411–1422.
Countable rational covers upgrade segment conclusions to each entire ray.
The incoming statement includes v = ṽ₀. Endpoint representatives are not
specified by this result.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory

/-- Primitive agreement on the late triangle gives almost-everywhere equality
of all four derivative fields on every ray, including the terminal incoming
ray. Paper `e1a0fd5`, lines 1411–1422. -/
theorem late_triangle_derivatives_agree_ae {S₁ S₂ : SSFields} {b : ℝ}
    (h₁ : ∀ a ∈ Ico 0 b,
      ChristodoulouBV (pastSet a b) (adjacentAxis (pastSet a b)) S₁)
    (h₂ : ChristodoulouBV smallBVDomain (Ici 0) S₂)
    (he : ∀ p : ℝ × ℝ, 0 ≤ p.1 → p.1 < p.2 → p.2 ≤ b →
      S₁.r p.1 p.2 = S₂.r p.1 p.2 ∧ S₁.phi p.1 p.2 = S₂.phi p.1 p.2) :
    (∀ u ∈ Ico 0 b, ∀ᵐ v, v ∈ Ioc u b →
      S₁.lam u v = S₂.lam u v ∧ S₁.dvpsi u v = S₂.dvpsi u v) ∧
    (∀ v ∈ Ioc 0 b, ∀ᵐ u, u ∈ Ico 0 v →
      S₁.nu u v = S₂.nu u v ∧ S₁.dupsi u v = S₂.dupsi u v) := by
  constructor
  · intro u hu
    have hq : ∀ q : ℚ, ∀ᵐ v,
        u < (q : ℝ) → (q : ℝ) < b → v ∈ Ioo (q : ℝ) b →
          S₁.lam u v = S₂.lam u v ∧ S₁.dvpsi u v = S₂.dvpsi u v := by
      intro q
      by_cases hgood : u < (q : ℝ) ∧ (q : ℝ) < b
      · have hs : outSeg u (q : ℝ) b ⊆ pastSet u b := by
          rintro ⟨x, y⟩ ⟨hx, hy⟩
          simp only [mem_singleton_iff] at hx
          subst x
          exact ⟨⟨hu.1, le_rfl⟩, hgood.1.trans_le hy.1, hy.2⟩
        exact (outgoing_derivatives_agree_ae hgood.2.le hs (h₁ u hu).1
          (h₂.on_pastSet u b).1 (fun p hp => he p hp.1.1 hp.2.1 hp.2.2)).mono
            (fun _ hv _ _ hvi => hv hvi)
      · exact Filter.Eventually.of_forall (fun _ hq hqb _ => False.elim (hgood ⟨hq, hqb⟩))
    have hne : ∀ᵐ v : ℝ, v ≠ b := by rw [ae_iff]; simp
    filter_upwards [ae_all_iff.mpr hq, hne] with v hv hnv
    intro hvi
    obtain ⟨q, huq, hqv⟩ := exists_rat_btwn hvi.1
    exact hv q huq (hqv.trans_le hvi.2) ⟨hqv, lt_of_le_of_ne hvi.2 hnv⟩
  · intro v hv
    have hq : ∀ q : ℚ, ∀ᵐ u,
        0 ≤ (q : ℝ) → (q : ℝ) < v → u ∈ Ioo 0 (q : ℝ) →
          S₁.nu u v = S₂.nu u v ∧ S₁.dupsi u v = S₂.dupsi u v := by
      intro q
      by_cases hgood : 0 ≤ (q : ℝ) ∧ (q : ℝ) < v
      · have hs : inSeg v 0 (q : ℝ) ⊆ pastSet (q : ℝ) b := by
          rintro ⟨x, y⟩ ⟨hx, hy⟩
          simp only [mem_singleton_iff] at hy
          subst y
          exact ⟨hx, hx.2.trans_lt hgood.2, hv.2⟩
        exact (incoming_derivatives_agree_ae hgood.1 hs
          (h₁ (q : ℝ) ⟨hgood.1, hgood.2.trans_le hv.2⟩).1
          (h₂.on_pastSet (q : ℝ) b).1 (fun p hp => he p hp.1.1 hp.2.1 hp.2.2)).mono
            (fun _ hu _ _ hui => hu hui)
      · exact Filter.Eventually.of_forall (fun _ hq hqv _ => False.elim (hgood ⟨hq, hqv⟩))
    have hne : ∀ᵐ u : ℝ, u ≠ 0 := by rw [ae_iff]; simp
    filter_upwards [ae_all_iff.mpr hq, hne] with u hu hnu
    intro hui
    obtain ⟨q, huq, hqv⟩ := exists_rat_btwn hui.2
    exact hu q (hui.1.trans huq.le) hqv ⟨lt_of_le_of_ne hui.1 hnu.symm, huq⟩

end AcExtensionPrinciple

end
