module

public import AcExtensionPrinciple.Weighted.ClassDomain

/-!
# Exhausting the incoming slices of the proper triangle

Paper `e1a0fd5`, `eq:frozen-solution-operators`, lines 1265–1276,
and `eq:remainder-difference-kato`, lines 1305–1316. Countably many
proper incoming segments suffice to control the whole triangle.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory
open scoped ENNReal

/-- The iterated integral of the triangle indicator is the incoming-slice
integral. Endpoint changes remove only one-dimensional null sets. Paper
`e1a0fd5`, lines 1268–1276 and 1311–1316. -/
theorem weighted_triangle_incoming_indicator_integral (u₀ U : ℝ)
    (F : ℝ × ℝ → ℝ≥0∞) :
    (∫⁻ v, ∫⁻ s, (weightedTruncatedDomain u₀ U).indicator F (s, v)) =
      ∫⁻ v in Ioc u₀ 0, ∫⁻ s in Ico u₀ (min U v), F (s, v) := by
  classical
  have he (v : ℝ) :
      (∫⁻ s, (weightedTruncatedDomain u₀ U).indicator F (s, v)) =
        (Icc u₀ 0).indicator (fun v => ∫⁻ s in Ico u₀ (min U v), F (s, v)) v := by
    by_cases hv : v ∈ Icc u₀ 0
    · rw [indicator_of_mem hv]
      have hfun : (fun s => (weightedTruncatedDomain u₀ U).indicator F (s, v)) =
          (Icc u₀ (min U v)).indicator (fun s => F (s, v)) := by
        funext s
        simp only [indicator, weightedTruncatedDomain, mem_ofPred_eq, mem_Icc,
          le_min_iff]
        split_ifs <;> simp_all
      rw [hfun, lintegral_indicator measurableSet_Icc, restrict_Ico_eq_restrict_Icc]
    · rw [indicator_of_notMem hv]
      have hfun : (fun s => (weightedTruncatedDomain u₀ U).indicator F (s, v)) = 0 := by
        funext s
        apply indicator_of_notMem
        intro hs
        exact hv ⟨hs.1.trans hs.2.2.1, hs.2.2.2⟩
      rw [hfun]
      change (∫⁻ _s : ℝ, (0 : ℝ≥0∞)) = 0
      simp
  simp_rw [he]
  rw [lintegral_indicator measurableSet_Icc, ← restrict_Ioc_eq_restrict_Icc]

/-- Upper-bound a triangular lower integral by incoming slices without
assuming measurability of the output. Paper `e1a0fd5`,
`eq:frozen-solution-operators`, lines 1268–1276. -/
theorem weighted_triangle_lintegral_le_incoming (u₀ U : ℝ)
    (F : ℝ × ℝ → ℝ≥0∞) :
    (∫⁻ p in weightedTruncatedDomain u₀ U, F p) ≤
      ∫⁻ v in Ioc u₀ 0, ∫⁻ s in Ico u₀ (min U v), F (s, v) := by
  rw [← lintegral_indicator (measurableSet_weightedTruncatedDomain u₀ U),
    Measure.volume_eq_prod, ← lintegral_prod_swap]
  exact (lintegral_prod_le _).trans_eq
    (weighted_triangle_incoming_indicator_integral u₀ U F)

/-- Tonelli in the incoming order on the proper triangle. Paper
`e1a0fd5`, lines 1268–1276 and 1311–1316. -/
theorem weighted_triangle_lintegral_eq_incoming (u₀ U : ℝ)
    {F : ℝ × ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ p in weightedTruncatedDomain u₀ U, F p) =
      ∫⁻ v in Ioc u₀ 0, ∫⁻ s in Ico u₀ (min U v), F (s, v) := by
  rw [← lintegral_indicator (measurableSet_weightedTruncatedDomain u₀ U),
    Measure.volume_eq_prod, lintegral_prod_symm _
      (hF.indicator (measurableSet_weightedTruncatedDomain u₀ U)).aemeasurable]
  exact weighted_triangle_incoming_indicator_integral u₀ U F

/-- Bounds on rational proper endpoints control an entire incoming slice
by monotone convergence, with no regularity assumption on the integrand.
Paper `e1a0fd5`, lines 1268–1276 and 1311–1316. -/
theorem incoming_lintegral_le_of_rational_bounds {u₀ U v : ℝ}
    (f : ℝ → ℝ≥0∞) {B : ℝ≥0∞}
    (hbound : ∀ b : ℚ, u₀ ≤ (b : ℝ) → (b : ℝ) ≤ U → (b : ℝ) < v →
      (∫⁻ s in Icc u₀ (b : ℝ), f s) ≤ B) :
    (∫⁻ s in Ico u₀ (min U v), f s) ≤ B := by
  let T := {b : ℚ // u₀ ≤ (b : ℝ) ∧ (b : ℝ) < min U v}
  let A := fun b : T => Icc u₀ (b.1 : ℝ)
  have he : Ico u₀ (min U v) = ⋃ b : T, A b := by
    ext s
    constructor
    · intro hs
      obtain ⟨b, hsb, hb⟩ := exists_rat_btwn hs.2
      exact mem_iUnion.mpr ⟨⟨b, hs.1.trans hsb.le, hb⟩, hs.1, hsb.le⟩
    · intro hs
      obtain ⟨b, hb⟩ := mem_iUnion.mp hs
      exact ⟨hb.1, hb.2.trans_lt b.2.2⟩
  have hd : Directed (· ⊆ ·) A := by
    intro b c
    rcases le_total b.1 c.1 with hbc | hcb
    · exact ⟨c, Icc_subset_Icc_right (Rat.cast_le.mpr hbc), Subset.rfl⟩
    · exact ⟨b, Subset.rfl, Icc_subset_Icc_right (Rat.cast_le.mpr hcb)⟩
  rw [he, setLIntegral_iUnion_of_directed f hd]
  exact iSup_le (fun b => hbound b.1 b.2.1
    (b.2.2.le.trans (min_le_left _ _)) (b.2.2.trans_le (min_le_right _ _)))

/-- Integrate uniform bounds on countably many proper ray segments over
the full triangle. Paper `e1a0fd5`, lines 1268–1276 and 1311–1316. -/
theorem weighted_triangle_lintegral_le_of_ray_bounds {u₀ U : ℝ}
    (F : ℝ × ℝ → ℝ≥0∞) (B : ℝ → ℝ≥0∞)
    (hbound : ∀ᵐ v ∂volume.restrict (Ioc u₀ 0),
      ∀ b : ℚ, u₀ ≤ (b : ℝ) → (b : ℝ) ≤ U → (b : ℝ) < v →
        (∫⁻ s in Icc u₀ (b : ℝ), F (s, v)) ≤ B v) :
    (∫⁻ p in weightedTruncatedDomain u₀ U, F p) ≤ ∫⁻ v in Ioc u₀ 0, B v := by
  apply (weighted_triangle_lintegral_le_incoming u₀ U F).trans
  apply lintegral_mono_ae
  filter_upwards [hbound] with v hv
  exact incoming_lintegral_le_of_rational_bounds _ hv

end AcExtensionPrinciple

end
