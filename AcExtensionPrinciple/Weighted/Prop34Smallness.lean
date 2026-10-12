module

public import AcExtensionPrinciple.Weighted.Prop34FixedPoint

/-!
# A uniform numerical budget for the actual fixed point

Paper `e1a0fd5`, lines 1278–1287. The smallness threshold depends on
the original geometric gap and δ, and is independent of U.
-/

public section

namespace AcExtensionPrinciple

open scoped ENNReal

/-- The explicit ε² budget makes the product of the two actual operator
constants at most one half. Paper `e1a0fd5`, lines 1278–1287. -/
theorem weighted_fixedPoint_half_of_smallness {δ ε g : ℝ}
    (hδ : δ < 1 / 3) (hε : 0 ≤ ε) (hg : 0 < g)
    (hbudget : ε ^ 2 ≤ (1 - 3 * δ) * g * (3 - δ) / 24) :
    ENNReal.ofReal ((18 * ε ^ 2 / (1 - 3 * δ)) * ((1 - 3 * δ) / 2)⁻¹) ^
        (1 / 2 : ℝ) * ENNReal.ofReal (2 / (g * (3 - δ)) * ε) ≤
      ENNReal.ofReal (1 / 2) := by
  have hc : 0 < 1 - 3 * δ := by linarith
  have hd : 0 < 3 - δ := by linarith
  have heq : (18 * ε ^ 2 / (1 - 3 * δ)) * ((1 - 3 * δ) / 2)⁻¹ =
      (6 * ε / (1 - 3 * δ)) ^ 2 := by field_simp; ring
  rw [heq, ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by norm_num),
    ← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hden : 0 < (1 - 3 * δ) * g * (3 - δ) := by positivity
  have heq' : (6 * ε / (1 - 3 * δ)) * (2 / (g * (3 - δ)) * ε) =
      12 * ε ^ 2 / ((1 - 3 * δ) * g * (3 - δ)) := by field_simp; ring
  rw [heq', div_le_iff₀ hden]
  nlinarith

/-- One positive ε discharges both the L² contraction and L¹ identification
thresholds, uniformly in U. Paper `e1a0fd5`, lines 1278–1287 and 1311–1318. -/
theorem exists_weighted_identification_epsilon {δ g t : ℝ}
    (hδ : δ < 1 / 3) (hg : 0 < g) (ht : 0 < t) :
    ∃ ε : ℝ, 0 < ε ∧ ε ^ 2 ≤ (1 - 3 * δ) * g * (3 - δ) / 24 ∧
      (3 * ε / (1 - 3 * δ)) * ((g ^ 2)⁻¹ / (t * (1 - δ)) * ε) < 1 := by
  have hc : 0 < 1 - 3 * δ := by linarith
  have hd : 0 < 1 - δ := by linarith
  have hd3 : 0 < 3 - δ := by linarith
  let b₁ := (1 - 3 * δ) * g * (3 - δ) / 24
  let b₂ := (1 - 3 * δ) * g ^ 2 * t * (1 - δ) / 6
  have hb₁ : 0 < b₁ := by dsimp [b₁]; positivity
  have hb₂ : 0 < b₂ := by dsimp [b₂]; positivity
  let ε := Real.sqrt (min b₁ b₂)
  have he : ε ^ 2 = min b₁ b₂ := Real.sq_sqrt (lt_min hb₁ hb₂).le
  refine ⟨ε, Real.sqrt_pos.mpr (lt_min hb₁ hb₂), he.le.trans (min_le_left _ _), ?_⟩
  have hb := he.le.trans (min_le_right b₁ b₂)
  have hden : 0 < (1 - 3 * δ) * g ^ 2 * t * (1 - δ) := by positivity
  have heq : (3 * ε / (1 - 3 * δ)) * ((g ^ 2)⁻¹ / (t * (1 - δ)) * ε) =
      3 * ε ^ 2 / ((1 - 3 * δ) * g ^ 2 * t * (1 - δ)) := by field_simp
  rw [heq]
  apply lt_of_le_of_lt _ (by norm_num : (1 / 2 : ℝ) < 1)
  apply (div_le_iff₀ hden).mpr
  dsimp only [b₂] at hb
  linarith

end AcExtensionPrinciple

end
