module

public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Tactic

/-!
# Abstract steps in the weighted remainder argument

Helpers for paper commit `e1a0fd5`, `equations.tex` lines 1278–1318.
-/

public section

namespace AcExtensionPrinciple

open scoped NNReal

/-- Banach's theorem with the displacement bound used in Proposition 3.4;
paper `e1a0fd5`, `equations.tex` lines 1278–1287. -/
theorem exists_unique_fixedPoint_half {E : Type*} [MetricSpace E] [CompleteSpace E]
    (Φ : E → E) (x₀ : E) {L : ℝ≥0} (hL : (L : ℝ) ≤ 1 / 2)
    (hΦ : LipschitzWith L Φ) :
    ∃ x, Φ x = x ∧ dist x x₀ ≤ 2 * dist (Φ x₀) x₀ ∧
      ∀ y, Φ y = y → y = x := by
  let : Nonempty E := ⟨x₀⟩
  have hc : ContractingWith L Φ := ⟨by exact_mod_cast (show (L : ℝ) < 1 by linarith), hΦ⟩
  refine ⟨hc.fixedPoint Φ, hc.fixedPoint_isFixedPt, ?_, ?_⟩
  · have hb := hc.dist_fixedPoint_le x₀
    rw [dist_comm x₀ (hc.fixedPoint Φ), dist_comm x₀ (Φ x₀)] at hb
    apply hb.trans
    apply (div_le_iff₀ hc.one_sub_K_pos).mpr
    nlinarith [dist_nonneg (x := Φ x₀) (y := x₀)]
  · intro y hy
    exact hc.fixedPoint_unique hy

/-- Absorb the composed source and radial operator bounds at a fixed point;
paper `e1a0fd5`, `equations.tex` lines 1278–1287
(`eq:constructed-remainder-bound`). -/
theorem fixedPoint_norm_bound {N M a b c₁ c₂ : ℝ}
    (hb : 0 ≤ b) (hsmall : b * c₂ < 1)
    (hN : N ≤ a + b * M) (hM : M ≤ c₁ + c₂ * N) :
    N ≤ (a + b * c₁) / (1 - b * c₂) := by
  apply (le_div_iff₀ (by linarith : 0 < 1 - b * c₂)).mpr
  have := mul_le_mul_of_nonneg_left hM hb
  nlinarith

/-- Identification by strict absorption of the finite full-domain L¹ norm;
paper `e1a0fd5`, `equations.tex` lines 1305–1318. -/
theorem remainder_difference_eq_zero {X C ε δ : ℝ} (hX : 0 ≤ X)
    (hbound : (1 - 3 * δ) * X ≤ C * ε ^ 2 * X)
    (hsmall : C * ε ^ 2 < 1 - 3 * δ) : X = 0 := by
  have : (1 - 3 * δ - C * ε ^ 2) * X ≤ 0 := by nlinarith
  have hp : 0 < 1 - 3 * δ - C * ε ^ 2 := by linarith
  nlinarith

end AcExtensionPrinciple

end
