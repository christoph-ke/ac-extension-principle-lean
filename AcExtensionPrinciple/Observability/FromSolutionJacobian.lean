module

public import AcExtensionPrinciple.Observability.FromSolutionEnergy
public import AcExtensionPrinciple.Observability.FromSolutionClockSource
public import AcExtensionPrinciple.Gauge.Variation
public import Mathlib.Analysis.Normed.Field.Basic

/-!
# Variation of the normalized incoming Jacobian

Paper `e1a0fd5`, `equations.tex` lines 1441–1443 and 1460–1473.
The positive expansion bound makes reciprocal Jacobians preserve BV.
The actual outgoing expansion on the cylinder is Lipschitz by the class regularity theorem, so its
reciprocal needs no new source premise.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory

/-- Reciprocation is Lipschitz on a positive half-line. Paper `e1a0fd5`,
lines 1441–1443 and 1460–1473 (Jacobian BV transport). -/
theorem chart_reciprocal_lipschitz {c : ℝ} (hc : 0 < c) :
    LipschitzOnWith ⟨(c * c)⁻¹, by positivity⟩ (fun x : ℝ => x⁻¹) (Ici c) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hx0 := hc.trans_le hx
  have hy0 := hc.trans_le hy
  rw [dist_inv_inv₀ hx0.ne' hy0.ne', Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos hx0, abs_of_pos hy0]
  change dist x y / (x * y) ≤ (c * c)⁻¹ * dist x y
  rw [div_eq_mul_inv, mul_comm (c * c)⁻¹ (dist x y)]
  apply mul_le_mul_of_nonneg_left _ dist_nonneg
  exact (inv_le_inv₀ (mul_pos hx0 hy0) (mul_pos hc hc)).mpr
    (mul_le_mul hx hy hc.le hx0.le)

/-- A uniformly positive BV density has a BV reciprocal. Paper
`e1a0fd5`, lines 1441–1443 and 1460–1473. -/
theorem boundedVariation_chart_reciprocal {f : ℝ → ℝ} {s : Set ℝ} {c : ℝ}
    (hc : 0 < c) (hf : BoundedVariationOn f s) (hlo : ∀ x ∈ s, c ≤ f x) :
    BoundedVariationOn (fun x => (f x)⁻¹) s :=
  (chart_reciprocal_lipschitz hc).comp_boundedVariationOn hlo hf

namespace DecayCylinder

/-- The outgoing expansion on any source cylinder has finite variation.
Uniqueness transfers the canonical Lipschitz theorem; degenerate
intervals have zero variation. Paper `e1a0fd5`, lines 731–737,
1441–1443 and 1460–1473. -/
theorem lambda_boundedVariation {ui b a₀ a₁ : ℝ} {S : SSFields}
    (c : DecayCylinder ui S b a₀ a₁) (h : StandingFull ui S) :
    BoundedVariationOn (fun u => S.lam u (c.v u)) (Icc a₀ a₁) := by
  rcases c.ordered.eq_or_lt with he | he
  · subst a₁
    simp [BoundedVariationOn]
  · obtain ⟨L, hL⟩ := h.cylinder_lambda_lipschitz_regular c.radius_pos (c.regularInterval h) he
    have hL' : LipschitzOnWith L (fun u => S.lam u (cylinderV h b u)) (uIcc a₀ a₁) := by
      simpa only [uIcc_of_le c.ordered] using hL
    have hBV := hL'.absolutelyContinuousOnInterval.boundedVariationOn
    rw [uIcc_of_le c.ordered] at hBV
    change eVariationOn (fun u => S.lam u (c.v u)) (Icc a₀ a₁) ≠ ⊤
    rw [eVariationOn.congr (show EqOn (fun u => S.lam u (c.v u))
      (fun u => S.lam u (cylinderV h b u)) (Icc a₀ a₁) from
      fun u hu => congrArg (S.lam u) (c.v_eq_canonical h hu))]
    exact hBV

/-- The inverse incoming Jacobian on entering rays has BV. The inverse
clock need only be increasing and map the time interval into the source
cylinder. These premises are discharged by `normalizedClockIso`.
Paper `e1a0fd5`, lines 1441–1443 and 1460–1473. -/
theorem incoming_jacobian_boundedVariation {ui b a₀ a₁ K T : ℝ} {S : SSFields}
    (c : DecayCylinder ui S b a₀ a₁) (h : StandingFull ui S)
    (hK : CylinderKBounds ui S K) (U : ℝ → ℝ)
    (hU : MonotoneOn U (Icc 0 T)) (hmap : MapsTo U (Icc 0 T) (Icc a₀ a₁)) :
    BoundedVariationOn (fun s => (S.lam (U s) (c.v (U s)))⁻¹) (Icc 0 T) := by
  have hBV : BoundedVariationOn (fun s => S.lam (U s) (c.v (U s))) (Icc 0 T) :=
    ne_top_of_le_ne_top (c.lambda_boundedVariation h)
      (eVariationOn.comp_le_of_monotoneOn (fun u => S.lam u (c.v u)) U hU hmap)
  apply boundedVariation_chart_reciprocal
    (inv_pos.mpr (zero_lt_one.trans_le hK.1)) hBV
  intro s hs
  exact (hK.2 _ (c.source_mem (hmap hs))).1

end DecayCylinder

end AcExtensionPrinciple

end
