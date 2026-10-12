module

public import AcExtensionPrinciple.Continuation.RadialChart
public import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# The inverse Jacobian of the selected chart

Paper `e1a0fd5`, `equations.tex` lines 1390–1411. The positive BV expansion on the selected cone
supplies a continuous, positive BV inverse Jacobian, with two-sided bounds on the compact image.
-/

public section

namespace AcExtensionPrinciple

open Set
open scoped Topology

/-- Reciprocal on a positive half-line preserves bounded variation.
Paper `e1a0fd5`, lines 1390–1411, inverse Jacobian component. -/
theorem boundedVariation_inv_of_lower {f : ℝ → ℝ} {s : Set ℝ} {c : ℝ}
    (hc : 0 < c) (hb : ∀ x ∈ s, c ≤ f x) (hBV : BoundedVariationOn f s) :
    BoundedVariationOn (fun x => (f x)⁻¹) s := by
  let C : NNReal := ⟨(c ^ 2)⁻¹, inv_nonneg.mpr (sq_nonneg c)⟩
  have hLip : LipschitzOnWith C (fun x : ℝ => x⁻¹) (Ici c) := by
    apply (convex_Ici c).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun x hx => (hasDerivAt_inv (ne_of_gt (hc.trans_le hx))).hasDerivWithinAt)
    intro x hx
    change ‖-(x ^ 2)⁻¹‖₊ ≤ C
    apply NNReal.coe_le_coe.mp
    change ‖-(x ^ 2)⁻¹‖ ≤ (c ^ 2)⁻¹
    rw [Real.norm_eq_abs, abs_neg, abs_inv, abs_sq]
    apply inv_anti₀ (sq_pos_of_pos hc)
    exact sq_le_sq₀ hc.le (hc.le.trans hx) |>.mpr hx
  exact hLip.comp_boundedVariationOn hb hBV

/-- Jacobian of the inverse coordinate. Paper `e1a0fd5`,
`eq:continuation-null-gauge`, lines 1393–1400 and 1411. -/
@[expose] noncomputable def inverseJacobian (T : ℝ ≃o ℝ) (dT : ℝ → ℝ) (x : ℝ) : ℝ :=
  (dT (T.symm x))⁻¹

/-- The inverse chart has the reciprocal derivative everywhere.
Paper `e1a0fd5`, lines 1390–1411. -/
theorem inverseJacobian_hasDerivAt {T : ℝ ≃o ℝ} {dT : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt (T : ℝ → ℝ) (dT x) x) (hn : ∀ x, dT x ≠ 0) :
    ∀ x, HasDerivAt (T.symm : ℝ → ℝ) (inverseJacobian T dT x) x := by
  intro x
  exact hasDerivAt_inverse_gauge (T.symm.continuous.continuousAt)
    (hd (T.symm x)) (hn (T.symm x)) (Filter.Eventually.of_forall T.apply_symm_apply)

/-- Continuity and positivity of the inverse Jacobian. Paper `e1a0fd5`,
lines 1390–1411. -/
theorem inverseJacobian_continuous_pos {T : ℝ ≃o ℝ} {dT : ℝ → ℝ}
    (hd : Continuous dT) (hp : ∀ x, 0 < dT x) :
    Continuous (inverseJacobian T dT) ∧ ∀ x, 0 < inverseJacobian T dT x := by
  exact ⟨(hd.comp T.symm.continuous).inv₀ (fun x => ne_of_gt (hp (T.symm x))),
    fun x => inv_pos.mpr (hp (T.symm x))⟩

/-- BV and compact two-sided bounds for the inverse Jacobian.
Paper `e1a0fd5`, lines 1390–1411. -/
theorem inverseJacobian_compact_bounds {T : ℝ ≃o ℝ} {dT : ℝ → ℝ} {a b c : ℝ}
    (_ha : a ≤ 0) (_hb : 0 ≤ b) (hvertex : T a = 0) (hterminal : T 0 = b)
    (hd : Continuous dT) (hc : 0 < c) (hl : ∀ x, c ≤ dT x)
    (hBV : BoundedVariationOn dT (Icc a 0)) :
    BoundedVariationOn (inverseJacobian T dT) (Icc 0 b) ∧
      ∃ q J : ℝ, 0 < q ∧ 0 ≤ J ∧
        ∀ x ∈ Icc 0 b, q ≤ inverseJacobian T dT x ∧ |inverseJacobian T dT x| ≤ J := by
  have hUa : T.symm 0 = a := by rw [← hvertex, T.symm_apply_apply]
  have hUb : T.symm b = 0 := by rw [← hterminal, T.symm_apply_apply]
  have hmap : MapsTo T.symm (Icc 0 b) (Icc a 0) := by
    intro x hx
    simpa only [mem_Icc, hUa, hUb] using
      (show T.symm 0 ≤ T.symm x ∧ T.symm x ≤ T.symm b from
        ⟨T.symm.monotone hx.1, T.symm.monotone hx.2⟩)
  have hcomp : BoundedVariationOn (fun x => dT (T.symm x)) (Icc 0 b) :=
    ne_top_of_le_ne_top hBV (eVariationOn.comp_le_of_monotoneOn dT T.symm
      (T.symm.monotone.monotoneOn _) hmap)
  refine ⟨boundedVariation_inv_of_lower hc (fun x _ => hl (T.symm x)) hcomp, ?_⟩
  obtain ⟨L, hL⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hd.continuousOn : ContinuousOn dT (Icc a 0))
  let R := |L| + 1
  have hR : 0 < R := by dsimp [R]; positivity
  refine ⟨R⁻¹, c⁻¹, inv_pos.mpr hR, (inv_pos.mpr hc).le, ?_⟩
  intro x hx
  have hp : 0 < dT (T.symm x) := hc.trans_le (hl _)
  have hupper : dT (T.symm x) ≤ R := by
    have hnorm : |dT (T.symm x)| ≤ L := by
      simpa only [Real.norm_eq_abs] using hL _ (hmap hx)
    exact (le_abs_self _).trans (hnorm.trans ((le_abs_self L).trans (by dsimp [R]; linarith)))
  exact ⟨inv_anti₀ hp hupper,
    (abs_of_pos (inv_pos.mpr hp)).trans_le (inv_anti₀ hc (hl _))⟩

end AcExtensionPrinciple

end
