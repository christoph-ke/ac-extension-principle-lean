module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Tactic

/-!
# Terminal scalar variation with a nonnegative weight

Helpers for paper `e1a0fd5`, `equations.tex` lines 952–962
(`eq:terminal-scalar-variation`). The blueshift density is required to be nonnegative. Its finite
integral supplies the integrability premise.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- AC variation is bounded by the integral of the absolute derivative;
paper `e1a0fd5`, `equations.tex` lines 952–962. -/
theorem ac_variation_le_integral_abs_deriv {P : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hP : AbsolutelyContinuousOnInterval P a b) :
    eVariationOn P (Icc a b) ≤ ENNReal.ofReal (∫ x in a..b, |deriv P x|) := by
  have hi := hP.intervalIntegrable_deriv.abs
  rw [eVariationOn]
  apply iSup_le
  rintro ⟨n, ⟨u, hu, hus⟩⟩
  have hsub (i j : ℕ) (hij : i ≤ j) : uIcc (u i) (u j) ⊆ uIcc a b := by
    rw [uIcc_of_le (hu hij), uIcc_of_le hab]
    exact Icc_subset_Icc (hus i).1 (hus j).2
  have hstep (i : ℕ) :
      edist (P (u (i + 1))) (P (u i)) ≤
        ENNReal.ofReal (∫ x in u i..u (i + 1), |deriv P x|) := by
    have hPac := hP.mono (hsub i (i + 1) (by omega))
    have hh := intervalIntegral.abs_integral_le_integral_abs
      (f := deriv P) (μ := volume) (hu (show i ≤ i + 1 by omega))
    rw [hPac.integral_deriv_eq_sub] at hh
    simpa [edist_dist, Real.dist_eq] using ENNReal.ofReal_le_ofReal hh
  calc
    _ ≤ ∑ i ∈ Finset.range n,
        ENNReal.ofReal (∫ x in u i..u (i + 1), |deriv P x|) := by
      exact Finset.sum_le_sum (fun i _ ↦ hstep i)
    _ = ENNReal.ofReal (∑ i ∈ Finset.range n,
        ∫ x in u i..u (i + 1), |deriv P x|) := by
      symm
      apply ENNReal.ofReal_sum_of_nonneg
      intro i _
      exact intervalIntegral.integral_nonneg_of_forall (hu (by omega))
        (fun _ ↦ abs_nonneg _)
    _ = ENNReal.ofReal (∫ x in u 0..u n, |deriv P x|) := by
      rw [intervalIntegral.sum_integral_adjacent_intervals
        (fun i _ ↦ hi.mono_set (hsub i (i + 1) (by omega)))]
    _ ≤ _ := ENNReal.ofReal_le_ofReal
      (intervalIntegral.integral_mono_interval (hus 0).1 (hu (Nat.zero_le n)) (hus n).2
        (Eventually.of_forall (fun _ ↦ abs_nonneg _)) hi)

/-- A nonnegative integrable weight and a finite amplitude bound control TV;
paper `e1a0fd5`, `equations.tex` lines 952–962 (`eq:terminal-scalar-variation`).
The weight is the blueshift density, and the amplitude bound is supplied by
uniform decay of the normalized outgoing scalar amplitude. -/
theorem scalar_variation_le_weighted_bound {P g A : ℝ → ℝ} {a b B M : ℝ}
    (hab : a ≤ b) (hP : AbsolutelyContinuousOnInterval P a b)
    (hg : IntervalIntegrable g volume a b)
    (hg0 : ∀ᵐ x ∂volume, x ∈ Ioo a b → 0 ≤ g x)
    (hd : ∀ᵐ x ∂volume, x ∈ Ioo a b → |deriv P x| ≤ g x * |A x|)
    (hA : ∀ x ∈ Icc a b, |A x| ≤ M) (hB : (∫ x in a..b, g x) ≤ B) :
    eVariationOn P (Icc a b) ≤ ENNReal.ofReal (B * M) := by
  have hM : 0 ≤ M := (abs_nonneg (A a)).trans (hA a ⟨le_rfl, hab⟩)
  have hint : (∫ x in a..b, |deriv P x|) ≤ ∫ x in a..b, g x * M := by
    apply intervalIntegral.integral_mono_ae_restrict hab hP.intervalIntegrable_deriv.abs
      (hg.mul_const M)
    rw [Filter.EventuallyLE, ← restrict_Ioo_eq_restrict_Icc,
      ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hg0, hd] with x hxg hxd hx
    exact (hxd hx).trans (mul_le_mul_of_nonneg_left
      (hA x (Ioo_subset_Icc_self hx)) (hxg hx))
  rw [intervalIntegral.integral_mul_const] at hint
  exact (ac_variation_le_integral_abs_deriv hab hP).trans
    (ENNReal.ofReal_le_ofReal (hint.trans (mul_le_mul_of_nonneg_right hB hM)))

/-- Real-valued TV estimate with the finite supremum represented by its LUB;
paper `e1a0fd5`, `equations.tex` lines 952–962 (`eq:terminal-scalar-variation`). -/
theorem scalar_variation_le_weighted_sup {P g A : ℝ → ℝ} {a b B S : ℝ}
    (hab : a ≤ b) (hP : AbsolutelyContinuousOnInterval P a b)
    (hg : IntervalIntegrable g volume a b)
    (hg0 : ∀ᵐ x ∂volume, x ∈ Ioo a b → 0 ≤ g x)
    (hd : ∀ᵐ x ∂volume, x ∈ Ioo a b → |deriv P x| ≤ g x * |A x|)
    (hS : IsLUB ((fun x ↦ |A x|) '' Icc a b) S)
    (hB : (∫ x in a..b, g x) ≤ B) :
    (eVariationOn P (Icc a b)).toReal ≤ B * S := by
  have hA (x : ℝ) (hx : x ∈ Icc a b) : |A x| ≤ S := hS.1 ⟨x, hx, rfl⟩
  have hS0 := (abs_nonneg (A a)).trans (hA a ⟨le_rfl, hab⟩)
  have hgint : 0 ≤ ∫ x in a..b, g x := by
    apply intervalIntegral.integral_nonneg_of_ae_restrict hab
    rw [Filter.EventuallyLE, ← restrict_Ioo_eq_restrict_Icc,
      ae_restrict_iff' measurableSet_Ioo]
    exact hg0
  have hBS : 0 ≤ B * S := mul_nonneg (hgint.trans hB) hS0
  have hbound := scalar_variation_le_weighted_bound hab hP hg hg0 hd hA hB
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq
    (ENNReal.toReal_ofReal hBS)

end AcExtensionPrinciple

end
