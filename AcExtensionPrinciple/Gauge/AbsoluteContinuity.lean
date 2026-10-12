module

public import AcExtensionPrinciple.Gauge.Primitive
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Absolute continuity under increasing gauge maps

Components for paper `e1a0fd5`, `equations.tex` lines 1390–1422.
An integral representation proves composition preserves absolute continuity,
without requiring pointwise differentiability of the scalar field.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory

/-- An increasing differentiable change of variables preserves absolute
continuity. Paper `e1a0fd5`, `eq:continuation-null-gauge`, lines 1390–1422. -/
theorem absolutelyContinuous_comp_gauge {f T dT : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hT : MonotoneOn T (Icc a b))
    (hd : ∀ x ∈ Icc a b, HasDerivWithinAt T (dT x) (Icc a b) x)
    (hn : ∀ x ∈ Icc a b, 0 ≤ dT x)
    (hf : AbsolutelyContinuousOnInterval f (T a) (T b)) :
    AbsolutelyContinuousOnInterval (fun x => f (T x)) a b := by
  have hG : GaugeSegment T dT a b := GaugeSegment.of_hasDerivWithinAt
    (by simpa only [uIcc_of_le hab] using hd) (by simpa only [uIcc_of_le hab] using hn)
  have hp : IntervalPrimitive f (deriv f) (T a) (T b) :=
    ⟨hf.intervalIntegrable_deriv, hf.integral_deriv_eq_sub.symm⟩
  have hi := (hp.comp hG).1
  have hac := hi.absolutelyContinuousOnInterval_intervalIntegral (c := a) left_mem_uIcc
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => f (T a)) a b :=
    (LipschitzWith.const (f (T a))).lipschitzOnWith.absolutelyContinuousOnInterval
  apply (hc.add hac).congr
  intro x hx
  rw [uIcc_of_le hab] at hx
  have hsub : uIcc a x ⊆ Icc a b := by
    rw [uIcc_of_le hx.1]
    exact Icc_subset_Icc le_rfl hx.2
  have hGx : GaugeSegment T dT a x := GaugeSegment.of_hasDerivWithinAt
    (fun y hy => (hd y (hsub hy)).mono hsub) (fun y hy => hn y (hsub hy))
  have hTaTx : T a ≤ T x := hT ⟨le_rfl, hab⟩ hx hx.1
  have hTaTb : T a ≤ T b := hT ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  have hTxTb : T x ≤ T b := hT hx ⟨hab, le_rfl⟩ hx.2
  have hfx := hf.mono (show uIcc (T a) (T x) ⊆ uIcc (T a) (T b) by
    rw [uIcc_of_le hTaTx, uIcc_of_le hTaTb]
    exact Icc_subset_Icc le_rfl hTxTb)
  have hpx : IntervalPrimitive f (deriv f) (T a) (T x) :=
    ⟨hfx.intervalIntegrable_deriv, hfx.integral_deriv_eq_sub.symm⟩
  have he := (hpx.comp hGx).2
  change f (T a) + (∫ v in a..x, deriv f (T v) * dT v) = f (T x)
  change f (T x) - f (T a) = ∫ v in a..x, deriv f (T v) * dT v at he
  linarith

/-- A bound on the coordinate derivative gives a Lipschitz bound on each
compact interval. Paper `e1a0fd5`, `eq:continuation-null-gauge`, line 1395. -/
theorem gauge_lipschitzOn {T dT : ℝ → ℝ} {a b : ℝ} {C : NNReal}
    (hd : ∀ x ∈ Icc a b, HasDerivWithinAt T (dT x) (Icc a b) x)
    (hb : ∀ x ∈ Icc a b, ‖dT x‖₊ ≤ C) : LipschitzOnWith C T (Icc a b) :=
  (convex_Icc a b).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun x hx => hd x hx) hb

/-- A positive derivative lower bound gives the other half of the bi-Lipschitz
estimate for ordered points. Paper `e1a0fd5`, `eq:continuation-null-gauge`, 1296. -/
theorem gauge_lower_bound {T dT : ℝ → ℝ} {a b c : ℝ}
    (hd : ∀ x ∈ Icc a b, HasDerivWithinAt T (dT x) (Icc a b) x)
    (hb : ∀ x ∈ Icc a b, c ≤ dT x) :
    ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y → c * (y - x) ≤ T y - T x := by
  apply (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv
  · exact fun x hx => (hd x hx).continuousWithinAt
  · exact fun x hx => (hd x (interior_subset hx)).differentiableWithinAt.mono interior_subset
  · intro x hx
    have hx' : x ∈ Ioo a b := by simpa only [interior_Icc] using hx
    rw [((hd x (interior_subset hx)).hasDerivAt (Icc_mem_nhds hx'.1 hx'.2)).deriv]
    exact hb x (interior_subset hx)

end AcExtensionPrinciple

end
