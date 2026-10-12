module

public import AcExtensionPrinciple.Gauge.Reparam
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.Calculus.Deriv.Inverse

/-!
# Gauge transport of characteristic integral identities

Components for paper `e1a0fd5`, `equations.tex` lines 1390–1422,
`eq:continuation-null-gauge`. Substitution is valid for integrable densities;
continuity of the densities is not required. Each equation is stated per segment.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory

/-- Minimal substitution premises on a segment. Paper `e1a0fd5`,
`eq:continuation-null-gauge`, lines 1390–1395. -/
structure GaugeSegment (T dT : ℝ → ℝ) (a b : ℝ) : Prop where
  continuous : ContinuousOn T (uIcc a b)
  hasDeriv : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt T (dT x) x
  nonneg : ∀ x ∈ Ioo (min a b) (max a b), 0 ≤ dT x

/-- Differentiability and a nonnegative derivative supply the substitution premises.
Paper `e1a0fd5`, `eq:continuation-null-gauge`, lines 1390–1395. -/
theorem GaugeSegment.of_hasDerivAt {T dT : ℝ → ℝ} {a b : ℝ}
    (hd : ∀ x ∈ uIcc a b, HasDerivAt T (dT x) x)
    (hn : ∀ x ∈ uIcc a b, 0 ≤ dT x) : GaugeSegment T dT a b where
  continuous x hx := (hd x hx).continuousAt.continuousWithinAt
  hasDeriv x hx := hd x (Ioo_subset_Icc_self hx)
  nonneg x hx := hn x (Ioo_subset_Icc_self hx)

/-- Domain-relative coordinate derivatives suffice for substitution; full
pointwise derivatives are needed only in the interval interior. Paper `e1a0fd5`,
`eq:continuation-null-gauge`, lines 1390–1422. -/
theorem GaugeSegment.of_hasDerivWithinAt {T dT : ℝ → ℝ} {a b : ℝ}
    (hd : ∀ x ∈ uIcc a b, HasDerivWithinAt T (dT x) (uIcc a b) x)
    (hn : ∀ x ∈ uIcc a b, 0 ≤ dT x) : GaugeSegment T dT a b where
  continuous x hx := (hd x hx).continuousWithinAt
  hasDeriv x hx := (hd x (Ioo_subset_Icc_self hx)).hasDerivAt
    (Icc_mem_nhds hx.1 hx.2)
  nonneg x hx := hn x (Ioo_subset_Icc_self hx)

/-- Derivative of an actual local inverse chart. Paper `e1a0fd5`,
`eq:continuation-null-gauge`, lines 1390–1422. -/
theorem hasDerivAt_inverse_gauge {T U dT : ℝ → ℝ} {x : ℝ}
    (hU : ContinuousAt U x) (hd : HasDerivAt T (dT (U x)) (U x))
    (hn : dT (U x) ≠ 0) (hi : ∀ᶠ y in nhds x, T (U y) = y) :
    HasDerivAt U (dT (U x))⁻¹ x :=
  HasDerivAt.of_local_left_inverse hU hd hn hi

/-- Primitive substitution in both directions, including integrability.
Paper `e1a0fd5`, `eq:continuation-null-gauge`, lines 1390–1422. -/
theorem intervalPrimitive_comp_iff {f g T dT : ℝ → ℝ} {a b : ℝ}
    (hT : GaugeSegment T dT a b) :
    IntervalPrimitive (fun x => f (T x)) (fun x => g (T x) * dT x) a b ↔
      IntervalPrimitive f g (T a) (T b) := by
  have hi := intervalIntegral.integrable_deriv_smul_comp_iff_of_deriv_nonneg
    (g := g) hT.continuous hT.hasDeriv hT.nonneg
  have he := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (g := g) hT.continuous hT.hasDeriv hT.nonneg
  simp only [smul_eq_mul, Function.comp_apply, mul_comm (dT _)] at hi
  simp only [Function.comp_apply] at he
  simp only [IntervalPrimitive, hi, he]

/-- Forward primitive transport. Paper `e1a0fd5`,
`eq:continuation-null-gauge`, lines 1390–1422. -/
theorem IntervalPrimitive.comp {f g T dT : ℝ → ℝ} {a b : ℝ}
    (h : IntervalPrimitive f g (T a) (T b)) (hT : GaugeSegment T dT a b) :
    IntervalPrimitive (fun x => f (T x)) (fun x => g (T x) * dT x) a b :=
  (intervalPrimitive_comp_iff hT).mpr h

/-- Inverse-coordinate transport; only inverse endpoint values are needed here.
For an inverse chart, `dU = 1/(dT ∘ U)`. Paper `e1a0fd5`,
`eq:continuation-null-gauge`, lines 1390–1422. -/
theorem IntervalPrimitive.comp_inverse {f g T U dU : ℝ → ℝ} {a b : ℝ}
    (h : IntervalPrimitive f g a b) (hU : GaugeSegment U dU (T a) (T b))
    (ha : U (T a) = a) (hb : U (T b) = b) :
    IntervalPrimitive (fun x => f (U x)) (fun x => g (U x) * dU x) (T a) (T b) := by
  apply (intervalPrimitive_comp_iff hU).mpr
  simpa only [ha, hb] using h

/-- Primitive equations are unchanged by equal fields on the segment.
Paper `e1a0fd5`, `equations.tex` lines 1411–1422. -/
theorem IntervalPrimitive.congr {f g F G : ℝ → ℝ} {a b : ℝ}
    (h : IntervalPrimitive f g a b) (hf : EqOn f F (uIcc a b))
    (hg : EqOn g G (uIcc a b)) : IntervalPrimitive F G a b := by
  refine ⟨h.1.congr (fun x hx => hg (uIoc_subset_uIcc hx)), ?_⟩
  rw [← hf right_mem_uIcc, ← hf left_mem_uIcc, h.2]
  exact intervalIntegral.integral_congr hg

/-- Constant scaling of a primitive, used for transverse derivative fields.
Paper `e1a0fd5`, `eq:continuation-null-gauge`, lines 1390–1422. -/
theorem IntervalPrimitive.mul_const {f g : ℝ → ℝ} {a b : ℝ}
    (h : IntervalPrimitive f g a b) (c : ℝ) :
    IntervalPrimitive (fun x => f x * c) (fun x => g x * c) a b := by
  refine ⟨h.1.mul_const c, ?_⟩
  rw [intervalIntegral.integral_mul_const, ← h.2]
  ring

/-- A continuous characteristic density and its primitive identities give the
radius derivative within the closed cone segment, including both endpoints.
Paper `e1a0fd5`, `eq:continuation-null-gauge`, lines 1390–1395; local continuity
is recorded in `equations.tex` line 222. -/
theorem hasDerivWithinAt_of_intervalPrimitives {f g : ℝ → ℝ} {a b x : ℝ}
    (hf : ∀ y ∈ Icc a b, IntervalPrimitive f g a y)
    (hg : ContinuousOn g (Icc a b)) (hx : x ∈ Icc a b) :
    HasDerivWithinAt f (g x) (Icc a b) x := by
  let : Fact (x ∈ Icc a b) := ⟨hx⟩
  have h := intervalIntegral.integral_hasDerivWithinAt_right
    (s := Icc a b) (t := Icc a b) (hf x hx).1
    (hg.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc x) (hg x hx)
  apply (h.const_add (f a)).congr_of_mem _ hx
  intro y hy
  have he := (hf y hy).2
  change f y = f a + ∫ t in a..y, g t
  linarith

namespace SSFields

/-- Outgoing radius equation in the pullback chart. Paper `e1a0fd5`,
`eq:continuation-null-gauge`, lines 1390–1422. -/
theorem pullback_radius_out {S : SSFields} {T dT : ℝ → ℝ} {u a b : ℝ}
    (hT : GaugeSegment T dT a b)
    (h : IntervalPrimitive (S.r (T u)) (S.lam (T u)) (T a) (T b)) :
    IntervalPrimitive ((S.pullback T dT).r u) ((S.pullback T dT).lam u) a b :=
  h.comp hT

/-- Incoming radius equation in the pullback chart. Paper `e1a0fd5`,
`eq:continuation-null-gauge`, lines 1390–1422. -/
theorem pullback_radius_in {S : SSFields} {T dT : ℝ → ℝ} {v a b : ℝ}
    (hT : GaugeSegment T dT a b)
    (h : IntervalPrimitive (fun u => S.r u (T v)) (fun u => S.nu u (T v)) (T a) (T b)) :
    IntervalPrimitive (fun u => (S.pullback T dT).r u v)
      (fun u => (S.pullback T dT).nu u v) a b := h.comp hT

/-- Outgoing scalar primitive equation in the pullback chart. Paper `e1a0fd5`,
`eq:continuation-null-gauge`, lines 1390–1422. -/
theorem pullback_psi_out {S : SSFields} {T dT : ℝ → ℝ} {u a b : ℝ}
    (hT : GaugeSegment T dT a b)
    (h : IntervalPrimitive (fun v => S.r (T u) v * S.phi (T u) v)
      (S.dvpsi (T u)) (T a) (T b)) :
    IntervalPrimitive (fun v => (S.pullback T dT).r u v * (S.pullback T dT).phi u v)
      ((S.pullback T dT).dvpsi u) a b := h.comp hT

/-- Incoming scalar primitive equation in the pullback chart. Paper `e1a0fd5`,
`eq:continuation-null-gauge`, lines 1390–1422. -/
theorem pullback_psi_in {S : SSFields} {T dT : ℝ → ℝ} {v a b : ℝ}
    (hT : GaugeSegment T dT a b)
    (h : IntervalPrimitive (fun u => S.r u (T v) * S.phi u (T v))
      (fun u => S.dupsi u (T v)) (T a) (T b)) :
    IntervalPrimitive (fun u => (S.pullback T dT).r u v * (S.pullback T dT).phi u v)
      (fun u => (S.pullback T dT).dupsi u v) a b := h.comp hT

/-- Outgoing mass equation in the pullback chart. Paper `e1a0fd5`,
`eq:continuation-null-gauge`, lines 1390–1422. -/
theorem pullback_mass_out {S : SSFields} {T dT : ℝ → ℝ} {u a b : ℝ}
    (hT : GaugeSegment T dT a b) (hn : ∀ x ∈ uIcc a b, dT x ≠ 0)
    (h : IntervalPrimitive (S.m (T u)) (S.massV (T u)) (T a) (T b)) :
    IntervalPrimitive ((S.pullback T dT).m u) ((S.pullback T dT).massV u) a b := by
  apply (h.comp hT).congr (fun _ _ => rfl)
  intro x hx
  exact (pullback_massV S T dT u x (hn x hx)).symm

/-- Incoming mass equation in the pullback chart. Paper `e1a0fd5`,
`eq:continuation-null-gauge`, lines 1390–1422. -/
theorem pullback_mass_in {S : SSFields} {T dT : ℝ → ℝ} {v a b : ℝ}
    (hT : GaugeSegment T dT a b) (hn : ∀ x ∈ uIcc a b, dT x ≠ 0)
    (h : IntervalPrimitive (fun u => S.m u (T v)) (fun u => S.massU u (T v)) (T a) (T b)) :
    IntervalPrimitive (fun u => (S.pullback T dT).m u v)
      (fun u => (S.pullback T dT).massU u v) a b := by
  apply (h.comp hT).congr (fun _ _ => rfl)
  intro x hx
  exact (pullback_massU S T dT x v (hn x hx)).symm

/-- Transverse outgoing expansion equation. Paper `e1a0fd5`,
`eq:continuation-null-gauge`, lines 1390–1422. -/
theorem pullback_lam_in {S : SSFields} {T dT : ℝ → ℝ} {v a b : ℝ}
    (hT : GaugeSegment T dT a b)
    (h : IntervalPrimitive (fun u => S.lam u (T v))
      (fun u => S.radiusCoeff u (T v)) (T a) (T b)) :
    IntervalPrimitive (fun u => (S.pullback T dT).lam u v)
      (fun u => (S.pullback T dT).radiusCoeff u v) a b := by
  apply ((h.comp hT).mul_const (dT v)).congr (fun _ _ => rfl)
  intro x _
  dsimp only
  rw [pullback_radiusCoeff]
  ring

/-- Transverse incoming expansion equation. Paper `e1a0fd5`,
`eq:continuation-null-gauge`, lines 1390–1422. -/
theorem pullback_nu_out {S : SSFields} {T dT : ℝ → ℝ} {u a b : ℝ}
    (hT : GaugeSegment T dT a b)
    (h : IntervalPrimitive (S.nu (T u)) (S.radiusCoeff (T u)) (T a) (T b)) :
    IntervalPrimitive ((S.pullback T dT).nu u) ((S.pullback T dT).radiusCoeff u) a b := by
  apply ((h.comp hT).mul_const (dT u)).congr (fun _ _ => rfl)
  intro x _
  dsimp only
  rw [pullback_radiusCoeff]
  ring

/-- Transverse outgoing scalar derivative equation. Paper `e1a0fd5`,
`eq:continuation-null-gauge`, lines 1390–1422. -/
theorem pullback_dvpsi_in {S : SSFields} {T dT : ℝ → ℝ} {v a b : ℝ}
    (hT : GaugeSegment T dT a b)
    (h : IntervalPrimitive (fun u => S.dvpsi u (T v))
      (fun u => S.radiusCoeff u (T v) * S.phi u (T v)) (T a) (T b)) :
    IntervalPrimitive (fun u => (S.pullback T dT).dvpsi u v)
      (fun u => (S.pullback T dT).radiusCoeff u v * (S.pullback T dT).phi u v) a b := by
  apply ((h.comp hT).mul_const (dT v)).congr (fun _ _ => rfl)
  intro x _
  dsimp only
  rw [pullback_radiusCoeff]
  change _ = S.radiusCoeff (T x) (T v) * (dT x * dT v) * S.phi (T x) (T v)
  ring

/-- Transverse incoming scalar derivative equation. Paper `e1a0fd5`,
`eq:continuation-null-gauge`, lines 1390–1422. -/
theorem pullback_dupsi_out {S : SSFields} {T dT : ℝ → ℝ} {u a b : ℝ}
    (hT : GaugeSegment T dT a b)
    (h : IntervalPrimitive (S.dupsi (T u))
      (fun v => S.radiusCoeff (T u) v * S.phi (T u) v) (T a) (T b)) :
    IntervalPrimitive ((S.pullback T dT).dupsi u)
      (fun v => (S.pullback T dT).radiusCoeff u v * (S.pullback T dT).phi u v) a b := by
  apply ((h.comp hT).mul_const (dT u)).congr (fun _ _ => rfl)
  intro x _
  dsimp only
  rw [pullback_radiusCoeff]
  change _ = S.radiusCoeff (T u) (T x) * (dT u * dT x) * S.phi (T u) (T x)
  ring

end SSFields
end AcExtensionPrinciple

end
