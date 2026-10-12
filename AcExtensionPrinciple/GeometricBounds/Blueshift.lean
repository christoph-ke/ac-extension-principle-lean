module

public import AcExtensionPrinciple.GeometricBounds.RayBounds

/-!
# Explicit bounds from incoming blueshift

Paper `e1a0fd5`, `eq:lambda-integrating-factor`,
`eq:lambda-kappa-bounds`, `eq:mass-gap-and-nu-bound`, `eq:radius-comparison`
(lines 289–299 and 311–349). These bounds do not use the initial-gap constant.

Docstrings in this library name the conclusions of Lemma 1.1 (`lem:geometric-bounds`, lines 281–307)
as follows: G0 the positive initial gap `c_i > 0` (`eq:initial-gap-and-expansion-bound`); G1 the
bounds `e^{-B_*} ≤ λ ≤ 1`; G2 the κ bounds and the gap from `μ = 1` (`eq:kappa-monotonicity-bound`);
G3 the bound `-ν ≥ e^{-B_*}`; G4 the radius comparison (`eq:radius-comparison`); G5 the terminal
blueshift bound (`eq:terminal-blueshift-bound`); G6 the incoming scalar flux bound
(`eq:incoming-flux-bound`).
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- Nonnegative interval integrals agree with their lower integrals on the open interval.
Paper `e1a0fd5`, `eq:uniform-blueshift`, `eq:lambda-integrating-factor`. -/
theorem ofReal_intervalIntegral {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hi : IntervalIntegrable f volume a b) (hn : ∀ x ∈ Ioo a b, 0 ≤ f x) :
    ENNReal.ofReal (∫ x in a..b, f x) = ∫⁻ x in Ioo a b, ENNReal.ofReal (f x) := by
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]
  exact ofReal_integral_eq_lintegral_ofReal
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mp hi)
    ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall hn))

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Any truncated incoming blueshift integral is bounded by the real supremum.
Paper `e1a0fd5`, `eq:uniform-blueshift`, lines 311–316. -/
theorem partial_blueshift_le {u v : ℝ} (huiu : ui ≤ u) (huv : u < v) (hv : v ∈ Ioo ui 0)
    (hi : IntervalIntegrable (fun s => -(S.gamma s v * S.varkappa s v)) volume ui u) :
    (∫ s in ui..u, -(S.gamma s v * S.varkappa s v)) ≤ Bstar ui S := by
  have hn : ∀ s ∈ Ioo ui u, 0 ≤ -(S.gamma s v * S.varkappa s v) := by
    intro s hs
    exact h.blueshift_nonneg ⟨hs.1.le, hs.2.trans (huv.trans hv.2),
      (hs.2.trans huv).le, hv.2.le⟩ (hs.2.trans huv)
  have hbound : ENNReal.ofReal (∫ s in ui..u, -(S.gamma s v * S.varkappa s v)) ≤
      blueshiftSup ui S := by
    rw [ofReal_intervalIntegral huiu hi hn]
    exact (lintegral_mono_set (Ioo_subset_Ioo_right huv.le)).trans
      (le_iSup_of_le v (le_iSup_of_le hv le_rfl))
  exact (ENNReal.ofReal_le_iff_le_toReal h.blueshift_finite.ne).mp hbound

/-- The incoming integrating factor and both λ bounds on strictly interior outgoing rays.
Paper `e1a0fd5`, `eq:lambda-integrating-factor`, `eq:lambda-kappa-bounds`. -/
theorem lam_bounds_interior {u v : ℝ} (huiu : ui ≤ u) (huv : u < v) (hv0 : v < 0) :
    Real.exp (-Bstar ui S) ≤ S.lam u v ∧ S.lam u v ≤ 1 := by
  have hv : v ∈ Ioo ui 0 := ⟨huiu.trans_lt huv, hv0⟩
  have hp : (u, v) ∈ pastTriangle ui := ⟨huiu, huv.trans hv0, huv.le, hv0.le⟩
  have hl := h.log_lam_primitive huiu le_rfl hp.2.1 huv hv0.le
  have hinit := (h.initial_gauge v ⟨hv.1.le, hv.2.le⟩).2
  have he : Real.log (S.lam u v) =
      -(∫ s in ui..u, -(S.gamma s v * S.varkappa s v)) := by
    have ht := hl.2
    dsimp only at ht
    rw [hinit, Real.log_one, sub_zero] at ht
    rw [intervalIntegral.integral_neg]
    linarith
  have hb := h.partial_blueshift_le huiu huv hv hl.1.neg
  have hn : 0 ≤ ∫ s in ui..u, -(S.gamma s v * S.varkappa s v) := by
    apply intervalIntegral.integral_nonneg huiu
    intro s hs
    exact h.blueshift_nonneg ⟨hs.1, hs.2.trans_lt hp.2.1,
      (hs.2.trans_lt huv).le, hv0.le⟩ (hs.2.trans_lt huv)
  have hlog : -Bstar ui S ≤ Real.log (S.lam u v) ∧ Real.log (S.lam u v) ≤ 0 := by
    rw [he]
    constructor <;> linarith
  constructor
  · calc
      Real.exp (-Bstar ui S) ≤ Real.exp (Real.log (S.lam u v)) := Real.exp_le_exp.mpr hlog.1
      _ = S.lam u v := Real.exp_log (h.lam_pos hp)
  · calc
      S.lam u v = Real.exp (Real.log (S.lam u v)) := (Real.exp_log (h.lam_pos hp)).symm
      _ ≤ Real.exp 0 := Real.exp_le_exp.mpr hlog.2
      _ = 1 := Real.exp_zero

/-- G1: explicit uniform bounds for λ, including the axis and terminal ray.
Paper `e1a0fd5`, `eq:lambda-kappa-bounds`, lines 289–299, 311–316, 352. -/
theorem lam_bounds {p : ℝ × ℝ} (hp : p ∈ pastTriangle ui) :
    Real.exp (-Bstar ui S) ≤ S.lam p.1 p.2 ∧ S.lam p.1 p.2 ≤ 1 := by
  have hc := continuous_out h.regularCenter.continuous_lam
    (outSeg_subset_triangle hp.1 hp.2.1 le_rfl le_rfl)
  exact interval_bounds_of_open hp.2.1 hc
    (fun v hv => h.lam_bounds_interior hp.1 hv.1 hv.2) p.2 ⟨hp.2.2.1, hp.2.2.2⟩

/-- G3: the incoming expansion is uniformly bounded away from zero.
Paper `e1a0fd5`, `eq:mass-gap-and-nu-bound`, lines 342–346. -/
theorem neg_nu_lower {p : ℝ × ℝ} (hp : p ∈ pastTriangle ui) :
    Real.exp (-Bstar ui S) ≤ -S.nu p.1 p.2 := by
  have ha : (p.1, p.1) ∈ axis ui := ⟨hp.1, hp.2.1, rfl⟩
  have hb := (h.lam_bounds (axis_subset_pastTriangle ui ha)).1
  have hn := h.nu_le_axis hp
  have he := h.regularCenter.axis_expansions p.1 ha
  linarith

/-- G4: radius comparison with the explicit blueshift constant.
Paper `e1a0fd5`, `eq:radius-comparison`, `eq:radius-from-axis`, lines 347–349. -/
theorem radius_bounds {p : ℝ × ℝ} (hp : p ∈ pastTriangle ui) :
    Real.exp (-Bstar ui S) * (p.2 - p.1) ≤ S.r p.1 p.2 ∧ S.r p.1 p.2 ≤ p.2 - p.1 := by
  have hs := outSeg_subset_triangle hp.1 hp.2.1 le_rfl hp.2.2.2
  have hi := (h.regularCenter.localBV.radius_out p.1 p.1 p.2 hp.2.2.1 hs).1
  have hb : ∀ s ∈ Icc p.1 p.2,
      Real.exp (-Bstar ui S) ≤ S.lam p.1 s ∧ S.lam p.1 s ≤ 1 := by
    intro s hs'
    exact h.lam_bounds (p := (p.1, s)) (hs ⟨by simp, hs'⟩)
  rw [h.radius_from_axis hp]
  constructor
  · calc
      _ = ∫ s in p.1..p.2, Real.exp (-Bstar ui S) := by simp [mul_comm]
      _ ≤ _ := intervalIntegral.integral_mono_on hp.2.2.1 intervalIntegrable_const hi
        (fun s hs' => (hb s hs').1)
  · calc
      _ ≤ ∫ s in p.1..p.2, (1 : ℝ) :=
        intervalIntegral.integral_mono_on hp.2.2.1 hi intervalIntegrable_const
          (fun s hs' => (hb s hs').2)
      _ = _ := by simp

end StandingFull

end AcExtensionPrinciple

end
