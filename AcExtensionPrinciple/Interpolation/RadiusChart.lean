module

public import AcExtensionPrinciple.Interpolation.ConeCalculus
public import AcExtensionPrinciple.Cylinder.Curve
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Radius coordinates on a closed outgoing cone

Paper `e1a0fd5`, `lem:ac-interpolation`, `equations.tex` lines 618–659.
The inverse radius coordinate is Lipschitz by the uniform positive λ bound.
Change of variables is valid up to the axis and the terminal incoming ray.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- Incoming label of the point with prescribed radius on a fixed cone.
Paper `e1a0fd5`, radius parametrization at line 619. -/
@[expose] noncomputable def coneRadiusLabel (S : SSFields) (u t : ℝ) : ℝ :=
  Function.invFunOn (S.r u) (Icc u 0) t

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The inverse radius belongs to the cone and has exactly the requested
radius. Paper `e1a0fd5`, radius parametrization at line 619. -/
theorem coneRadiusLabel_spec {u t : ℝ} (hu : ui ≤ u) (hu0 : u < 0)
    (ht : t ∈ Icc 0 (S.r u 0)) :
    coneRadiusLabel S u t ∈ Icc u 0 ∧ S.r u (coneRadiusLabel S u t) = t := by
  have hc := continuous_out h.regularCenter.continuous_r
    (outSeg_subset_triangle hu hu0 le_rfl le_rfl)
  have hr0 := (h.regularCenter.localBV.axis_values u
    ⟨hu, hu0, le_rfl, hu0.le⟩).1
  have hex : ∃ v ∈ Icc u 0, S.r u v = t :=
    intermediate_value_Icc hu0.le hc (by simpa only [hr0] using ht)
  exact ⟨Function.invFunOn_mem hex, Function.invFunOn_eq hex⟩

/-- The inverse radius returns each original incoming label. Paper `e1a0fd5`,
change of variables dr = λ dv at lines 627 and 647–656. -/
theorem coneRadiusLabel_radius {u v : ℝ} (hu : ui ≤ u) (hu0 : u < 0)
    (hv : v ∈ Icc u 0) : coneRadiusLabel S u (S.r u v) = v :=
  (h.radius_strictMono hu hu0).injOn.leftInvOn_invFunOn hv

/-- Positive radius corresponds to a point strictly above the axis.
Paper `e1a0fd5`, annular radius parametrization at lines 627–633. -/
theorem coneRadiusLabel_offAxis {u t : ℝ} (hu : ui ≤ u) (hu0 : u < 0)
    (ht : t ∈ Icc 0 (S.r u 0)) (ht0 : 0 < t) : u < coneRadiusLabel S u t := by
  have hs := h.coneRadiusLabel_spec hu hu0 ht
  apply lt_of_le_of_ne hs.1.1
  intro he
  have hr0 := (h.regularCenter.localBV.axis_values u
    ⟨hu, hu0, le_rfl, hu0.le⟩).1
  rw [← he, hr0] at hs
  linarith [hs.2]

/-- The inverse radius is monotone on the full closed radial interval.
Paper `e1a0fd5`, lines 619 and 627–633. -/
theorem coneRadiusLabel_monotone {u : ℝ} (hu : ui ≤ u) (hu0 : u < 0) :
    MonotoneOn (coneRadiusLabel S u) (Icc 0 (S.r u 0)) := by
  intro t ht s hs hts
  have ht' := h.coneRadiusLabel_spec hu hu0 ht
  have hs' := h.coneRadiusLabel_spec hu hu0 hs
  by_contra hn
  have hh := h.radius_strictMono hu hu0 hs'.1 ht'.1 (lt_of_not_ge hn)
  rw [ht'.2, hs'.2] at hh
  exact (not_lt_of_ge hts) hh

/-- The outgoing geometric bound quantitatively separates radial labels.
Paper `e1a0fd5`, Lemma 1.1 λ bounds, used in line 619. -/
theorem coordinate_gap_le_radius_gap {u a b : ℝ} (hu : ui ≤ u) (hu0 : u < 0)
    (ha : a ∈ Icc u 0) (hb : b ∈ Icc u 0) (hab : a ≤ b) :
    b - a ≤ Real.exp (Bstar ui S) * (S.r u b - S.r u a) := by
  have hs := outSeg_subset_triangle hu hu0 ha.1 hb.2
  have he := h.regularCenter.localBV.radius_out u a b hab hs
  have hlo : Real.exp (-Bstar ui S) * (b - a) ≤ S.r u b - S.r u a := by
    rw [he.2]
    calc
      _ = ∫ _v in a..b, Real.exp (-Bstar ui S) := by simp [mul_comm]
      _ ≤ _ := intervalIntegral.integral_mono_on hab intervalIntegrable_const he.1
        (fun v hv => (h.lam_bounds (p := (u, v))
          ⟨hu, hu0, ha.1.trans hv.1, hv.2.trans hb.2⟩).1)
  have hh := mul_le_mul_of_nonneg_left hlo (Real.exp_pos (Bstar ui S)).le
  simpa only [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] using hh

/-- The inverse radius is Lipschitz with the geometric constant exp(B*).
Paper `e1a0fd5`, line 619 and dr = λ dv at line 627. -/
theorem coneRadiusLabel_lipschitz {u : ℝ} (hu : ui ≤ u) (hu0 : u < 0) :
    LipschitzOnWith ⟨Real.exp (Bstar ui S), (Real.exp_pos _).le⟩
      (coneRadiusLabel S u) (Icc 0 (S.r u 0)) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro t ht s hs
  change dist (coneRadiusLabel S u t) (coneRadiusLabel S u s) ≤
    Real.exp (Bstar ui S) * dist t s
  have ht' := h.coneRadiusLabel_spec hu hu0 ht
  have hs' := h.coneRadiusLabel_spec hu hu0 hs
  have hm := h.coneRadiusLabel_monotone hu hu0
  rcases le_total t s with hts | hst
  · have hh := h.coordinate_gap_le_radius_gap hu hu0 ht'.1 hs'.1 (hm ht hs hts)
    rw [ht'.2, hs'.2] at hh
    simpa only [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (hm ht hs hts)),
      abs_of_nonpos (sub_nonpos.mpr hts), neg_sub, NNReal.coe_mk] using hh
  · have hh := h.coordinate_gap_le_radius_gap hu hu0 hs'.1 ht'.1 (hm hs ht hst)
    rw [ht'.2, hs'.2] at hh
    simpa only [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (hm hs ht hst)),
      abs_of_nonneg (sub_nonneg.mpr hst), NNReal.coe_mk] using hh

/-- Continuous radial amplitude on the closed cone. Paper `e1a0fd5`,
`eq:radial-amplitude-oscillation`, lines 627–633. -/
theorem outgoingAmplitude_continuous_out {u : ℝ} (hu : ui ≤ u) (hu0 : u < 0) :
    ContinuousOn (outgoingAmplitude S u) (Icc u 0) := by
  have hf := continuous_out h.regularCenter.continuous_phi
    (outSeg_subset_triangle hu hu0 le_rfl le_rfl)
  apply ((h.normalized_datum_continuous_out hu hu0).sub hf).congr
  intro v hv
  exact (outgoingAmplitude_eq S
    (h.lam_pos (p := (u, v)) ⟨hu, hu0, hv⟩).ne')

/-- Radial integration of a continuous cone quantity agrees with weighted
coordinate integration. Paper `e1a0fd5`, dr = λ dv, lines 627 and 647–656. -/
theorem cone_integral_radius_change {u a b : ℝ} {F : ℝ → ℝ}
    (hu : ui ≤ u) (hu0 : u < 0) (ha : a ∈ Icc u 0) (hb : b ∈ Icc u 0)
    (hab : a ≤ b) :
    (∫ v in a..b, F (S.r u v) * S.lam u v) = ∫ t in S.r u a..S.r u b, F t := by
  have hc := continuous_out h.regularCenter.continuous_r
    (outSeg_subset_triangle hu hu0 ha.1 hb.2)
  apply intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (by simpa only [uIcc_of_le hab] using hc)
  · intro v hv
    rw [min_eq_left hab, max_eq_right hab] at hv
    exact h.acdatum_radius_hasDerivAt_out hu hu0 (ha.1.trans_lt hv.1) (hv.2.trans_le hb.2)
  · intro v hv
    rw [min_eq_left hab, max_eq_right hab] at hv
    exact (h.lam_pos (p := (u, v))
      ⟨hu, hu0, (ha.1.trans_lt hv.1).le, hv.2.le.trans hb.2⟩).le

end StandingFull

end AcExtensionPrinciple

end
