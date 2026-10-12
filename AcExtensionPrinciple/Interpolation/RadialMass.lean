module

public import AcExtensionPrinciple.Interpolation.RadiusChart

/-!
# Radial mass in the inverse cone coordinate

Paper `e1a0fd5`, `eq:radial-mass` and
`eq:interpolation-mass-lower-bound`, equations.tex lines 647–656.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The mass is nonnegative, as follows from μ ≥ 0 and the axis value.
Paper `e1a0fd5`, `eq:interpolation-mass-lower-bound`, line 652. -/
theorem interpolation_mass_nonneg {u v : ℝ} (hp : (u, v) ∈ pastTriangle ui) :
    0 ≤ S.m u v := by
  rcases eq_or_lt_of_le hp.2.2.1 with he | he
  · change u = v at he
    rw [← he, (h.regularCenter.localBV.axis_values u
      ⟨hp.1, hp.2.1, le_rfl, hp.2.1.le⟩).2]
  · have hh := (h.mu_bounds hp).1
    change 0 ≤ 2 * S.m u v / S.r u v at hh
    have hr := h.r_pos hp he
    have hm := (le_div_iff₀ hr).mp hh
    linarith

/-- The radial mass equation gives a positive multiple of the radial
amplitude energy. The mass-gap premise is discharged by Lemma 1.1.
Paper `e1a0fd5`, `eq:radial-mass`, lines 647–656. -/
theorem radial_mass_lower_bound {u t r g : ℝ}
    (hu : ui ≤ u) (hu0 : u < 0) (ht : t ∈ Icc 0 (S.r u 0))
    (hr : r ∈ Icc 0 (S.r u 0)) (ht0 : 0 < t) (htr : t ≤ r)
    (hgap : ∀ p ∈ pastTriangle ui, g ≤ 1 - S.mu p.1 p.2) :
    (g / 2) * (∫ s in t..r,
      outgoingAmplitude S u (coneRadiusLabel S u s) ^ 2) ≤
      S.m u (coneRadiusLabel S u r) - S.m u (coneRadiusLabel S u t) := by
  let a := coneRadiusLabel S u t
  let b := coneRadiusLabel S u r
  have ha := h.coneRadiusLabel_spec hu hu0 ht
  have hb := h.coneRadiusLabel_spec hu hu0 hr
  have hab : a ≤ b := h.coneRadiusLabel_monotone hu hu0 ht hr htr
  have hua : u < a := h.coneRadiusLabel_offAxis hu hu0 ht ht0
  have hs := outSeg_subset_triangle hu hu0 ha.1.1 hb.1.2
  have hm := h.regularCenter.localBV.mass_out u a b hab hs
  have hA := (h.outgoingAmplitude_continuous_out hu hu0).mono
    (Icc_subset_Icc ha.1.1 hb.1.2)
  have hl := continuous_out h.regularCenter.continuous_lam hs
  have hi := ((hA.pow 2).mul hl).intervalIntegrable_of_Icc (μ := volume) hab
  have henergy : (∫ v in a..b, outgoingAmplitude S u v ^ 2 * S.lam u v) =
      ∫ s in t..r, outgoingAmplitude S u (coneRadiusLabel S u s) ^ 2 := by
    have he := h.cone_integral_radius_change
      (F := fun s => outgoingAmplitude S u (coneRadiusLabel S u s) ^ 2)
      hu hu0 ha.1 hb.1 hab
    rw [ha.2, hb.2] at he
    rw [← he]
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le hab] at hv
    dsimp only
    rw [h.coneRadiusLabel_radius hu hu0
      ⟨ha.1.1.trans hv.1, hv.2.trans hb.1.2⟩]
  rw [← henergy, hm.2, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on hab (hi.const_mul (g / 2)) hm.1
  intro v hv
  have hp : (u, v) ∈ pastTriangle ui :=
    ⟨hu, hu0, (hua.trans_le hv.1).le, hv.2.trans hb.1.2⟩
  have hl0 := h.lam_pos hp
  have heq : S.massV u v = ((1 - S.mu u v) / 2) *
      (outgoingAmplitude S u v ^ 2 * S.lam u v) := by
    dsimp [SSFields.massV, outgoingAmplitude]
    field_simp
  rw [heq]
  exact mul_le_mul_of_nonneg_right (by linarith [hgap (u, v) hp])
    (mul_nonneg (sq_nonneg _) hl0.le)

end StandingFull

end AcExtensionPrinciple

end
