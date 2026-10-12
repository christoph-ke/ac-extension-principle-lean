module

public import AcExtensionPrinciple.Renormalized.ClassCalculus
public import AcExtensionPrinciple.Analysis.HardyVariation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Scalar primitive and Hardy estimate on outgoing cones

Paper `e1a0fd5`, `equations.tex` lines 1006–1015.
The pulled-back primitive is proved directly from class primitives.
The radius-profile helpers expose the precise change-of-variable interface.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Radius is strictly increasing on every proper outgoing cone.
Paper `e1a0fd5`, `eq:radius-from-axis`, lines 1006–1015. -/
theorem cone_radius_strictMono {u : ℝ} (hu : ui ≤ u) (hu0 : u < 0) :
    StrictMonoOn (S.r u) (Icc u 0) := by
  intro a ha b hb hab
  have hs := outSeg_subset_triangle hu hu0 ha.1 hb.2
  obtain ⟨c, hc, he⟩ := h.regularCenter.localBV.expansion_bounds (outSeg u a b)
    (isCompact_singleton.prod isCompact_Icc) hs
  have hi := h.regularCenter.localBV.radius_out u a b hab.le hs
  have hbound : c * (b - a) ≤ S.r u b - S.r u a := by
    rw [hi.2]
    calc
      _ = ∫ _s in a..b, c := by simp [mul_comm]
      _ ≤ _ := intervalIntegral.integral_mono_on hab.le intervalIntegrable_const hi.1
        (fun s hs => (he (u, s) ⟨rfl, hs⟩).1)
  exact sub_pos.mp ((mul_pos hc (sub_pos.mpr hab)).trans_le hbound)

/-- Radius maps a proper cone onto `[0,r(u,0)]`.
Paper `e1a0fd5`, lines 1006–1015, change of integration variable. -/
theorem cone_radius_image {u : ℝ} (hu : ui ≤ u) (hu0 : u < 0) :
    S.r u '' Icc u 0 = Icc 0 (S.r u 0) := by
  have hc := continuous_out h.regularCenter.continuous_r
    (outSeg_subset_triangle hu hu0 le_rfl le_rfl)
  rw [hc.image_Icc_of_monotoneOn hu0.le (h.cone_radius_strictMono hu hu0).monotoneOn]
  rw [(h.regularCenter.localBV.axis_values u ⟨hu, hu0, le_rfl, hu0.le⟩).1]

/-- The regular-center scalar primitive, pulled back by `dr = λ dv`.
Paper `e1a0fd5`, `eq:scalar-radial-primitive`, lines 1006–1009.
The AC premise is the Lemma 2.2 conclusion for this cone. -/
theorem scalar_cone_primitive_of_ac_datum {u v : ℝ}
    (hu : ui ≤ u) (hu0 : u < 0) (huv : u < v) (hv0 : v ≤ 0)
    (hP : AbsolutelyContinuousOnInterval (S.outgoingDatum u) u v) :
    S.r u v / S.lam u v * S.dvphi u v =
      (1 / S.r u v) * ∫ s in u..v,
        S.r u s * (S.lam u s * S.radialDatumDerivative u s) := by
  have hs := outSeg_subset_triangle hu hu0 le_rfl hv0
  have hr := intervalPrimitive_ac huv.le
    (fun x hx => h.regularCenter.localBV.radius_out u u x hx.1
      (outSeg_subset_triangle hu hu0 le_rfl (hx.2.trans hv0)))
  have hrd := intervalPrimitive_ae_hasDerivAt huv.le
    (fun x hx => h.regularCenter.localBV.radius_out u u x hx.1
      (outSeg_subset_triangle hu hu0 le_rfl (hx.2.trans hv0)))
  have he : (∫ s in u..v, deriv (S.r u) s * S.outgoingDatum u s) =
      ∫ s in u..v, S.dvpsi u s := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hrd, show ∀ᵐ s : ℝ, s ≠ v by simp [ae_iff]] with s hs' hsv hmem
    rw [uIoc_of_le huv.le] at hmem
    rw [(hs' ⟨hmem.1, lt_of_le_of_ne hmem.2 hsv⟩).deriv]
    dsimp [SSFields.outgoingDatum]
    exact mul_div_cancel₀ _ (ne_of_gt (h.lam_pos (p := (u, s))
      ⟨hu, hu0, hmem.1.le, hmem.2.trans hv0⟩))
  have hψ := (h.regularCenter.localBV.psi_out u u v huv.le hs).2
  have haxis := (h.regularCenter.localBV.axis_values u ⟨hu, hu0, le_rfl, hu0.le⟩).1
  have hibp := hr.integral_mul_deriv_eq_deriv_mul hP
  rw [he, ← hψ] at hibp
  dsimp only at hibp
  simp only [haxis, zero_mul, sub_zero] at hibp
  have hq : (∫ s in u..v, S.r u s * (S.lam u s * S.radialDatumDerivative u s)) =
      ∫ s in u..v, S.r u s * deriv (S.outgoingDatum u) s := by
    apply intervalIntegral.integral_congr
    intro s hs'
    rw [uIcc_of_le huv.le] at hs'
    dsimp [SSFields.radialDatumDerivative]
    rw [mul_div_cancel₀ _ (ne_of_gt (h.lam_pos (p := (u, s))
      ⟨hu, hu0, hs'.1, hs'.2.trans hv0⟩))]
  rw [hq, hibp, h.outgoing_amplitude_eq ⟨hu, hu0, huv.le, hv0⟩ huv]
  field_simp [ne_of_gt (h.r_pos ⟨hu, hu0, huv.le, hv0⟩ huv)]

/-- Total variation is unchanged by the strictly increasing radius coordinate.
Paper `e1a0fd5`, `eq:scalar-radial-hardy`, lines 1006–1015.
The profile equation says precisely that `P` is the datum in radius coordinates. -/
theorem radial_profile_variation {P : ℝ → ℝ} {u : ℝ} (hu : ui ≤ u) (hu0 : u < 0)
    (hprofile : ∀ v ∈ Icc u 0, P (S.r u v) = S.outgoingDatum u v) :
    eVariationOn P (Icc 0 (S.r u 0)) = S.outgoingVariation u := by
  rw [← h.cone_radius_image hu hu0,
    ← eVariationOn.comp_eq_of_monotoneOn P (S.r u) (h.cone_radius_strictMono hu hu0).monotoneOn]
  exact eVariationOn.congr hprofile

/-- Change of variables `dr = λ dv` identifies the radius-profile average
with the scalar field. Paper `e1a0fd5`, `eq:scalar-radial-primitive`,
lines 1006–1009, using the regular-center scalar primitive. -/
theorem scalar_average_of_radius_profile {P : ℝ → ℝ} {u v : ℝ}
    (hu : ui ≤ u) (hu0 : u < 0) (huv : u < v) (hv0 : v ≤ 0)
    (hP : AbsolutelyContinuousOnInterval P 0 (S.r u 0))
    (hprofile : ∀ s ∈ Icc u 0, P (S.r u s) = S.outgoingDatum u s) :
    S.phi u v = (1 / S.r u v) * ∫ ρ in 0..S.r u v, P ρ := by
  have hs := outSeg_subset_triangle hu hu0 le_rfl hv0
  have hc := continuous_out h.regularCenter.continuous_r hs
  have hl := continuous_out h.regularCenter.continuous_lam hs
  have haxis := (h.regularCenter.localBV.axis_values u ⟨hu, hu0, le_rfl, hu0.le⟩).1
  have hmono := (h.cone_radius_strictMono hu hu0).monotoneOn
  have hR := h.r_pos (u := u) (v := 0) ⟨hu, hu0, hu0.le, le_rfl⟩ hu0
  have hsub : S.r u '' uIcc u v ⊆ uIcc 0 (S.r u 0) := by
    rw [uIcc_of_le huv.le, uIcc_of_le hR.le]
    rintro _ ⟨s, hs', rfl⟩
    have hs0 : s ∈ Icc u 0 := ⟨hs'.1, hs'.2.trans hv0⟩
    exact ⟨by rw [← haxis]; exact hmono ⟨le_rfl, hu0.le⟩ hs0 hs'.1,
      hmono hs0 ⟨hu0.le, le_rfl⟩ hs0.2⟩
  have hchange := intervalIntegral.integral_comp_mul_deriv''
    (by simpa only [uIcc_of_le huv.le] using hc)
    (fun s hs' => (intervalPrimitive_hasDerivAt
      (by simpa only [min_eq_left huv.le, max_eq_right huv.le] using hs') hl
      (fun x hx => h.regularCenter.localBV.radius_out u u x hx.1
        (outSeg_subset_triangle hu hu0 le_rfl (hx.2.trans hv0)))).hasDerivWithinAt)
    (by simpa only [uIcc_of_le huv.le] using hl) (hP.continuousOn.mono hsub)
  change (∫ s in u..v, P (S.r u s) * S.lam u s) = ∫ ρ in S.r u u..S.r u v, P ρ at hchange
  have hψ := (h.regularCenter.localBV.psi_out u u v huv.le hs).2
  have hi : (∫ s in u..v, S.dvpsi u s) =
      ∫ s in u..v, P (S.r u s) * S.lam u s := by
    apply intervalIntegral.integral_congr
    intro s hs'
    rw [uIcc_of_le huv.le] at hs'
    change S.dvpsi u s = P (S.r u s) * S.lam u s
    rw [hprofile s ⟨hs'.1, hs'.2.trans hv0⟩]
    dsimp [SSFields.outgoingDatum]
    exact (div_mul_cancel₀ _ (ne_of_gt (h.lam_pos (p := (u, s))
      ⟨hu, hu0, hs'.1, hs'.2.trans hv0⟩))).symm
  rw [hi, hchange, haxis] at hψ
  dsimp only at hψ
  simp only [haxis, zero_mul, sub_zero] at hψ
  rw [← hψ]
  field_simp [ne_of_gt (h.r_pos ⟨hu, hu0, huv.le, hv0⟩ huv)]

/-- The scalar radial primitive in actual radius coordinates.
Paper `e1a0fd5`, `eq:scalar-radial-primitive`, lines 1006–1009.
The radial derivative `q` is `deriv P` for the radius profile. -/
theorem scalar_radial_primitive_of_radius_profile {P : ℝ → ℝ} {u v : ℝ}
    (hu : ui ≤ u) (hu0 : u < 0) (huv : u < v) (hv0 : v ≤ 0)
    (hP : AbsolutelyContinuousOnInterval P 0 (S.r u 0))
    (hprofile : ∀ s ∈ Icc u 0, P (S.r u s) = S.outgoingDatum u s) :
    S.r u v / S.lam u v * S.dvphi u v =
      (1 / S.r u v) * ∫ ρ in 0..S.r u v, ρ * deriv P ρ := by
  rw [h.outgoing_amplitude_eq ⟨hu, hu0, huv.le, hv0⟩ huv,
    h.scalar_average_of_radius_profile hu hu0 huv hv0 hP hprofile,
    ← hprofile v ⟨huv.le, hv0⟩]
  exact radial_primitive_eq hP (h.r_pos ⟨hu, hu0, huv.le, hv0⟩ huv)
    ((h.cone_radius_strictMono hu hu0).monotoneOn ⟨huv.le, hv0⟩ ⟨hu0.le, le_rfl⟩ hv0)

/-- Applying the radial Hardy lemma after changing variables to radius gives
the cone's variation bound. Paper `e1a0fd5`, `eq:scalar-radial-hardy`,
lines 1010–1015. AC of the radius profile follows from cone datum AC and the
bi-Lipschitz radius coordinate; that calculus conversion is explicit here. -/
theorem scalar_radial_hardy_of_radius_profile {P : ℝ → ℝ} {u : ℝ}
    (hu : ui ≤ u) (hu0 : u < 0)
    (hP : AbsolutelyContinuousOnInterval P 0 (S.r u 0))
    (hprofile : ∀ v ∈ Icc u 0, P (S.r u v) = S.outgoingDatum u v) :
    (∫⁻ ρ in Ioc 0 (S.r u 0),
      ENNReal.ofReal (|P ρ - (1 / ρ) * (∫ σ in 0..ρ, P σ)| / ρ)) ≤
        S.outgoingVariation u := by
  rw [← h.radial_profile_variation hu hu0 hprofile]
  exact radial_hardy_le_eVariationOn (h.r_pos ⟨hu, hu0, hu0.le, le_rfl⟩ hu0) hP

end StandingFull

end AcExtensionPrinciple

end
