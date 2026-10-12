module

public import AcExtensionPrinciple.Renormalized.ClassRadiusCoordinate
public import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Hardy's inequality on the actual outgoing cone

Paper `e1a0fd5`, `equations.tex` lines 1006–1015.
The radius profile is constructed, and its lower integral is pulled back
through the differentiable strictly increasing radius coordinate.
-/

public section

namespace AcExtensionPrinciple.StandingFull

open Set Filter MeasureTheory
open scoped Topology ENNReal

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Radius has its prescribed derivative at every interior cone point.
Paper `e1a0fd5`, `eq:radius`, lines 1006–1015. -/
theorem cone_radius_hasDerivAt {u v : ℝ} (hu : ui ≤ u) (hu0 : u < 0)
    (hv : v ∈ Ioo u 0) : HasDerivAt (S.r u) (S.lam u v) v := by
  apply intervalPrimitive_hasDerivAt hv
    (continuous_out h.regularCenter.continuous_lam (outSeg_subset_triangle hu hu0 le_rfl le_rfl))
  intro x hx
  exact h.regularCenter.localBV.radius_out u u x hx.1
    (outSeg_subset_triangle hu hu0 le_rfl hx.2)

/-- Exact lower-integral change of variables on a proper cone, including
the terminal endpoint by null-singleton equivalence. Paper `e1a0fd5`,
lines 1006–1015, `dr = λ dv`. -/
theorem cone_lintegral_radius_change {u : ℝ} (hu : ui ≤ u) (hu0 : u < 0)
    (F : ℝ → ℝ≥0∞) :
    (∫⁻ ρ in Ioc 0 (S.r u 0), F ρ) =
      ∫⁻ v in Ioc u 0, ENNReal.ofReal (S.lam u v) * F (S.r u v) := by
  have hc := continuous_out h.regularCenter.continuous_r
    (outSeg_subset_triangle hu hu0 le_rfl le_rfl)
  have himage := hc.image_Ioo_of_strictMonoOn hu0.le (h.cone_radius_strictMono hu hu0)
  rw [(h.regularCenter.localBV.axis_values u ⟨hu, hu0, le_rfl, hu0.le⟩).1] at himage
  have he := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo
    (fun v hv => (h.cone_radius_hasDerivAt hu hu0 hv).hasDerivWithinAt)
    ((h.cone_radius_strictMono hu hu0).injOn.mono Ioo_subset_Icc_self) F
  rw [himage] at he
  simp only [restrict_Ioo_eq_restrict_Ioc] at he
  rw [he]
  apply setLIntegral_congr_fun measurableSet_Ioc
  intro v hv
  dsimp only
  rw [abs_of_pos (h.lam_pos (p := (u, v)) ⟨hu, hu0, hv.1.le, hv.2⟩)]

/-- The scalar primitive in the constructed radius coordinate has only
the outgoing AC conclusion of Lemma 2.2 as input.
Paper `e1a0fd5`, `eq:scalar-radial-primitive`, lines 1006–1009. -/
theorem scalar_radial_primitive_of_ac_datum {u v : ℝ}
    (hu : ui ≤ u) (hu0 : u < 0) (huv : u < v) (hv0 : v ≤ 0)
    (hP : AbsolutelyContinuousOnInterval (S.outgoingDatum u) u 0) :
    S.r u v / S.lam u v * S.dvphi u v =
      (1 / S.r u v) * ∫ ρ in 0..S.r u v, ρ * deriv (S.coneRadiusProfile u) ρ :=
  h.scalar_radial_primitive_of_radius_profile hu hu0 huv hv0
    (h.coneRadiusProfile_ac_of_ac_datum hu hu0 hP)
    (fun v hv => h.coneRadiusProfile_radius (v := v) hu hu0 hv)

/-- The scalar radial Hardy inequality on the original v-coordinate cone.
Paper `e1a0fd5`, `eq:scalar-radial-hardy`, lines 1010–1015.
The only input beyond the class is Lemma 2.2's outgoing AC conclusion. -/
theorem scalar_cone_hardy_of_ac_datum {u : ℝ} (hu : ui ≤ u) (hu0 : u < 0)
    (hP : AbsolutelyContinuousOnInterval (S.outgoingDatum u) u 0) :
    (∫⁻ v in Ioc u 0,
      ENNReal.ofReal (S.lam u v * |S.r u v / S.lam u v * S.dvphi u v| / S.r u v)) ≤
        S.outgoingVariation u := by
  have hprofile := h.coneRadiusProfile_ac_of_ac_datum hu hu0 hP
  have hh := h.scalar_radial_hardy_of_radius_profile hu hu0 hprofile
    (fun v hv => h.coneRadiusProfile_radius hu hu0 hv)
  rw [h.cone_lintegral_radius_change hu hu0] at hh
  calc
    _ = ∫⁻ v in Ioc u 0, ENNReal.ofReal (S.lam u v) *
        ENNReal.ofReal (|S.coneRadiusProfile u (S.r u v) -
          (1 / S.r u v) * (∫ ρ in 0..S.r u v, S.coneRadiusProfile u ρ)| / S.r u v) := by
      apply setLIntegral_congr_fun measurableSet_Ioc
      intro v hv
      dsimp only
      have hp : (u, v) ∈ pastTriangle ui := ⟨hu, hu0, hv.1.le, hv.2⟩
      rw [h.coneRadiusProfile_radius hu hu0 ⟨hv.1.le, hv.2⟩,
        ← h.scalar_average_of_radius_profile hu hu0 hv.1 hv.2 hprofile
          (fun v hv => h.coneRadiusProfile_radius hu hu0 hv),
        ← h.outgoing_amplitude_eq hp hv.1,
        ← ENNReal.ofReal_mul (h.lam_pos hp).le]
      congr 1
      ring
    _ ≤ _ := hh

end AcExtensionPrinciple.StandingFull

end
