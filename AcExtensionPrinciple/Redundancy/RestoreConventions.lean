module

public import AcExtensionPrinciple.Redundancy.ConventionRest

/-!
# Reinsert only the deleted hypothesis after proving it
Paper commit `e1a0fd5`, `equations.tex` lines 114–132 and 220–275.
Under ruling Q1, each deletion retains every other standing assumption.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- Restore the standing class using an explicit proof of the deleted `lam_right_cont` field. Paper
`e1a0fd5`, lines 114–132 and 220–275, `eq:regular-axis`, `eq:regular-axis-scalar-traces`. -/
theorem StandingWithout_lam_right_cont.restore {ui : ℝ} {S : SSFields}
    (h : StandingWithout_lam_right_cont ui S) (hx : ∀ p ∈ pastTriangle ui,
      ContinuousWithinAt (S.lam p.1) {w | p.2 ≤ w ∧ (p.1, w) ∈ pastTriangle ui} p.2) :
    StandingFull ui S := {
  initial_negative := h.initial_negative
  regularCenter := {
    localBV := {
      radius_out := h.regularCenter.localBV.radius_out
      radius_in := h.regularCenter.localBV.radius_in
      psi_out := h.regularCenter.localBV.psi_out
      psi_in := h.regularCenter.localBV.psi_in
      mass_out := h.regularCenter.localBV.mass_out
      mass_in := h.regularCenter.localBV.mass_in
      lam_in := h.regularCenter.localBV.lam_in
      nu_out := h.regularCenter.localBV.nu_out
      dvpsi_in := h.regularCenter.localBV.dvpsi_in
      dupsi_out := h.regularCenter.localBV.dupsi_out
      expansion_bounds := h.regularCenter.localBV.expansion_bounds
      expansion_variation := h.regularCenter.localBV.expansion_variation
      expansion_axis_limit := h.regularCenter.localBV.expansion_axis_limit
      scalar_ac_variation := h.regularCenter.localBV.scalar_ac_variation
      scalar_axis_variation := h.regularCenter.localBV.scalar_axis_variation
      psi_variation := h.regularCenter.localBV.psi_variation
      psi_axis_limit := h.regularCenter.localBV.psi_axis_limit
      axis_values := h.regularCenter.localBV.axis_values
      lam_right_cont := hx
      dvpsi_right_cont := h.dvpsi_right_cont
      nu_right_cont := h.nu_right_cont
      dupsi_right_cont := h.dupsi_right_cont
    }
    continuous_r := h.continuous_r
    continuous_m := h.continuous_m
    continuous_lam := h.continuous_lam
    continuous_nu := h.continuous_nu
    continuous_phi := h.continuous_phi
    ac_lam_out := h.ac_lam_out
    axis_expansions := h.regularCenter.axis_expansions
    axis_dvpsi_trace := h.regularCenter.axis_dvpsi_trace
    axis_dupsi_trace := h.regularCenter.axis_dupsi_trace
    axis_dvpsi_value := h.regularCenter.axis_dvpsi_value
    axis_dupsi_value := h.regularCenter.axis_dupsi_value
  }
  signs := h.signs
  initial_gauge := h.initial_gauge
  initial_ac_data := h.initial_ac_data
  blueshift_finite := h.blueshift_finite
}

/-- Restore the standing class using an explicit proof of the deleted `nu_right_cont` field. Paper
`e1a0fd5`, lines 114–132 and 220–275, `eq:regular-axis`, `eq:regular-axis-scalar-traces`. -/
theorem StandingWithout_nu_right_cont.restore {ui : ℝ} {S : SSFields}
    (h : StandingWithout_nu_right_cont ui S) (hx : ∀ p ∈ pastTriangle ui,
      ContinuousWithinAt (fun s => S.nu s p.2) {s | p.1 ≤ s ∧ (s, p.2) ∈ pastTriangle ui} p.1) :
    StandingFull ui S := {
  initial_negative := h.initial_negative
  regularCenter := {
    localBV := {
      radius_out := h.regularCenter.localBV.radius_out
      radius_in := h.regularCenter.localBV.radius_in
      psi_out := h.regularCenter.localBV.psi_out
      psi_in := h.regularCenter.localBV.psi_in
      mass_out := h.regularCenter.localBV.mass_out
      mass_in := h.regularCenter.localBV.mass_in
      lam_in := h.regularCenter.localBV.lam_in
      nu_out := h.regularCenter.localBV.nu_out
      dvpsi_in := h.regularCenter.localBV.dvpsi_in
      dupsi_out := h.regularCenter.localBV.dupsi_out
      expansion_bounds := h.regularCenter.localBV.expansion_bounds
      expansion_variation := h.regularCenter.localBV.expansion_variation
      expansion_axis_limit := h.regularCenter.localBV.expansion_axis_limit
      scalar_ac_variation := h.regularCenter.localBV.scalar_ac_variation
      scalar_axis_variation := h.regularCenter.localBV.scalar_axis_variation
      psi_variation := h.regularCenter.localBV.psi_variation
      psi_axis_limit := h.regularCenter.localBV.psi_axis_limit
      axis_values := h.regularCenter.localBV.axis_values
      lam_right_cont := h.lam_right_cont
      dvpsi_right_cont := h.dvpsi_right_cont
      nu_right_cont := hx
      dupsi_right_cont := h.dupsi_right_cont
    }
    continuous_r := h.continuous_r
    continuous_m := h.continuous_m
    continuous_lam := h.continuous_lam
    continuous_nu := h.continuous_nu
    continuous_phi := h.continuous_phi
    ac_lam_out := h.ac_lam_out
    axis_expansions := h.regularCenter.axis_expansions
    axis_dvpsi_trace := h.regularCenter.axis_dvpsi_trace
    axis_dupsi_trace := h.regularCenter.axis_dupsi_trace
    axis_dvpsi_value := h.regularCenter.axis_dvpsi_value
    axis_dupsi_value := h.regularCenter.axis_dupsi_value
  }
  signs := h.signs
  initial_gauge := h.initial_gauge
  initial_ac_data := h.initial_ac_data
  blueshift_finite := h.blueshift_finite
}

/-- Restore the standing class using an explicit proof of the deleted `dvpsi_right_cont` field.
Paper `e1a0fd5`, lines 114–132 and 220–275, `eq:regular-axis`, `eq:regular-axis-scalar-traces`. -/
theorem StandingWithout_dvpsi_right_cont.restore {ui : ℝ} {S : SSFields}
    (h : StandingWithout_dvpsi_right_cont ui S) (hx : ∀ p ∈ pastTriangle ui,
      ContinuousWithinAt (S.dvpsi p.1) {w | p.2 ≤ w ∧ (p.1, w) ∈ pastTriangle ui} p.2) :
    StandingFull ui S := {
  initial_negative := h.initial_negative
  regularCenter := {
    localBV := {
      radius_out := h.regularCenter.localBV.radius_out
      radius_in := h.regularCenter.localBV.radius_in
      psi_out := h.regularCenter.localBV.psi_out
      psi_in := h.regularCenter.localBV.psi_in
      mass_out := h.regularCenter.localBV.mass_out
      mass_in := h.regularCenter.localBV.mass_in
      lam_in := h.regularCenter.localBV.lam_in
      nu_out := h.regularCenter.localBV.nu_out
      dvpsi_in := h.regularCenter.localBV.dvpsi_in
      dupsi_out := h.regularCenter.localBV.dupsi_out
      expansion_bounds := h.regularCenter.localBV.expansion_bounds
      expansion_variation := h.regularCenter.localBV.expansion_variation
      expansion_axis_limit := h.regularCenter.localBV.expansion_axis_limit
      scalar_ac_variation := h.regularCenter.localBV.scalar_ac_variation
      scalar_axis_variation := h.regularCenter.localBV.scalar_axis_variation
      psi_variation := h.regularCenter.localBV.psi_variation
      psi_axis_limit := h.regularCenter.localBV.psi_axis_limit
      axis_values := h.regularCenter.localBV.axis_values
      lam_right_cont := h.lam_right_cont
      dvpsi_right_cont := hx
      nu_right_cont := h.nu_right_cont
      dupsi_right_cont := h.dupsi_right_cont
    }
    continuous_r := h.continuous_r
    continuous_m := h.continuous_m
    continuous_lam := h.continuous_lam
    continuous_nu := h.continuous_nu
    continuous_phi := h.continuous_phi
    ac_lam_out := h.ac_lam_out
    axis_expansions := h.regularCenter.axis_expansions
    axis_dvpsi_trace := h.regularCenter.axis_dvpsi_trace
    axis_dupsi_trace := h.regularCenter.axis_dupsi_trace
    axis_dvpsi_value := h.regularCenter.axis_dvpsi_value
    axis_dupsi_value := h.regularCenter.axis_dupsi_value
  }
  signs := h.signs
  initial_gauge := h.initial_gauge
  initial_ac_data := h.initial_ac_data
  blueshift_finite := h.blueshift_finite
}

/-- Restore the standing class using an explicit proof of the deleted `dupsi_right_cont` field.
Paper `e1a0fd5`, lines 114–132 and 220–275, `eq:regular-axis`, `eq:regular-axis-scalar-traces`. -/
theorem StandingWithout_dupsi_right_cont.restore {ui : ℝ} {S : SSFields}
    (h : StandingWithout_dupsi_right_cont ui S) (hx : ∀ p ∈ pastTriangle ui,
      ContinuousWithinAt (fun s => S.dupsi s p.2) {s | p.1 ≤ s ∧ (s, p.2) ∈ pastTriangle ui} p.1) :
    StandingFull ui S := {
  initial_negative := h.initial_negative
  regularCenter := {
    localBV := {
      radius_out := h.regularCenter.localBV.radius_out
      radius_in := h.regularCenter.localBV.radius_in
      psi_out := h.regularCenter.localBV.psi_out
      psi_in := h.regularCenter.localBV.psi_in
      mass_out := h.regularCenter.localBV.mass_out
      mass_in := h.regularCenter.localBV.mass_in
      lam_in := h.regularCenter.localBV.lam_in
      nu_out := h.regularCenter.localBV.nu_out
      dvpsi_in := h.regularCenter.localBV.dvpsi_in
      dupsi_out := h.regularCenter.localBV.dupsi_out
      expansion_bounds := h.regularCenter.localBV.expansion_bounds
      expansion_variation := h.regularCenter.localBV.expansion_variation
      expansion_axis_limit := h.regularCenter.localBV.expansion_axis_limit
      scalar_ac_variation := h.regularCenter.localBV.scalar_ac_variation
      scalar_axis_variation := h.regularCenter.localBV.scalar_axis_variation
      psi_variation := h.regularCenter.localBV.psi_variation
      psi_axis_limit := h.regularCenter.localBV.psi_axis_limit
      axis_values := h.regularCenter.localBV.axis_values
      lam_right_cont := h.lam_right_cont
      dvpsi_right_cont := h.dvpsi_right_cont
      nu_right_cont := h.nu_right_cont
      dupsi_right_cont := hx
    }
    continuous_r := h.continuous_r
    continuous_m := h.continuous_m
    continuous_lam := h.continuous_lam
    continuous_nu := h.continuous_nu
    continuous_phi := h.continuous_phi
    ac_lam_out := h.ac_lam_out
    axis_expansions := h.regularCenter.axis_expansions
    axis_dvpsi_trace := h.regularCenter.axis_dvpsi_trace
    axis_dupsi_trace := h.regularCenter.axis_dupsi_trace
    axis_dvpsi_value := h.regularCenter.axis_dvpsi_value
    axis_dupsi_value := h.regularCenter.axis_dupsi_value
  }
  signs := h.signs
  initial_gauge := h.initial_gauge
  initial_ac_data := h.initial_ac_data
  blueshift_finite := h.blueshift_finite
}

end AcExtensionPrinciple

end
