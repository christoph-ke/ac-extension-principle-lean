module

public import AcExtensionPrinciple.Minimal.ScalarAC
public import AcExtensionPrinciple.Minimal.OneSidedTraces
public import AcExtensionPrinciple.Redundancy.LambdaContinuity

/-!
# Recover the core and record exact expansion premises
Paper `e1a0fd5`, `equations.tex` lines 114–132 and 220–261.
Joint normalized traces and scalar AC have been restored when constructing the Q1 core.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- Restore scalar AC into the old core after deriving it from the minimal class.
Paper `e1a0fd5`, lines 114–132 and 220–261,
`eq:regular-axis`, `eq:regular-axis-scalar-traces`. -/
theorem StandingAssumptions.toQ1StandingCore {ui : ℝ} {S : SSFields}
    (h : StandingAssumptions ui S) : Q1StandingCore ui S := {
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
      scalar_ac_variation := by
        intro K hK hKD
        obtain ⟨C, hout, hin⟩ := h.regularCenter.localBV.scalar_variation K hK hKD
        exact ⟨C,
          fun u a b hab hs => ⟨h.phi_out_ac u a b hab (hs.trans hKD), hout u a b hab hs⟩,
          fun v a b hab hs => ⟨h.phi_in_ac v a b hab (hs.trans hKD), hin v a b hab hs⟩⟩
      scalar_axis_variation := h.regularCenter.localBV.scalar_axis_variation
      psi_variation := h.regularCenter.localBV.psi_variation
      psi_axis_limit := h.regularCenter.localBV.psi_axis_limit
      axis_values := h.regularCenter.localBV.axis_values
    }
    axis_expansions := h.regularCenter.axis_expansions
    axis_dvpsi_trace := fun _ ha => h.axis_dvpsi_trace ha
    axis_dupsi_trace := fun _ ha => h.axis_dupsi_trace ha
    axis_dvpsi_value := h.regularCenter.axis_dvpsi_value
    axis_dupsi_value := h.regularCenter.axis_dupsi_value
  }
  signs := h.signs
  initial_gauge := h.initial_gauge
  initial_ac_data := h.initial_ac_data
  blueshift_finite := h.blueshift_finite
}

/-- Intermediate derived bundle: continuous r, m, φ and the retained ν, without any
λ regularity or right-continuity conventions. Every added field is discharged by
`StandingAssumptions.toExpansionDraft`. Paper `e1a0fd5`, lines 220–275. -/
structure MinimalExpansionDraft (ui : ℝ) (S : SSFields) : Prop extends Q1StandingCore ui S where
  continuous_r : ContinuousOn (fun p => S.r p.1 p.2) (pastTriangle ui)
  continuous_m : ContinuousOn (fun p => S.m p.1 p.2) (pastTriangle ui)
  continuous_nu : ContinuousOn (fun p => S.nu p.1 p.2) (pastTriangle ui)
  continuous_phi : ContinuousOn (fun p => S.phi p.1 p.2) (pastTriangle ui)

/-- Enter the expansion proof after scalar AC and joint scalar continuity are derived.
Paper `e1a0fd5`, lines 220–275. -/
theorem StandingAssumptions.toExpansionDraft {ui : ℝ} {S : SSFields}
    (h : StandingAssumptions ui S) : MinimalExpansionDraft ui S := {
  toQ1StandingCore := h.toQ1StandingCore
  continuous_r := h.continuous_r
  continuous_m := h.continuous_m
  continuous_nu := h.regularCenter.continuous_nu
  continuous_phi := h.continuous_phi
}

end AcExtensionPrinciple

end
