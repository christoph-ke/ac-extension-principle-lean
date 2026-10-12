module

public import AcExtensionPrinciple.Redundancy.Core

/-!
# Explicit classes with exactly one Q1 field deleted
Paper commit `e1a0fd5`, `equations.tex` lines 114–132 and 220–275.
Under ruling Q1, each deletion retains every other standing assumption.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- Exactly `StandingFull` with `lam_right_cont` deleted; the ten other Q1 fields remain.
Paper `e1a0fd5`, lines 114–132 and 220–275, `eq:regular-axis`, `eq:regular-axis-scalar-traces`. -/
structure StandingWithout_lam_right_cont (ui : ℝ) (S : SSFields) : Prop
    extends Q1StandingCore ui S where
  continuous_r : ContinuousOn (fun p => S.r p.1 p.2) (pastTriangle ui)
  continuous_m : ContinuousOn (fun p => S.m p.1 p.2) (pastTriangle ui)
  continuous_lam : ContinuousOn (fun p => S.lam p.1 p.2) (pastTriangle ui)
  continuous_nu : ContinuousOn (fun p => S.nu p.1 p.2) (pastTriangle ui)
  continuous_phi : ContinuousOn (fun p => S.phi p.1 p.2) (pastTriangle ui)
  ac_lam_out : ∀ u a b, a ≤ b → outSeg u a b ⊆ pastTriangle ui →
    AbsolutelyContinuousOnInterval (S.lam u) a b
  nu_right_cont : ∀ p ∈ pastTriangle ui,
    ContinuousWithinAt (fun s => S.nu s p.2) {s | p.1 ≤ s ∧ (s, p.2) ∈ pastTriangle ui} p.1
  dvpsi_right_cont : ∀ p ∈ pastTriangle ui,
    ContinuousWithinAt (S.dvpsi p.1) {w | p.2 ≤ w ∧ (p.1, w) ∈ pastTriangle ui} p.2
  dupsi_right_cont : ∀ p ∈ pastTriangle ui,
    ContinuousWithinAt (fun s => S.dupsi s p.2) {s | p.1 ≤ s ∧ (s, p.2) ∈ pastTriangle ui} p.1

/-- Extract the class with `lam_right_cont` deleted without retaining the deleted proof. Paper
`e1a0fd5`, lines 114–132 and 220–275, `eq:regular-axis`, `eq:regular-axis-scalar-traces`. -/
theorem StandingWithout_lam_right_cont.ofStanding {ui : ℝ} {S : SSFields}
    (h : StandingFull ui S) : StandingWithout_lam_right_cont ui S := {
  toQ1StandingCore := Q1StandingCore.ofStanding h
  continuous_r := h.regularCenter.continuous_r
  continuous_m := h.regularCenter.continuous_m
  continuous_lam := h.regularCenter.continuous_lam
  continuous_nu := h.regularCenter.continuous_nu
  continuous_phi := h.regularCenter.continuous_phi
  ac_lam_out := h.regularCenter.ac_lam_out
  nu_right_cont := h.regularCenter.localBV.nu_right_cont
  dvpsi_right_cont := h.regularCenter.localBV.dvpsi_right_cont
  dupsi_right_cont := h.regularCenter.localBV.dupsi_right_cont
}

/-- Exactly `StandingFull` with `nu_right_cont` deleted; the ten other Q1 fields remain.
Paper `e1a0fd5`, lines 114–132 and 220–275, `eq:regular-axis`, `eq:regular-axis-scalar-traces`. -/
structure StandingWithout_nu_right_cont (ui : ℝ) (S : SSFields) : Prop
    extends Q1StandingCore ui S where
  continuous_r : ContinuousOn (fun p => S.r p.1 p.2) (pastTriangle ui)
  continuous_m : ContinuousOn (fun p => S.m p.1 p.2) (pastTriangle ui)
  continuous_lam : ContinuousOn (fun p => S.lam p.1 p.2) (pastTriangle ui)
  continuous_nu : ContinuousOn (fun p => S.nu p.1 p.2) (pastTriangle ui)
  continuous_phi : ContinuousOn (fun p => S.phi p.1 p.2) (pastTriangle ui)
  ac_lam_out : ∀ u a b, a ≤ b → outSeg u a b ⊆ pastTriangle ui →
    AbsolutelyContinuousOnInterval (S.lam u) a b
  lam_right_cont : ∀ p ∈ pastTriangle ui,
    ContinuousWithinAt (S.lam p.1) {w | p.2 ≤ w ∧ (p.1, w) ∈ pastTriangle ui} p.2
  dvpsi_right_cont : ∀ p ∈ pastTriangle ui,
    ContinuousWithinAt (S.dvpsi p.1) {w | p.2 ≤ w ∧ (p.1, w) ∈ pastTriangle ui} p.2
  dupsi_right_cont : ∀ p ∈ pastTriangle ui,
    ContinuousWithinAt (fun s => S.dupsi s p.2) {s | p.1 ≤ s ∧ (s, p.2) ∈ pastTriangle ui} p.1

/-- Extract the class with `nu_right_cont` deleted without retaining the deleted proof. Paper
`e1a0fd5`, lines 114–132 and 220–275, `eq:regular-axis`, `eq:regular-axis-scalar-traces`. -/
theorem StandingWithout_nu_right_cont.ofStanding {ui : ℝ} {S : SSFields}
    (h : StandingFull ui S) : StandingWithout_nu_right_cont ui S := {
  toQ1StandingCore := Q1StandingCore.ofStanding h
  continuous_r := h.regularCenter.continuous_r
  continuous_m := h.regularCenter.continuous_m
  continuous_lam := h.regularCenter.continuous_lam
  continuous_nu := h.regularCenter.continuous_nu
  continuous_phi := h.regularCenter.continuous_phi
  ac_lam_out := h.regularCenter.ac_lam_out
  lam_right_cont := h.regularCenter.localBV.lam_right_cont
  dvpsi_right_cont := h.regularCenter.localBV.dvpsi_right_cont
  dupsi_right_cont := h.regularCenter.localBV.dupsi_right_cont
}

/-- Exactly `StandingFull` with `dvpsi_right_cont` deleted; the ten other Q1 fields remain.
Paper `e1a0fd5`, lines 114–132 and 220–275, `eq:regular-axis`, `eq:regular-axis-scalar-traces`. -/
structure StandingWithout_dvpsi_right_cont (ui : ℝ) (S : SSFields) : Prop
    extends Q1StandingCore ui S where
  continuous_r : ContinuousOn (fun p => S.r p.1 p.2) (pastTriangle ui)
  continuous_m : ContinuousOn (fun p => S.m p.1 p.2) (pastTriangle ui)
  continuous_lam : ContinuousOn (fun p => S.lam p.1 p.2) (pastTriangle ui)
  continuous_nu : ContinuousOn (fun p => S.nu p.1 p.2) (pastTriangle ui)
  continuous_phi : ContinuousOn (fun p => S.phi p.1 p.2) (pastTriangle ui)
  ac_lam_out : ∀ u a b, a ≤ b → outSeg u a b ⊆ pastTriangle ui →
    AbsolutelyContinuousOnInterval (S.lam u) a b
  lam_right_cont : ∀ p ∈ pastTriangle ui,
    ContinuousWithinAt (S.lam p.1) {w | p.2 ≤ w ∧ (p.1, w) ∈ pastTriangle ui} p.2
  nu_right_cont : ∀ p ∈ pastTriangle ui,
    ContinuousWithinAt (fun s => S.nu s p.2) {s | p.1 ≤ s ∧ (s, p.2) ∈ pastTriangle ui} p.1
  dupsi_right_cont : ∀ p ∈ pastTriangle ui,
    ContinuousWithinAt (fun s => S.dupsi s p.2) {s | p.1 ≤ s ∧ (s, p.2) ∈ pastTriangle ui} p.1

/-- Extract the class with `dvpsi_right_cont` deleted without retaining the deleted proof. Paper
`e1a0fd5`, lines 114–132 and 220–275, `eq:regular-axis`, `eq:regular-axis-scalar-traces`. -/
theorem StandingWithout_dvpsi_right_cont.ofStanding {ui : ℝ} {S : SSFields}
    (h : StandingFull ui S) : StandingWithout_dvpsi_right_cont ui S := {
  toQ1StandingCore := Q1StandingCore.ofStanding h
  continuous_r := h.regularCenter.continuous_r
  continuous_m := h.regularCenter.continuous_m
  continuous_lam := h.regularCenter.continuous_lam
  continuous_nu := h.regularCenter.continuous_nu
  continuous_phi := h.regularCenter.continuous_phi
  ac_lam_out := h.regularCenter.ac_lam_out
  lam_right_cont := h.regularCenter.localBV.lam_right_cont
  nu_right_cont := h.regularCenter.localBV.nu_right_cont
  dupsi_right_cont := h.regularCenter.localBV.dupsi_right_cont
}

/-- Exactly `StandingFull` with `dupsi_right_cont` deleted; the ten other Q1 fields remain.
Paper `e1a0fd5`, lines 114–132 and 220–275, `eq:regular-axis`, `eq:regular-axis-scalar-traces`. -/
structure StandingWithout_dupsi_right_cont (ui : ℝ) (S : SSFields) : Prop
    extends Q1StandingCore ui S where
  continuous_r : ContinuousOn (fun p => S.r p.1 p.2) (pastTriangle ui)
  continuous_m : ContinuousOn (fun p => S.m p.1 p.2) (pastTriangle ui)
  continuous_lam : ContinuousOn (fun p => S.lam p.1 p.2) (pastTriangle ui)
  continuous_nu : ContinuousOn (fun p => S.nu p.1 p.2) (pastTriangle ui)
  continuous_phi : ContinuousOn (fun p => S.phi p.1 p.2) (pastTriangle ui)
  ac_lam_out : ∀ u a b, a ≤ b → outSeg u a b ⊆ pastTriangle ui →
    AbsolutelyContinuousOnInterval (S.lam u) a b
  lam_right_cont : ∀ p ∈ pastTriangle ui,
    ContinuousWithinAt (S.lam p.1) {w | p.2 ≤ w ∧ (p.1, w) ∈ pastTriangle ui} p.2
  nu_right_cont : ∀ p ∈ pastTriangle ui,
    ContinuousWithinAt (fun s => S.nu s p.2) {s | p.1 ≤ s ∧ (s, p.2) ∈ pastTriangle ui} p.1
  dvpsi_right_cont : ∀ p ∈ pastTriangle ui,
    ContinuousWithinAt (S.dvpsi p.1) {w | p.2 ≤ w ∧ (p.1, w) ∈ pastTriangle ui} p.2

/-- Extract the class with `dupsi_right_cont` deleted without retaining the deleted proof. Paper
`e1a0fd5`, lines 114–132 and 220–275, `eq:regular-axis`, `eq:regular-axis-scalar-traces`. -/
theorem StandingWithout_dupsi_right_cont.ofStanding {ui : ℝ} {S : SSFields}
    (h : StandingFull ui S) : StandingWithout_dupsi_right_cont ui S := {
  toQ1StandingCore := Q1StandingCore.ofStanding h
  continuous_r := h.regularCenter.continuous_r
  continuous_m := h.regularCenter.continuous_m
  continuous_lam := h.regularCenter.continuous_lam
  continuous_nu := h.regularCenter.continuous_nu
  continuous_phi := h.regularCenter.continuous_phi
  ac_lam_out := h.regularCenter.ac_lam_out
  lam_right_cont := h.regularCenter.localBV.lam_right_cont
  nu_right_cont := h.regularCenter.localBV.nu_right_cont
  dvpsi_right_cont := h.regularCenter.localBV.dvpsi_right_cont
}

end AcExtensionPrinciple

end
