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

/-- Exactly `StandingFull` with `continuous_r` deleted; the ten other Q1 fields remain.
Paper `e1a0fd5`, lines 114–132 and 220–275, `eq:regular-axis`, `eq:regular-axis-scalar-traces`. -/
structure StandingWithout_continuous_r (ui : ℝ) (S : SSFields) : Prop
    extends Q1StandingCore ui S where
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
  dupsi_right_cont : ∀ p ∈ pastTriangle ui,
    ContinuousWithinAt (fun s => S.dupsi s p.2) {s | p.1 ≤ s ∧ (s, p.2) ∈ pastTriangle ui} p.1

/-- Extract the class with `continuous_r` deleted without retaining the deleted proof. Paper
`e1a0fd5`, lines 114–132 and 220–275, `eq:regular-axis`, `eq:regular-axis-scalar-traces`. -/
theorem StandingWithout_continuous_r.ofStanding {ui : ℝ} {S : SSFields}
    (h : StandingFull ui S) : StandingWithout_continuous_r ui S := {
  toQ1StandingCore := Q1StandingCore.ofStanding h
  continuous_m := h.regularCenter.continuous_m
  continuous_lam := h.regularCenter.continuous_lam
  continuous_nu := h.regularCenter.continuous_nu
  continuous_phi := h.regularCenter.continuous_phi
  ac_lam_out := h.regularCenter.ac_lam_out
  lam_right_cont := h.regularCenter.localBV.lam_right_cont
  nu_right_cont := h.regularCenter.localBV.nu_right_cont
  dvpsi_right_cont := h.regularCenter.localBV.dvpsi_right_cont
  dupsi_right_cont := h.regularCenter.localBV.dupsi_right_cont
}

/-- Exactly `StandingFull` with `continuous_m` deleted; the ten other Q1 fields remain.
Paper `e1a0fd5`, lines 114–132 and 220–275, `eq:regular-axis`, `eq:regular-axis-scalar-traces`. -/
structure StandingWithout_continuous_m (ui : ℝ) (S : SSFields) : Prop
    extends Q1StandingCore ui S where
  continuous_r : ContinuousOn (fun p => S.r p.1 p.2) (pastTriangle ui)
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
  dupsi_right_cont : ∀ p ∈ pastTriangle ui,
    ContinuousWithinAt (fun s => S.dupsi s p.2) {s | p.1 ≤ s ∧ (s, p.2) ∈ pastTriangle ui} p.1

/-- Extract the class with `continuous_m` deleted without retaining the deleted proof. Paper
`e1a0fd5`, lines 114–132 and 220–275, `eq:regular-axis`, `eq:regular-axis-scalar-traces`. -/
theorem StandingWithout_continuous_m.ofStanding {ui : ℝ} {S : SSFields}
    (h : StandingFull ui S) : StandingWithout_continuous_m ui S := {
  toQ1StandingCore := Q1StandingCore.ofStanding h
  continuous_r := h.regularCenter.continuous_r
  continuous_lam := h.regularCenter.continuous_lam
  continuous_nu := h.regularCenter.continuous_nu
  continuous_phi := h.regularCenter.continuous_phi
  ac_lam_out := h.regularCenter.ac_lam_out
  lam_right_cont := h.regularCenter.localBV.lam_right_cont
  nu_right_cont := h.regularCenter.localBV.nu_right_cont
  dvpsi_right_cont := h.regularCenter.localBV.dvpsi_right_cont
  dupsi_right_cont := h.regularCenter.localBV.dupsi_right_cont
}

/-- Exactly `StandingFull` with `continuous_lam` deleted; the ten other Q1 fields remain.
Paper `e1a0fd5`, lines 114–132 and 220–275, `eq:regular-axis`, `eq:regular-axis-scalar-traces`. -/
structure StandingWithout_continuous_lam (ui : ℝ) (S : SSFields) : Prop
    extends Q1StandingCore ui S where
  continuous_r : ContinuousOn (fun p => S.r p.1 p.2) (pastTriangle ui)
  continuous_m : ContinuousOn (fun p => S.m p.1 p.2) (pastTriangle ui)
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
  dupsi_right_cont : ∀ p ∈ pastTriangle ui,
    ContinuousWithinAt (fun s => S.dupsi s p.2) {s | p.1 ≤ s ∧ (s, p.2) ∈ pastTriangle ui} p.1

/-- Extract the class with `continuous_lam` deleted without retaining the deleted proof. Paper
`e1a0fd5`, lines 114–132 and 220–275, `eq:regular-axis`, `eq:regular-axis-scalar-traces`. -/
theorem StandingWithout_continuous_lam.ofStanding {ui : ℝ} {S : SSFields}
    (h : StandingFull ui S) : StandingWithout_continuous_lam ui S := {
  toQ1StandingCore := Q1StandingCore.ofStanding h
  continuous_r := h.regularCenter.continuous_r
  continuous_m := h.regularCenter.continuous_m
  continuous_nu := h.regularCenter.continuous_nu
  continuous_phi := h.regularCenter.continuous_phi
  ac_lam_out := h.regularCenter.ac_lam_out
  lam_right_cont := h.regularCenter.localBV.lam_right_cont
  nu_right_cont := h.regularCenter.localBV.nu_right_cont
  dvpsi_right_cont := h.regularCenter.localBV.dvpsi_right_cont
  dupsi_right_cont := h.regularCenter.localBV.dupsi_right_cont
}

/-- Exactly `StandingFull` with `continuous_nu` deleted; the ten other Q1 fields remain.
Paper `e1a0fd5`, lines 114–132 and 220–275, `eq:regular-axis`, `eq:regular-axis-scalar-traces`. -/
structure StandingWithout_continuous_nu (ui : ℝ) (S : SSFields) : Prop
    extends Q1StandingCore ui S where
  continuous_r : ContinuousOn (fun p => S.r p.1 p.2) (pastTriangle ui)
  continuous_m : ContinuousOn (fun p => S.m p.1 p.2) (pastTriangle ui)
  continuous_lam : ContinuousOn (fun p => S.lam p.1 p.2) (pastTriangle ui)
  continuous_phi : ContinuousOn (fun p => S.phi p.1 p.2) (pastTriangle ui)
  ac_lam_out : ∀ u a b, a ≤ b → outSeg u a b ⊆ pastTriangle ui →
    AbsolutelyContinuousOnInterval (S.lam u) a b
  lam_right_cont : ∀ p ∈ pastTriangle ui,
    ContinuousWithinAt (S.lam p.1) {w | p.2 ≤ w ∧ (p.1, w) ∈ pastTriangle ui} p.2
  nu_right_cont : ∀ p ∈ pastTriangle ui,
    ContinuousWithinAt (fun s => S.nu s p.2) {s | p.1 ≤ s ∧ (s, p.2) ∈ pastTriangle ui} p.1
  dvpsi_right_cont : ∀ p ∈ pastTriangle ui,
    ContinuousWithinAt (S.dvpsi p.1) {w | p.2 ≤ w ∧ (p.1, w) ∈ pastTriangle ui} p.2
  dupsi_right_cont : ∀ p ∈ pastTriangle ui,
    ContinuousWithinAt (fun s => S.dupsi s p.2) {s | p.1 ≤ s ∧ (s, p.2) ∈ pastTriangle ui} p.1

/-- Extract the class with `continuous_nu` deleted without retaining the deleted proof. Paper
`e1a0fd5`, lines 114–132 and 220–275, `eq:regular-axis`, `eq:regular-axis-scalar-traces`. -/
theorem StandingWithout_continuous_nu.ofStanding {ui : ℝ} {S : SSFields}
    (h : StandingFull ui S) : StandingWithout_continuous_nu ui S := {
  toQ1StandingCore := Q1StandingCore.ofStanding h
  continuous_r := h.regularCenter.continuous_r
  continuous_m := h.regularCenter.continuous_m
  continuous_lam := h.regularCenter.continuous_lam
  continuous_phi := h.regularCenter.continuous_phi
  ac_lam_out := h.regularCenter.ac_lam_out
  lam_right_cont := h.regularCenter.localBV.lam_right_cont
  nu_right_cont := h.regularCenter.localBV.nu_right_cont
  dvpsi_right_cont := h.regularCenter.localBV.dvpsi_right_cont
  dupsi_right_cont := h.regularCenter.localBV.dupsi_right_cont
}

/-- Exactly `StandingFull` with `continuous_phi` deleted; the ten other Q1 fields remain.
Paper `e1a0fd5`, lines 114–132 and 220–275, `eq:regular-axis`, `eq:regular-axis-scalar-traces`. -/
structure StandingWithout_continuous_phi (ui : ℝ) (S : SSFields) : Prop
    extends Q1StandingCore ui S where
  continuous_r : ContinuousOn (fun p => S.r p.1 p.2) (pastTriangle ui)
  continuous_m : ContinuousOn (fun p => S.m p.1 p.2) (pastTriangle ui)
  continuous_lam : ContinuousOn (fun p => S.lam p.1 p.2) (pastTriangle ui)
  continuous_nu : ContinuousOn (fun p => S.nu p.1 p.2) (pastTriangle ui)
  ac_lam_out : ∀ u a b, a ≤ b → outSeg u a b ⊆ pastTriangle ui →
    AbsolutelyContinuousOnInterval (S.lam u) a b
  lam_right_cont : ∀ p ∈ pastTriangle ui,
    ContinuousWithinAt (S.lam p.1) {w | p.2 ≤ w ∧ (p.1, w) ∈ pastTriangle ui} p.2
  nu_right_cont : ∀ p ∈ pastTriangle ui,
    ContinuousWithinAt (fun s => S.nu s p.2) {s | p.1 ≤ s ∧ (s, p.2) ∈ pastTriangle ui} p.1
  dvpsi_right_cont : ∀ p ∈ pastTriangle ui,
    ContinuousWithinAt (S.dvpsi p.1) {w | p.2 ≤ w ∧ (p.1, w) ∈ pastTriangle ui} p.2
  dupsi_right_cont : ∀ p ∈ pastTriangle ui,
    ContinuousWithinAt (fun s => S.dupsi s p.2) {s | p.1 ≤ s ∧ (s, p.2) ∈ pastTriangle ui} p.1

/-- Extract the class with `continuous_phi` deleted without retaining the deleted proof. Paper
`e1a0fd5`, lines 114–132 and 220–275, `eq:regular-axis`, `eq:regular-axis-scalar-traces`. -/
theorem StandingWithout_continuous_phi.ofStanding {ui : ℝ} {S : SSFields}
    (h : StandingFull ui S) : StandingWithout_continuous_phi ui S := {
  toQ1StandingCore := Q1StandingCore.ofStanding h
  continuous_r := h.regularCenter.continuous_r
  continuous_m := h.regularCenter.continuous_m
  continuous_lam := h.regularCenter.continuous_lam
  continuous_nu := h.regularCenter.continuous_nu
  ac_lam_out := h.regularCenter.ac_lam_out
  lam_right_cont := h.regularCenter.localBV.lam_right_cont
  nu_right_cont := h.regularCenter.localBV.nu_right_cont
  dvpsi_right_cont := h.regularCenter.localBV.dvpsi_right_cont
  dupsi_right_cont := h.regularCenter.localBV.dupsi_right_cont
}

/-- Exactly `StandingFull` with `ac_lam_out` deleted; the ten other Q1 fields remain. Paper
`e1a0fd5`, lines 114–132 and 220–275, `eq:regular-axis`, `eq:regular-axis-scalar-traces`. -/
structure StandingWithout_ac_lam_out (ui : ℝ) (S : SSFields) : Prop
    extends Q1StandingCore ui S where
  continuous_r : ContinuousOn (fun p => S.r p.1 p.2) (pastTriangle ui)
  continuous_m : ContinuousOn (fun p => S.m p.1 p.2) (pastTriangle ui)
  continuous_lam : ContinuousOn (fun p => S.lam p.1 p.2) (pastTriangle ui)
  continuous_nu : ContinuousOn (fun p => S.nu p.1 p.2) (pastTriangle ui)
  continuous_phi : ContinuousOn (fun p => S.phi p.1 p.2) (pastTriangle ui)
  lam_right_cont : ∀ p ∈ pastTriangle ui,
    ContinuousWithinAt (S.lam p.1) {w | p.2 ≤ w ∧ (p.1, w) ∈ pastTriangle ui} p.2
  nu_right_cont : ∀ p ∈ pastTriangle ui,
    ContinuousWithinAt (fun s => S.nu s p.2) {s | p.1 ≤ s ∧ (s, p.2) ∈ pastTriangle ui} p.1
  dvpsi_right_cont : ∀ p ∈ pastTriangle ui,
    ContinuousWithinAt (S.dvpsi p.1) {w | p.2 ≤ w ∧ (p.1, w) ∈ pastTriangle ui} p.2
  dupsi_right_cont : ∀ p ∈ pastTriangle ui,
    ContinuousWithinAt (fun s => S.dupsi s p.2) {s | p.1 ≤ s ∧ (s, p.2) ∈ pastTriangle ui} p.1

/-- Extract the class with `ac_lam_out` deleted without retaining the deleted proof. Paper
`e1a0fd5`, lines 114–132 and 220–275, `eq:regular-axis`, `eq:regular-axis-scalar-traces`. -/
theorem StandingWithout_ac_lam_out.ofStanding {ui : ℝ} {S : SSFields}
    (h : StandingFull ui S) : StandingWithout_ac_lam_out ui S := {
  toQ1StandingCore := Q1StandingCore.ofStanding h
  continuous_r := h.regularCenter.continuous_r
  continuous_m := h.regularCenter.continuous_m
  continuous_lam := h.regularCenter.continuous_lam
  continuous_nu := h.regularCenter.continuous_nu
  continuous_phi := h.regularCenter.continuous_phi
  lam_right_cont := h.regularCenter.localBV.lam_right_cont
  nu_right_cont := h.regularCenter.localBV.nu_right_cont
  dvpsi_right_cont := h.regularCenter.localBV.dvpsi_right_cont
  dupsi_right_cont := h.regularCenter.localBV.dupsi_right_cont
}

/-- Exactly `StandingFull` with `ac_nu_in` deleted; the ten other Q1 fields remain. Paper
`e1a0fd5`, lines 114–132 and 220–275, `eq:regular-axis`, `eq:regular-axis-scalar-traces`. -/
structure StandingWithout_ac_nu_in (ui : ℝ) (S : SSFields) : Prop
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
  dupsi_right_cont : ∀ p ∈ pastTriangle ui,
    ContinuousWithinAt (fun s => S.dupsi s p.2) {s | p.1 ≤ s ∧ (s, p.2) ∈ pastTriangle ui} p.1

/-- Extract the class with `ac_nu_in` deleted without retaining the deleted proof. Paper `e1a0fd5`,
lines 114–132 and 220–275, `eq:regular-axis`, `eq:regular-axis-scalar-traces`. -/
theorem StandingWithout_ac_nu_in.ofStanding {ui : ℝ} {S : SSFields}
    (h : StandingFull ui S) : StandingWithout_ac_nu_in ui S := {
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
  dupsi_right_cont := h.regularCenter.localBV.dupsi_right_cont
}

end AcExtensionPrinciple

end
