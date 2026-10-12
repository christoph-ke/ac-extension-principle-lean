module

public import AcExtensionPrinciple.Solution.StandingFull

/-!
# Common unchanged hypotheses for the regularity deletions under ruling Q1
Paper commit `e1a0fd5`, `equations.tex` lines 114–132 and 220–275.
Under ruling Q1, each deletion retains every other standing assumption.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- The exact local BV class with its four representative conventions omitted. Paper `e1a0fd5`,
lines 114–132 and 220–275, `eq:regular-axis`, `eq:regular-axis-scalar-traces`. -/
structure Q1LocalBVCore (D : Set (ℝ × ℝ)) (S : SSFields) : Prop where
  radius_out : ∀ u a b, a ≤ b → outSeg u a b ⊆ D →
    IntervalPrimitive (S.r u) (S.lam u) a b
  radius_in : ∀ v a b, a ≤ b → inSeg v a b ⊆ D →
    IntervalPrimitive (fun u => S.r u v) (fun u => S.nu u v) a b
  psi_out : ∀ u a b, a ≤ b → outSeg u a b ⊆ D →
    IntervalPrimitive (fun v => S.r u v * S.phi u v) (S.dvpsi u) a b
  psi_in : ∀ v a b, a ≤ b → inSeg v a b ⊆ D →
    IntervalPrimitive (fun u => S.r u v * S.phi u v) (fun u => S.dupsi u v) a b
  mass_out : ∀ u a b, a ≤ b → outSeg u a b ⊆ D →
    IntervalPrimitive (S.m u) (S.massV u) a b
  mass_in : ∀ v a b, a ≤ b → inSeg v a b ⊆ D →
    IntervalPrimitive (fun u => S.m u v) (fun u => S.massU u v) a b
  lam_in : ∀ v a b, a ≤ b → inSeg v a b ⊆ offAxis D →
    IntervalPrimitive (fun u => S.lam u v) (fun u => S.radiusCoeff u v) a b
  nu_out : ∀ u a b, a ≤ b → outSeg u a b ⊆ offAxis D →
    IntervalPrimitive (S.nu u) (S.radiusCoeff u) a b
  dvpsi_in : ∀ v a b, a ≤ b → inSeg v a b ⊆ offAxis D →
    IntervalPrimitive (fun u => S.dvpsi u v) (fun u => S.radiusCoeff u v * S.phi u v) a b
  dupsi_out : ∀ u a b, a ≤ b → outSeg u a b ⊆ offAxis D →
    IntervalPrimitive (S.dupsi u) (fun v => S.radiusCoeff u v * S.phi u v) a b
  expansion_bounds : ∀ K, IsCompact K → K ⊆ D → ∃ c : ℝ, 0 < c ∧
    ∀ p ∈ K, c ≤ S.lam p.1 p.2 ∧ -S.nu p.1 p.2 ≤ 1 / c
  expansion_variation : ∀ K, IsCompact K → K ⊆ D → ∃ C : ℝ,
    (∀ u a b, a ≤ b → outSeg u a b ⊆ K →
      eVariationOn (S.lam u) (Icc a b) ≤ ENNReal.ofReal C) ∧
    (∀ v a b, a ≤ b → inSeg v a b ⊆ K →
      eVariationOn (fun u => S.nu u v) (Icc a b) ≤ ENNReal.ofReal C)
  expansion_axis_limit : ∀ a, (a, a) ∈ D →
    Tendsto (fun ε => S.nu a (a + ε) + S.lam a (a + ε)) (𝓝[>] 0) (𝓝 0)
  scalar_ac_variation : ∀ K, IsCompact K → K ⊆ D → ∃ C : ℝ,
    (∀ u a b, a ≤ b → outSeg u a b ⊆ K →
      AbsolutelyContinuousOnInterval (S.phi u) a b ∧
        eVariationOn (S.phi u) (Icc a b) ≤ ENNReal.ofReal C) ∧
    (∀ v a b, a ≤ b → inSeg v a b ⊆ K →
      AbsolutelyContinuousOnInterval (fun u => S.phi u v) a b ∧
        eVariationOn (fun u => S.phi u v) (Icc a b) ≤ ENNReal.ofReal C)
  scalar_axis_variation : ∀ a, (a, a) ∈ D → AxisVanishingVariation D S a
  psi_variation : ∀ K, IsCompact K → K ⊆ D → ∃ C : ℝ,
    (∀ u a b, a ≤ b → outSeg u a b ⊆ K →
      eVariationOn (S.dvpsi u) (Icc a b) ≤ ENNReal.ofReal C) ∧
    (∀ v a b, a ≤ b → inSeg v a b ⊆ K →
      eVariationOn (fun u => S.dupsi u v) (Icc a b) ≤ ENNReal.ofReal C)
  psi_axis_limit : ∀ a, (a, a) ∈ D →
    Tendsto (fun ε => S.dvpsi a (a + ε) + S.dupsi a (a + ε)) (𝓝[>] 0) (𝓝 0)
  axis_values : ∀ a, (a, a) ∈ D → S.r a a = 0 ∧ S.m a a = 0

/-- The regular-center class with all eleven additional fields omitted. Paper `e1a0fd5`, lines
114–132 and 220–275, `eq:regular-axis`, `eq:regular-axis-scalar-traces`. -/
structure Q1RegularCenterCore (ui : ℝ) (S : SSFields) : Prop where
  localBV : Q1LocalBVCore (pastTriangle ui) S
  axis_expansions : ∀ a, (a, a) ∈ axis ui → S.nu a a = -S.lam a a
  axis_dvpsi_trace : ∀ a, (a, a) ∈ axis ui →
    Tendsto (fun p => S.dvpsi p.1 p.2 / S.lam p.1 p.2)
      (𝓝[pastTriangle ui \ axis ui] (a, a)) (𝓝 (S.phi a a))
  axis_dupsi_trace : ∀ a, (a, a) ∈ axis ui →
    Tendsto (fun p => S.dupsi p.1 p.2 / S.nu p.1 p.2)
      (𝓝[pastTriangle ui \ axis ui] (a, a)) (𝓝 (S.phi a a))
  axis_dvpsi_value : ∀ a, (a, a) ∈ axis ui → S.dvpsi a a / S.lam a a = S.phi a a
  axis_dupsi_value : ∀ a, (a, a) ∈ axis ui → S.dupsi a a / S.nu a a = S.phi a a

/-- All standing hypotheses other than the eleven additional fields of the full working class
(ruling Q1). Paper `e1a0fd5`, lines 114–132 and 220–275, `eq:regular-axis`,
`eq:regular-axis-scalar-traces`. -/
structure Q1StandingCore (ui : ℝ) (S : SSFields) : Prop where
  initial_negative : ui < 0
  regularCenter : Q1RegularCenterCore ui S
  signs : ∀ p ∈ pastTriangle ui, p.1 < p.2 →
    0 < S.lam p.1 p.2 ∧ S.nu p.1 p.2 < 0 ∧ 0 ≤ S.mu p.1 p.2 ∧ S.mu p.1 p.2 < 1
  initial_gauge : ∀ v ∈ Icc ui 0, S.r ui v = v - ui ∧ S.lam ui v = 1
  initial_ac_data : AbsolutelyContinuousOnInterval (S.dvpsi ui) ui 0
  blueshift_finite : blueshiftSup ui S < ⊤

/-- Extract only the unchanged hypotheses from the existing standing class. Paper `e1a0fd5`, lines
114–132 and 220–275, `eq:regular-axis`, `eq:regular-axis-scalar-traces`. -/
theorem Q1StandingCore.ofStanding {ui : ℝ} {S : SSFields}
    (h : StandingFull ui S) : Q1StandingCore ui S := {
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
    }
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
