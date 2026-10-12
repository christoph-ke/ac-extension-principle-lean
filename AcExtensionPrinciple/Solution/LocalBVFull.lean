module

public import AcExtensionPrinciple.Solution.LocalBV

/-!
# Internal full local BV bundle
Paper `e1a0fd5`, `equations.tex` lines 66–84 and 220–275.
This preserves the former full interface for downstream proofs.
The source class is minimal; this bundle is derived for standing solutions.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- Integral equations and localized Luk–Oh BV conditions. Paper `e1a0fd5`,
lines 66–84 and 220–275; Definition 2.1(1)–(7), rulings Q6/Q8.
Segment endpoints are ordered; bounds are uniform over all segments in each
compact subset. No geometric conclusions are assumed. -/
structure LocalBVSolutionFull (D : Set (ℝ × ℝ)) (S : SSFields) : Prop where
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
  /-- Luk–Oh BV convention (pp. 1608–1609: BV functions are right-continuous),
  inherited by the paper's
  reference to Luk–Oh Def. 2.1 (paper `e1a0fd5`, line 222): λ, ∂ᵥψ right-continuous in v;
  ν, ∂ᵤψ right-continuous in u.
  Author ruling Q1. -/
  lam_right_cont : ∀ p ∈ D, ContinuousWithinAt (S.lam p.1) {w | p.2 ≤ w ∧ (p.1, w) ∈ D} p.2
  dvpsi_right_cont : ∀ p ∈ D, ContinuousWithinAt (S.dvpsi p.1) {w | p.2 ≤ w ∧ (p.1, w) ∈ D} p.2
  nu_right_cont : ∀ p ∈ D,
    ContinuousWithinAt (fun s => S.nu s p.2) {s | p.1 ≤ s ∧ (s, p.2) ∈ D} p.1
  dupsi_right_cont : ∀ p ∈ D,
    ContinuousWithinAt (fun s => S.dupsi s p.2) {s | p.1 ≤ s ∧ (s, p.2) ∈ D} p.1


end AcExtensionPrinciple

end
