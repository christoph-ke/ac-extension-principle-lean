module

public import AcExtensionPrinciple.Solution.LocalBVFull

/-!
# Internal full regular-center AC/BV bundle

Paper commit `e1a0fd5`, `equations.tex` lines 114–119 and 220–275. Ruling Q1 supplies additional
outgoing AC of λ and omits incoming AC of ν: the proof of Theorem 1 uses only incoming continuity
and BV of ν, supplied by the remaining fields. Scalar axis traces are limits within the off-axis
past triangle.
-/

public section

namespace AcExtensionPrinciple

open Set Filter
open scoped Topology

/-- Regular-center additions to the full working BV class. Paper `e1a0fd5`,
lines 114 and 220–275, `eq:regular-axis`, `eq:regular-axis-scalar-traces`. -/
structure RegularCenterFull (ui : ℝ) (S : SSFields) : Prop where
  localBV : LocalBVSolutionFull (pastTriangle ui) S
  continuous_r : ContinuousOn (fun p => S.r p.1 p.2) (pastTriangle ui)
  continuous_m : ContinuousOn (fun p => S.m p.1 p.2) (pastTriangle ui)
  continuous_lam : ContinuousOn (fun p => S.lam p.1 p.2) (pastTriangle ui)
  continuous_nu : ContinuousOn (fun p => S.nu p.1 p.2) (pastTriangle ui)
  continuous_phi : ContinuousOn (fun p => S.phi p.1 p.2) (pastTriangle ui)
  ac_lam_out : ∀ u a b, a ≤ b → outSeg u a b ⊆ pastTriangle ui →
    AbsolutelyContinuousOnInterval (S.lam u) a b
  axis_expansions : ∀ a, (a, a) ∈ axis ui → S.nu a a = -S.lam a a
  axis_dvpsi_trace : ∀ a, (a, a) ∈ axis ui →
    Tendsto (fun p => S.dvpsi p.1 p.2 / S.lam p.1 p.2)
      (𝓝[pastTriangle ui \ axis ui] (a, a)) (𝓝 (S.phi a a))
  axis_dupsi_trace : ∀ a, (a, a) ∈ axis ui →
    Tendsto (fun p => S.dupsi p.1 p.2 / S.nu p.1 p.2)
      (𝓝[pastTriangle ui \ axis ui] (a, a)) (𝓝 (S.phi a a))
  /-- The axis values themselves: (∂ᵥψ/λ)(u,u) = φ(u,u). A limit alone does not
  fix the value on the axis. Paper `e1a0fd5`, `eq:regular-axis-scalar-traces`, line 259. -/
  axis_dvpsi_value : ∀ a, (a, a) ∈ axis ui → S.dvpsi a a / S.lam a a = S.phi a a
  /-- Paper `e1a0fd5`, `eq:regular-axis-scalar-traces`, line 259:
  (∂ᵤψ/ν)(u,u) = φ(u,u). -/
  axis_dupsi_value : ∀ a, (a, a) ∈ axis ui → S.dupsi a a / S.nu a a = S.phi a a

end AcExtensionPrinciple

end
