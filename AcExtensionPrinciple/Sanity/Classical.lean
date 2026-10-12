module

public import AcExtensionPrinciple.Solution.StandingFull
public import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# Classical solutions with a regular apex (non-vacuity check)

This module defines a classical solution for non-vacuity checks.
This auxiliary definition is **not a source statement**. It describes a solution that is `C¹` on
the closed past triangle *including its apex* `(0,0)` (Christodoulou's `C¹` notion, CPAM 46 (1993)
p. 1157: λ, ν, φ, θ, ζ ∈ C¹ and inf λ > 0, here taken up to the axis and the apex), with the paper's
regular-axis conditions and the initial gauge of Theorem 1. It is used only to check that the
class of Theorem 1 contains every such solution. Paper `e1a0fd5`, `thm:main`,
lines 112–132, `eq:regular-axis` and lines 220–275.
-/

public section

namespace AcExtensionPrinciple

open Set

/-- Closed past triangle, including the apex `(0,0)`. Paper `e1a0fd5`, `eq:past-triangle`. -/
@[expose] def closedTriangle (ui : ℝ) : Set (ℝ × ℝ) := {p | ui ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 0}

/-- A classical (`C¹` up to the boundary) solution on the closed past triangle with a regular apex,
in the gauge of Theorem 1. The equations hold pointwise along each characteristic at the points
where that characteristic is two-sided inside the triangle. Paper `e1a0fd5`, lines 49–106
(`eq:radius`, `eq:mass`, `eq:wave-psi`), `eq:regular-axis`, `eq:initial-radius-gauge`, lines
112–132; Christodoulou, CPAM 46 (1993), p. 1157 (definition of a `C¹` solution). -/
structure ClassicalTriangleSolution (ui : ℝ) (S : SSFields) : Prop where
  initial_negative : ui < 0
  c1_r : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.r p.1 p.2) (closedTriangle ui)
  c1_m : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.m p.1 p.2) (closedTriangle ui)
  c1_phi : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.phi p.1 p.2) (closedTriangle ui)
  c1_lam : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.lam p.1 p.2) (closedTriangle ui)
  c1_nu : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.nu p.1 p.2) (closedTriangle ui)
  c1_dvpsi : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.dvpsi p.1 p.2) (closedTriangle ui)
  c1_dupsi : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.dupsi p.1 p.2) (closedTriangle ui)
  r_v : ∀ u v, ui ≤ u → u < v → v < 0 → HasDerivAt (S.r u) (S.lam u v) v
  r_u : ∀ u v, ui < u → u < v → v ≤ 0 → HasDerivAt (fun s => S.r s v) (S.nu u v) u
  psi_v : ∀ u v, ui ≤ u → u < v → v < 0 →
    HasDerivAt (fun w => S.r u w * S.phi u w) (S.dvpsi u v) v
  psi_u : ∀ u v, ui < u → u < v → v ≤ 0 →
    HasDerivAt (fun s => S.r s v * S.phi s v) (S.dupsi u v) u
  m_v : ∀ u v, ui ≤ u → u < v → v < 0 → HasDerivAt (S.m u) (S.massV u v) v
  m_u : ∀ u v, ui < u → u < v → v ≤ 0 → HasDerivAt (fun s => S.m s v) (S.massU u v) u
  lam_u : ∀ u v, ui < u → u < v → v ≤ 0 →
    HasDerivAt (fun s => S.lam s v) (S.radiusCoeff u v) u
  nu_v : ∀ u v, ui ≤ u → u < v → v < 0 → HasDerivAt (S.nu u) (S.radiusCoeff u v) v
  dvpsi_u : ∀ u v, ui < u → u < v → v ≤ 0 →
    HasDerivAt (fun s => S.dvpsi s v) (S.radiusCoeff u v * S.phi u v) u
  dupsi_v : ∀ u v, ui ≤ u → u < v → v < 0 →
    HasDerivAt (S.dupsi u) (S.radiusCoeff u v * S.phi u v) v
  /-- `eq:regular-axis`, on the closed axis including the apex.
Paper `e1a0fd5`, line 243. -/
  axis : ∀ a, ui ≤ a → a ≤ 0 → S.r a a = 0 ∧ S.m a a = 0 ∧ S.nu a a = -S.lam a a
  /-- Christodoulou's `inf λ > 0` and `ν < 0`, on the closed triangle. -/
  expansions : ∀ p ∈ closedTriangle ui, 0 < S.lam p.1 p.2 ∧ S.nu p.1 p.2 < 0
  /-- Line 113: `0 ≤ μ < 1` away from the axis. -/
  mass_ratio : ∀ p ∈ closedTriangle ui, p.1 < p.2 → 0 ≤ S.mu p.1 p.2 ∧ S.mu p.1 p.2 < 1
  /-- `eq:initial-radius-gauge`. -/
  initial_gauge : ∀ v ∈ Icc ui 0, S.r ui v = v - ui ∧ S.lam ui v = 1

end AcExtensionPrinciple

end
