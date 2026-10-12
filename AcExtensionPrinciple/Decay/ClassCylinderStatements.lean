module

public import AcExtensionPrinciple.Decay.ClassScalarStatements
public import AcExtensionPrinciple.BoundaryEnergy.Pointwise
public import AcExtensionPrinciple.Cylinder.Geometry
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Tactic

/-!
# Exact cylinder premises for the mass-decay assembly

Paper `e1a0fd5`, `equations.tex` lines 661–833. Regular intervals have `a₁ < 0` and `r(u,0) ≥ b`
(the regular cylinder condition); the exterior hypothesis is confined to `u₀ ≤ u ≤ a₁` (the past
exterior condition). Constants are selected before radii, times and ε.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped ENNReal

/-- A regular cylinder and its boundary clock; paper `e1a0fd5`, `eq:cylinder-tangent`,
`eq:cylinder-time`, lines 664–675, with the regular cylinder condition. -/
structure DecayCylinder (ui : ℝ) (S : SSFields) (b a₀ a₁ : ℝ) where
  v : ℝ → ℝ
  tau : ℝ → ℝ
  radius_pos : 0 < b
  initial_le : ui ≤ a₀
  ordered : a₀ ≤ a₁
  terminal_negative : a₁ < 0
  points : ∀ u ∈ Icc a₀ a₁, u < v u ∧ v u ≤ 0 ∧ S.r u (v u) = b
  smooth_v : ContDiffOn ℝ 1 v (Icc a₀ a₁)
  tangent : ∀ u ∈ Ioo a₀ a₁,
    HasDerivAt v (-S.nu u (v u) / S.lam u (v u)) u
  continuous_tau : ContinuousOn tau (Icc a₀ a₁)
  clock : ∀ a d, a₀ ≤ a → a ≤ d → d ≤ a₁ →
    IntervalPrimitive tau (fun u => -S.nu u (v u)) a d

/-- The normalized outgoing datum on a cylinder; paper `e1a0fd5`,
`eq:boundary-energy-stability`, lines 700–706. -/
@[expose] noncomputable def cylinderDatum {ui b a₀ a₁ : ℝ} (S : SSFields)
    (c : DecayCylinder ui S b a₀ a₁) (u : ℝ) : ℝ := S.dvpsi u (c.v u) / S.lam u (c.v u)

/-- The scalar trace on a cylinder; paper `e1a0fd5`,
`eq:cylinder-scalar-derivative`, lines 718–721. -/
@[expose] noncomputable def cylinderPhi {ui b a₀ a₁ : ℝ} (S : SSFields)
    (c : DecayCylinder ui S b a₀ a₁) (u : ℝ) : ℝ := S.phi u (c.v u)

/-- Cylinder boundary energy using the shared energy definition; paper
`e1a0fd5`, `eq:boundary-energy`, lines 676–681. -/
@[expose] noncomputable def decayCylinderEnergy {ui b a₀ a₁ : ℝ} (S : SSFields)
    (c : DecayCylinder ui S b a₀ a₁) (u : ℝ) : ℝ :=
  boundaryEnergy b (S.m u (c.v u)) (cylinderDatum S c u - cylinderPhi S c u)

/-- Real total variation of the cylinder datum (finite under Lemma 2.4's AC).
Paper `e1a0fd5`, `eq:boundary-energy-stability`, lines 700–706. -/
@[expose] noncomputable def cylinderVariation {ui b a₀ a₁ : ℝ} (S : SSFields)
    (c : DecayCylinder ui S b a₀ a₁) (a d : ℝ) : ℝ :=
  (eVariationOn (cylinderDatum S c) (Icc a d)).toReal

/-- Lemma 2.4: AC traces, all energy comparisons, exact balance in the original u parameter, and
stability on every subinterval. Paper `e1a0fd5`, `lem:boundary-energy-identity`, lines 682–707, with
the regular cylinder condition. -/
@[expose] def Lemma24Statement (ui : ℝ) (S : SSFields) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ b a₀ a₁ (c : DecayCylinder ui S b a₀ a₁),
    (∀ u ∈ Icc a₀ a₁, S.m u (c.v u) ≤ decayCylinderEnergy S c u ∧
      b / 2 * (cylinderDatum S c u - cylinderPhi S c u) ^ 2 ≤ decayCylinderEnergy S c u ∧
      decayCylinderEnergy S c u ≤ C * b) ∧
    AbsolutelyContinuousOnInterval (fun u => S.m u (c.v u)) a₀ a₁ ∧
    AbsolutelyContinuousOnInterval (cylinderPhi S c) a₀ a₁ ∧
    AbsolutelyContinuousOnInterval (cylinderDatum S c) a₀ a₁ ∧
    AbsolutelyContinuousOnInterval (decayCylinderEnergy S c) a₀ a₁ ∧
    (∀ᵐ u ∂volume, u ∈ Ioo a₀ a₁ →
      deriv (decayCylinderEnergy S c) u + b ^ 2 / 2 * deriv (cylinderPhi S c) u ^ 2 /
        (-S.nu u (c.v u)) =
      b * (cylinderDatum S c u - cylinderPhi S c u) * deriv (cylinderDatum S c) u) ∧
    (∀ a d, a₀ ≤ a → a ≤ d → d ≤ a₁ →
      Real.sqrt (decayCylinderEnergy S c d) ≤ Real.sqrt (decayCylinderEnergy S c a) +
        Real.sqrt (b / 2) * cylinderVariation S c a d)

/-- Lemma 2.5, with its three constants explicit, selected before cylinder
variables. Paper `e1a0fd5`, `lem:boundary-contraction`, lines 751–761. -/
@[expose] def Lemma25Statement (ui : ℝ) (S : SSFields) (H C rho : ℝ) : Prop :=
  0 < H ∧ 0 < C ∧ 0 < rho ∧ rho < 1 ∧
  ∀ b a₀ a₁ (c : DecayCylinder ui S b a₀ a₁) a d,
    a₀ ≤ a → a ≤ d → d ≤ a₁ → c.tau d - c.tau a = H * b →
    decayCylinderEnergy S c d ≤ rho * decayCylinderEnergy S c a +
      C * b * cylinderVariation S c a d ^ 2

/-- Lemma 2.6 with fixed geometric K and observability H, uniformly in ε. The late-variation
estimate requires existence on I and bounds only in its past exterior. Paper `e1a0fd5`,
`lem:late-cylinder-variation`, lines 791–801. -/
@[expose] def Lemma26Statement (ui : ℝ) (S : SSFields) (K H : ℝ) : Prop :=
  ∃ D : ℝ, 0 < D ∧ ∀ eps b u₀ a₀ a₁ (c : DecayCylinder ui S b a₀ a₁),
    0 < eps → eps ≤ 1 → ui ≤ u₀ → u₀ ≤ a₀ →
    (∀ u v, (u, v) ∈ pastTriangle ui → u₀ ≤ u → u ≤ a₁ → b ≤ S.r u v →
      S.mu u v ≤ eps) → initialACTail ui S u₀ ≤ eps →
    K * b / eps ≤ a₀ - u₀ → c.tau a₁ - c.tau a₀ ≤ H * b →
    eVariationOn (cylinderDatum S c) (Icc a₀ a₁) ≤ ENNReal.ofReal (D * eps)

/-- The regular cylinder geometry and K facts, including a terminal intersection. Paper `e1a0fd5`,
lines 664–675 and 742–749, `eq:boundary-travel-time`. -/
@[expose] def CylinderGeometryStatement (ui : ℝ) (S : SSFields) (K : ℝ) : Prop :=
  1 ≤ K ∧
  (∀ u v, (u, v) ∈ pastTriangle ui →
    K⁻¹ ≤ S.lam u v ∧ S.lam u v ≤ 1 ∧ K⁻¹ ≤ 1 - S.mu u v ∧ K⁻¹ ≤ -S.nu u v) ∧
  (∀ a d v, ui ≤ a → a ≤ d → d < 0 → d ≤ v → v ≤ 0 →
    S.lam a v / S.lam d v ≤ K) ∧
  (∀ b a₀ a₁, 0 < b → ui ≤ a₀ → a₀ ≤ a₁ → a₁ < 0 →
    (∀ u ∈ Icc a₀ a₁, b ≤ S.r u 0) → Nonempty (DecayCylinder ui S b a₀ a₁)) ∧
  (∀ b a₀ a₁ (c : DecayCylinder ui S b a₀ a₁) a d,
    a₀ ≤ a → a ≤ d → d ≤ a₁ →
    c.tau d - c.tau a ≤ c.v d - c.v a ∧ c.v d - d ≤ K * b)

end AcExtensionPrinciple

end
