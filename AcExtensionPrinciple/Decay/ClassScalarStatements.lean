module

public import AcExtensionPrinciple.Solution.StandingFull
public import AcExtensionPrinciple.ACDatum.InitialTail

/-!
# Scalar statements for the decay-chain assembly

This module records the scalar statements of paper `e1a0fd5`,
`equations.tex` lines 537–659, 835–846 and 931–989.
The statements use the existing derivative fields,
including the regular-axis values prescribed by the corrected solution class.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory

/-- Lemma 2.3, exactly the pointwise AC interpolation conclusion at positive
radius, with a single uniform constant. Paper `e1a0fd5`, `lem:ac-interpolation`,
`eq:ac-interpolation`, lines 608–616. -/
@[expose] def Lemma23Statement (ui : ℝ) (S : SSFields) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ u v : ℝ, (u, v) ∈ pastTriangle ui → 0 < S.r u v →
    |S.r u v / S.lam u v * S.dvphi u v| ^ 3 ≤
      C * (S.mu u v + initialACTail ui S u ^ 3)

/-- Epsilon–delta form of Proposition 2.7. Paper `e1a0fd5`,
`prop:uniform-mass-decay`, `eq:uniform-mass-decay`, lines 835–846. -/
@[expose] def UniformMassDecayStatement (ui : ℝ) (S : SSFields) : Prop :=
  ∀ eps : ℝ, 0 < eps → ∃ a : ℝ, ui ≤ a ∧ a < 0 ∧
    ∀ u v : ℝ, a ≤ u → u < 0 → u ≤ v → v ≤ 0 → |S.mu u v| < eps

/-- Epsilon–delta form of the common scalar limit, including the axis as in
the paper's closed-cone supremum. Paper `e1a0fd5`, `prop:common-scalar-limit`,
`eq:common-scalar-limit`, lines 931–942. -/
@[expose] def CommonScalarLimitStatement (ui : ℝ) (S : SSFields) : Prop :=
  ∃ L : ℝ, ∀ eps : ℝ, 0 < eps → ∃ a : ℝ, ui ≤ a ∧ a < 0 ∧
    ∀ u v : ℝ, a ≤ u → u < 0 → u ≤ v → v ≤ 0 →
      |S.dvpsi u v / S.lam u v - L| + |S.phi u v - L| +
        |S.dupsi u v / S.nu u v - L| < eps

/-- Epsilon–delta form of vanishing normalized scalar amplitudes.
Paper `e1a0fd5`, `eq:normalized-scalar-amplitudes-vanish`, lines 943–949. -/
@[expose] def NormalizedScalarAmplitudesVanishStatement (ui : ℝ) (S : SSFields) : Prop :=
  ∀ eps : ℝ, 0 < eps → ∃ a : ℝ, ui ≤ a ∧ a < 0 ∧
    ∀ u v : ℝ, a ≤ u → u < 0 → u ≤ v → v ≤ 0 →
      |S.r u v / S.lam u v * S.dvphi u v| +
        |S.r u v / S.nu u v * S.duphi u v| < eps

end AcExtensionPrinciple

end
