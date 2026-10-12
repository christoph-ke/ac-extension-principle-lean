module

public import AcExtensionPrinciple.Frozen.GammaOf
public import AcExtensionPrinciple.Frozen.MassRatio
public import AcExtensionPrinciple.Frozen.VarkappaOf
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Pointwise derived quantities of the reduced system

Source: paper commit `e1a0fd5`, `equations.tex`
lines 49–65 (`eq:scalar-and-mass-ratio`, `eq:normalized-expansions`, `eq:varkappa`).

All quantities are functions of the point values of the primitive fields. They are used only
where `r > 0`, `λ > 0`, `ν < 0`, `0 ≤ μ < 1` (paper line 66). At `r = 0` Lean's `x / 0 = 0`
gives `μ = 0`, which matches the paper's convention of extending `μ` by zero at the regular
axis (line 275).
The frozen declarations of this file live in `AcExtensionPrinciple/Frozen/` (one per file).
-/

public section

namespace AcExtensionPrinciple

/-- `κ = λ / (1 - μ)` (`eq:normalized-expansions`). -/
@[expose] noncomputable def kappaOf (lam mu : ℝ) : ℝ := lam / (1 - mu)

/-- With the Hawking mass relation `1 - μ = -4λν/Ω²` (`eq:hawking-mass`), the two expressions
for `κ` in `eq:normalized-expansions` agree: `κ = -Ω²/(4ν)`. -/
theorem kappaOf_eq_of_hawking {lam nu mu Ω2 : ℝ} (hnu : nu ≠ 0) (hΩ : Ω2 ≠ 0)
    (hlam : lam ≠ 0) (hH : 1 - mu = -4 * lam * nu / Ω2) :
    kappaOf lam mu = -Ω2 / (4 * nu) := by
  unfold kappaOf
  rw [hH]
  field_simp

/-- With the Hawking mass relation, `γ = -Ω²/(4λ)` (`eq:normalized-expansions`). -/
theorem gammaOf_eq_of_hawking {lam nu mu Ω2 : ℝ} (hnu : nu ≠ 0) (hΩ : Ω2 ≠ 0)
    (hlam : lam ≠ 0) (hH : 1 - mu = -4 * lam * nu / Ω2) :
    gammaOf nu mu = -Ω2 / (4 * lam) := by
  unfold gammaOf
  rw [hH]
  field_simp

/-- `ϰ = 2m/r²` (`eq:varkappa`). -/
theorem varkappaOf_massRatio (r m : ℝ) : varkappaOf r (massRatio r m) = 2 * m / r ^ 2 := by
  unfold varkappaOf massRatio
  rw [div_div, sq]

end AcExtensionPrinciple

end
