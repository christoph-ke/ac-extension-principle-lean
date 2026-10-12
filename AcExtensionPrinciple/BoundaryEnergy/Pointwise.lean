module

public import AcExtensionPrinciple.Reduced.Quantities
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Tactic

/-!
# Boundary energy: pointwise identities

Source: paper commit `e1a0fd5`, `equations.tex` lines 661–729,
`lem:boundary-energy-identity`. The cylinder chain rule is supplied as derivative data.
-/

public section

namespace AcExtensionPrinciple

/-- Cylinder mass derivative; paper `e1a0fd5`, `eq:cylinder-mass-balance`, lines 709–716. -/
@[expose] noncomputable def cylinderMassDerivative (b lam nu m phiU phiV : ℝ) : ℝ :=
  b ^ 2 / (2 * gammaOf nu (massRatio b m)) * phiU ^ 2 -
    (nu / lam) * (b ^ 2 / (2 * kappaOf lam (massRatio b m))) * phiV ^ 2

/-- Cylinder scalar derivative; paper `e1a0fd5`, `eq:cylinder-scalar-derivative`, lines 716–719. -/
@[expose] noncomputable def cylinderScalarDerivative (lam nu phiU phiV : ℝ) : ℝ :=
  phiU - (nu / lam) * phiV

/-- Boundary energy; paper `e1a0fd5`, `eq:boundary-energy`, lines 674–679. -/
@[expose] noncomputable def boundaryEnergy (b m A : ℝ) : ℝ :=
  (b / 2) * (A ^ 2 - Real.log (1 - massRatio b m))

/-- Normalized mass balance; paper `e1a0fd5`, `eq:cylinder-mass-balance`, lines 709–716. -/
theorem cylinder_mass_balance {b lam nu m phiU phiV : ℝ}
    (hlam : 0 < lam) (hnu : nu < 0) (hmu : massRatio b m < 1) :
    cylinderMassDerivative b lam nu m phiU phiV / (1 - massRatio b m) =
      (b ^ 2 / 2) * (phiU ^ 2 / nu - (nu / lam ^ 2) * phiV ^ 2) := by
  have hn := ne_of_lt hnu
  have hl := ne_of_gt hlam
  have hm : 1 - massRatio b m ≠ 0 := ne_of_gt (sub_pos.mpr hmu)
  unfold cylinderMassDerivative gammaOf kappaOf
  field_simp

/-- Logarithmic energy balance in cylinder time; paper `e1a0fd5`, lines 721–725. -/
theorem cylinder_log_energy_balance {b lam nu m phiU phiV : ℝ}
    (hlam : 0 < lam) (hnu : nu < 0) (hmu : massRatio b m < 1) :
    (1 / (-nu)) * (cylinderMassDerivative b lam nu m phiU phiV /
      (1 - massRatio b m)) =
      b * ((b / lam) * phiV) * (cylinderScalarDerivative lam nu phiU phiV / (-nu)) -
        (b ^ 2 / 2) * (cylinderScalarDerivative lam nu phiU phiV / (-nu)) ^ 2 := by
  rw [cylinder_mass_balance hlam hnu hmu]
  unfold cylinderScalarDerivative
  have hn := ne_of_lt hnu
  have hl := ne_of_gt hlam
  field_simp
  ring

/-- Exact energy balance in the `u` parameter; paper `e1a0fd5`, `eq:boundary-energy-balance`, lines
690–697 and 726–729. -/
theorem boundary_energy_balance {b lam nu m phiU phiV P' : ℝ}
    (hlam : 0 < lam) (hnu : nu < 0) (hmu : massRatio b m < 1) :
    b * ((b / lam) * phiV) * (P' - cylinderScalarDerivative lam nu phiU phiV) +
      cylinderMassDerivative b lam nu m phiU phiV / (1 - massRatio b m) +
      (b ^ 2 / 2) * (cylinderScalarDerivative lam nu phiU phiV) ^ 2 / (-nu) =
      b * ((b / lam) * phiV) * P' := by
  rw [cylinder_mass_balance hlam hnu hmu]
  unfold cylinderScalarDerivative
  have hn := ne_of_lt hnu
  have hl := ne_of_gt hlam
  field_simp
  ring

/-- The energy derivative for actual cylinder traces; paper `e1a0fd5`, `eq:boundary-energy-balance`,
lines 690–697 and 709–729. The value relation `P - φ = (b/λ)∂ᵥφ` is the paper's `∂ᵥψ/λ = φ +
(b/λ)∂ᵥφ`. -/
theorem hasDerivAt_boundaryEnergy {b lam nu phiU phiV P' u : ℝ}
    {mB phiB PB : ℝ → ℝ} (hb : 0 < b) (hlam : 0 < lam) (hnu : nu < 0)
    (hmu : massRatio b (mB u) < 1)
    (hA : PB u - phiB u = (b / lam) * phiV)
    (hm : HasDerivAt mB (cylinderMassDerivative b lam nu (mB u) phiU phiV) u)
    (hphi : HasDerivAt phiB (cylinderScalarDerivative lam nu phiU phiV) u)
    (hP : HasDerivAt PB P' u) :
    HasDerivAt (fun s ↦ boundaryEnergy b (mB s) (PB s - phiB s))
      (b * ((b / lam) * phiV) * P' -
        (b ^ 2 / 2) * (cylinderScalarDerivative lam nu phiU phiV) ^ 2 / (-nu)) u := by
  have hb0 := ne_of_gt hb
  have hm0 : 1 - massRatio b (mB u) ≠ 0 := ne_of_gt (sub_pos.mpr hmu)
  have hlog := ((hasDerivAt_const u (1 : ℝ)).sub
    ((hm.const_mul 2).div_const b)).log hm0
  have hder := (((hP.sub hphi).pow 2).sub hlog).const_mul (b / 2)
  have heq : (b / 2) *
      (2 * (PB u - phiB u) ^ (2 - 1) * (P' - cylinderScalarDerivative lam nu phiU phiV) -
        (0 - (2 * cylinderMassDerivative b lam nu (mB u) phiU phiV) / b) /
          (1 - 2 * mB u / b)) =
      b * ((b / lam) * phiV) * P' -
        (b ^ 2 / 2) * (cylinderScalarDerivative lam nu phiU phiV) ^ 2 / (-nu) := by
    have hbal := boundary_energy_balance (phiU := phiU) (phiV := phiV) (P' := P') hlam hnu hmu
    rw [show PB u - phiB u = (b / lam) * phiV from hA]
    simp only [Nat.reduceSub, pow_one]
    have halg : (b / 2) *
        (2 * ((b / lam) * phiV) * (P' - cylinderScalarDerivative lam nu phiU phiV) -
          (0 - 2 * cylinderMassDerivative b lam nu (mB u) phiU phiV / b) /
            (1 - 2 * mB u / b)) =
        b * ((b / lam) * phiV) * (P' - cylinderScalarDerivative lam nu phiU phiV) +
          cylinderMassDerivative b lam nu (mB u) phiU phiV /
            (1 - massRatio b (mB u)) := by
      unfold massRatio
      field_simp
      ring
    rw [halg]
    linarith
  convert hder using 1
  · rfl
  · exact heq.symm

/-- Energy controls mass; paper `e1a0fd5`, `eq:boundary-energy-comparison`, lines 684–688. -/
theorem mass_le_boundaryEnergy {b m A : ℝ} (hb : 0 < b)
    (hmu : massRatio b m < 1) : m ≤ boundaryEnergy b m A := by
  have hlog := Real.log_le_sub_one_of_pos (sub_pos.mpr hmu)
  have hid : (b / 2) * massRatio b m = m := by
    unfold massRatio
    field_simp
  unfold boundaryEnergy
  nlinarith [sq_nonneg A]

/-- Energy controls the scalar square; paper `e1a0fd5`, `eq:boundary-energy-comparison`, lines
684–688. -/
theorem scalar_square_le_boundaryEnergy {b m A : ℝ} (hb : 0 < b)
    (hmu0 : 0 ≤ massRatio b m) (hmu : massRatio b m < 1) :
    (b / 2) * A ^ 2 ≤ boundaryEnergy b m A := by
  have hlog := Real.log_le_sub_one_of_pos (sub_pos.mpr hmu)
  unfold boundaryEnergy
  nlinarith

end AcExtensionPrinciple

end
