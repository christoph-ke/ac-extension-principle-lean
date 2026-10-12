module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic

/-!
# Numerical steps in the cylinder argument

Paper `e1a0fd5`, `equations.tex` lines 814 and 893–924.
-/

public section

namespace AcExtensionPrinciple

open Filter
open scoped Topology

/-- Waiting `Kb/ε` suffices, and in fact gives the sharper `ε/(1+ε)`;
paper `e1a0fd5`, `equations.tex` line 814 (`eq:remainder-dilution`). -/
theorem cylinder_remainder_dilution {b K eps dt R : ℝ}
    (hb : 0 < b) (hK : 0 < K) (heps : 0 < eps)
    (hR : b + K⁻¹ * dt ≤ R) (hwait : K * b / eps ≤ dt) :
    b / R ≤ eps / (1 + eps) ∧ b / R ≤ eps := by
  have hdt : b / eps ≤ K⁻¹ * dt := by
    have hm := mul_le_mul_of_nonneg_left hwait (inv_nonneg.mpr hK.le)
    have heq : K⁻¹ * (K * b / eps) = b / eps := by field_simp
    rwa [heq] at hm
  have hR0 : 0 < R := by linarith [div_pos hb heps]
  have hprod : b * (1 + eps) ≤ eps * R := by
    have hh := (div_le_iff₀ heps).mp (hdt.trans (by linarith : K⁻¹ * dt ≤ R - b))
    nlinarith
  have hsharp : b / R ≤ eps / (1 + eps) := by
    apply (div_le_div_iff₀ hR0 (by positivity)).mpr
    exact hprod
  refine ⟨hsharp, hsharp.trans ?_⟩
  apply (div_le_iff₀ (by positivity : 0 < 1 + eps)).mpr
  nlinarith [sq_nonneg eps]

/-- Squaring the stability estimate: the partial interval costs at most
`b D² ε²`; paper `e1a0fd5`, lines 893–905 (`eq:late-cylinder-energy-smallness`). -/
theorem energy_after_partial_interval {E E0 b C D eps q : ℝ}
    (hE : 0 ≤ E) (hE0 : 0 ≤ E0) (hb : 0 ≤ b) (hD : 0 ≤ D) (heps : 0 ≤ eps)
    (hdecay : E0 ≤ C * (q + eps ^ 2) * b)
    (hstab : Real.sqrt E ≤ Real.sqrt E0 + Real.sqrt (b / 2) * D * eps) :
    E ≤ (2 * C * q + (2 * C + D ^ 2) * eps ^ 2) * b := by
  have hsE := Real.sq_sqrt hE
  have hsE0 := Real.sq_sqrt hE0
  have hsb := Real.sq_sqrt (show 0 ≤ b / 2 by positivity)
  have hright : 0 ≤ Real.sqrt E0 + Real.sqrt (b / 2) * D * eps := by positivity
  have hsq := mul_self_le_mul_self (Real.sqrt_nonneg E) hstab
  have hcross := sq_nonneg (Real.sqrt E0 - Real.sqrt (b / 2) * D * eps)
  have hterm : (Real.sqrt (b / 2) * D * eps) ^ 2 = b / 2 * D ^ 2 * eps ^ 2 := by
    rw [mul_pow, mul_pow, hsb]
  have hyoung : E ≤ 2 * E0 + b * D ^ 2 * eps ^ 2 := by
    nlinarith only [hsq, hcross, hsE, hsE0, hterm]
  nlinarith only [hyoung, hdecay]

/-- Explicit sufficient smallness: `(2C+D²) ε ≤ 1/16` and
`2C q ≤ ε/16`; paper `e1a0fd5`, lines 898–905. -/
theorem late_energy_small {E E0 b C D eps q : ℝ}
    (hE : 0 ≤ E) (hE0 : 0 ≤ E0) (hb : 0 ≤ b) (hD : 0 ≤ D) (heps : 0 ≤ eps)
    (hdecay : E0 ≤ C * (q + eps ^ 2) * b)
    (hstab : Real.sqrt E ≤ Real.sqrt E0 + Real.sqrt (b / 2) * D * eps)
    (hsmall : (2 * C + D ^ 2) * eps ≤ 1 / 16)
    (htransient : 2 * C * q ≤ eps / 16) : E ≤ eps * b / 8 := by
  have h := energy_after_partial_interval hE hE0 hb hD heps hdecay hstab
  have hs := mul_le_mul_of_nonneg_right hsmall heps
  have hc : 2 * C * q + (2 * C + D ^ 2) * eps ^ 2 ≤ eps / 8 := by nlinarith
  exact h.trans (by nlinarith [mul_le_mul_of_nonneg_right hc hb])

/-- Choose ε and N independently of b, with the above explicit conditions;
paper `e1a0fd5`, lines 898–905 (`eq:late-cylinder-energy-smallness`). -/
theorem exists_decay_parameters {C D rho : ℝ} (hC : 0 ≤ C)
    (hrho : 0 ≤ rho) (hrho1 : rho < 1) :
    ∃ eps : ℝ, 0 < eps ∧ eps ≤ 1 ∧ (2 * C + D ^ 2) * eps ≤ 1 / 16 ∧
      ∃ N : ℕ, ∀ k ≥ N, 2 * C * rho ^ k ≤ eps / 16 := by
  let eps : ℝ := 1 / (16 * (2 * C + D ^ 2 + 1))
  have hden : 0 < 16 * (2 * C + D ^ 2 + 1) := by positivity
  have heps : 0 < eps := div_pos zero_lt_one hden
  have heps1 : eps ≤ 1 := by
    dsimp [eps]
    apply (div_le_iff₀ hden).mpr
    nlinarith [sq_nonneg D]
  have hsmall : (2 * C + D ^ 2) * eps ≤ 1 / 16 := by
    dsimp [eps]
    rw [← mul_div_assoc, mul_one]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hlim : Tendsto (fun k : ℕ ↦ 2 * C * rho ^ k) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hrho hrho1).const_mul (2 * C)
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hlim.eventually (gt_mem_nhds (show 0 < eps / 16 by positivity)))
  exact ⟨eps, heps, heps1, hsmall, N, fun k hk ↦ (hN k hk).le⟩

/-- The bad-point lower bound contradicts late boundary energy smallness;
paper `e1a0fd5`, lines 918–924 (`eq:bad-point-mass-lower-bound`). -/
theorem bad_point_energy_contradiction {m E eps b : ℝ}
    (heps : 0 < eps) (hb : 0 < b) (hm : eps * b / 4 < m)
    (hmE : m ≤ E) (hE : E ≤ eps * b / 8) : False := by
  have hp : 0 < eps * b := mul_pos heps hb
  linarith

end AcExtensionPrinciple

end
