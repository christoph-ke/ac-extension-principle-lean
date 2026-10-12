module

public import AcExtensionPrinciple.GeometricBounds.Blueshift
public import AcExtensionPrinciple.Solution.Raychaudhuri
public import AcExtensionPrinciple.GeometricBounds.InitialGap

/-!
# Uniform κ and mass-gap bounds

Paper `e1a0fd5`, `eq:kappa-monotonicity-bound`
(lines 320–332). The upper constant uses the positive subtype-indexed
minimum on the initial cone.
-/

public section

namespace AcExtensionPrinciple.StandingFull

open Set

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- λ ≤ κ, including the regular axis where μ = 0.
Paper `e1a0fd5`, `eq:kappa-monotonicity-bound`, lines 320–328. -/
theorem lam_le_kappa {p : ℝ × ℝ} (hp : p ∈ pastTriangle ui) :
    S.lam p.1 p.2 ≤ S.kappa p.1 p.2 := by
  have hm := h.mu_bounds hp
  change S.lam p.1 p.2 ≤ S.lam p.1 p.2 / (1 - S.mu p.1 p.2)
  apply (le_div_iff₀ (sub_pos.mpr hm.2)).mpr
  nlinarith [mul_nonneg (h.lam_pos hp).le hm.1]

/-- The lower bound in G2, independent of the initial-gap encoding.
Paper `e1a0fd5`, `eq:kappa-monotonicity-bound`, lines 320–328. -/
theorem kappa_lower {p : ℝ × ℝ} (hp : p ∈ pastTriangle ui) :
    Real.exp (-Bstar ui S) ≤ S.kappa p.1 p.2 :=
  (h.lam_bounds hp).1.trans (h.lam_le_kappa hp)

/-- κ is bounded above by its initial value on each regular off-axis incoming segment.
Paper `e1a0fd5`, `eq:kappa-monotonicity-bound`, lines 320–328. -/
theorem kappa_le_initial {u v : ℝ} (hp : (u, v) ∈ pastTriangle ui) (huv : u < v) :
    S.kappa u v ≤ S.kappa ui v :=
  h.kappa_le_of_le hp.1 le_rfl hp.2.1 huv hp.2.2.2

/-- G2: the upper κ bound, including regular axis points and the terminal ray.
Paper `e1a0fd5`, `eq:kappa-monotonicity-bound`, lines 320–328. -/
theorem kappa_upper {p : ℝ × ℝ} (hp : p ∈ pastTriangle ui) :
    S.kappa p.1 p.2 ≤ 1 / initialGap ui S := by
  have hi : 1 ≤ 1 / initialGap ui S := by
    apply (le_div_iff₀ h.initialGap_pos).mpr
    simpa using h.initialGap_le_one
  rcases hp.2.2.1.eq_or_lt with he | he
  · have hmu := h.mu_axis ⟨hp.1, hp.2.1, rfl⟩
    have hk : S.kappa p.1 p.2 = S.lam p.1 p.2 := by
      simp [← he, SSFields.kappa, kappaOf, hmu]
    rw [hk]
    exact (h.lam_bounds hp).2.trans hi
  · have hv : p.2 ∈ Icc ui 0 := ⟨hp.1.trans hp.2.2.1, hp.2.2.2⟩
    calc
      S.kappa p.1 p.2 ≤ S.kappa ui p.2 := h.kappa_le_initial hp he
      _ = 1 / (1 - S.mu ui p.2) := by
        simp [SSFields.kappa, kappaOf, (h.initial_gauge p.2 hv).2]
      _ ≤ 1 / initialGap ui S :=
        one_div_le_one_div_of_le h.initialGap_pos (h.initialGap_le hv)

/-- G2: both explicit κ bounds on the whole past triangle.
Paper `e1a0fd5`, `eq:kappa-monotonicity-bound`. -/
theorem kappa_bounds {p : ℝ × ℝ} (hp : p ∈ pastTriangle ui) :
    Real.exp (-Bstar ui S) ≤ S.kappa p.1 p.2 ∧
      S.kappa p.1 p.2 ≤ 1 / initialGap ui S :=
  ⟨h.kappa_lower hp, h.kappa_upper hp⟩

/-- G2: the uniform gap from μ = 1, including the regular axis where μ = 0.
Paper `e1a0fd5`, `eq:gap-from-kappa`, lines 329–332. -/
theorem mass_gap_lower {p : ℝ × ℝ} (hp : p ∈ pastTriangle ui) :
    initialGap ui S * Real.exp (-Bstar ui S) ≤ 1 - S.mu p.1 p.2 := by
  have hg := sub_pos.mpr (h.mu_bounds hp).2
  have hk := h.kappa_upper hp
  have hl := (h.lam_bounds hp).1
  change S.lam p.1 p.2 / (1 - S.mu p.1 p.2) ≤ 1 / initialGap ui S at hk
  have hb := (div_le_div_iff₀ hg h.initialGap_pos).mp hk
  nlinarith [mul_le_mul_of_nonneg_left hl h.initialGap_pos.le]

end AcExtensionPrinciple.StandingFull

end
