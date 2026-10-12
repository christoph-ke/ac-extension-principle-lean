module

public import AcExtensionPrinciple.ScalarBound.StripCoefficients

/-!
# Stable rational coefficient comparisons

Paper commit `e1a0fd5`, `equations.tex`
lines 463–470, `eq:scalar-bound-strip-coefficient`.
-/

public section

namespace AcExtensionPrinciple

open Set

/-- Reciprocal radii differ by a width divided by the square of the
reference radius. Paper `e1a0fd5`, lines 463–468. -/
theorem scalar_reciprocal_radius_difference {r R d : ℝ}
    (hR : 0 < R) (hr : R / 2 ≤ r) (hd : 0 ≤ d) (hrr : |R - r| ≤ d) :
    |1 / r - 1 / R| ≤ 2 * d / R ^ 2 := by
  have hr0 : 0 < r := (by positivity : 0 < R / 2).trans_le hr
  have he : 1 / r - 1 / R = (R - r) / (r * R) := by field_simp
  rw [he, abs_div, abs_of_pos (mul_pos hr0 hR)]
  have hden : R ^ 2 / 2 ≤ r * R := by nlinarith
  exact (div_le_div₀ hd hrr (by positivity : 0 < R ^ 2 / 2) hden).trans_eq
    (by field_simp)

/-- The untrapped rational coefficient μ/(1−μ) is Lipschitz with constant
1/g² when both gaps are at least g. Paper `e1a0fd5`, lines 463–470. -/
theorem scalar_gap_coefficient_difference {mu mu₀ g : ℝ}
    (hg : 0 < g) (hgap : g ≤ 1 - mu) (hgap₀ : g ≤ 1 - mu₀) :
    |mu / (1 - mu) - mu₀ / (1 - mu₀)| ≤ |mu - mu₀| / g ^ 2 := by
  have hp := hg.trans_le hgap
  have hp₀ := hg.trans_le hgap₀
  have he : mu / (1 - mu) - mu₀ / (1 - mu₀) =
      (mu - mu₀) / ((1 - mu) * (1 - mu₀)) := by
    field_simp
    ring
  rw [he, abs_div, abs_of_pos (mul_pos hp hp₀)]
  have hd : g ^ 2 ≤ (1 - mu) * (1 - mu₀) := by
    simpa only [sq] using mul_le_mul hgap hgap₀ hg.le hp.le
  exact div_le_div₀ (abs_nonneg _) le_rfl (sq_pos_of_pos hg) hd

/-- The same coefficient lies in [0,1/g]. Paper `e1a0fd5`, lines 463–470. -/
theorem scalar_gap_coefficient_bounds {mu g : ℝ}
    (hg : 0 < g) (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1) (hgap : g ≤ 1 - mu) :
    0 ≤ mu / (1 - mu) ∧ mu / (1 - mu) ≤ 1 / g := by
  exact ⟨div_nonneg hmu (hg.trans_le hgap).le,
    div_le_div₀ zero_le_one hmu1 hg hgap⟩

/-- A three-term decomposition compares γϰ without ever dividing by ν.
Paper `e1a0fd5`, `eq:scalar-bound-strip-coefficient`, lines 466–470. -/
theorem scalar_transport_coefficient_difference {mu mu₀ nu nu₀ r R d g : ℝ}
    (hR : 0 < R) (hr : R / 2 ≤ r) (hd : 0 ≤ d) (hrr : |R - r| ≤ d)
    (hg : 0 < g) (hgap : g ≤ 1 - mu) (hgap₀ : g ≤ 1 - mu₀)
    (hmu : 0 ≤ mu ∧ mu ≤ 1) (hmu₀ : 0 ≤ mu₀ ∧ mu₀ ≤ 1) :
    |nu * (mu / (1 - mu)) / r - nu₀ * (mu₀ / (1 - mu₀)) / R| ≤
      |nu - nu₀| * (2 / (g * R)) +
        |nu₀| * |mu - mu₀| * (2 / (g ^ 2 * R)) +
        |nu₀| * d * (2 / (g * R ^ 2)) := by
  let A := mu / (1 - mu)
  let A₀ := mu₀ / (1 - mu₀)
  have hA := scalar_gap_coefficient_bounds hg hmu.1 hmu.2 hgap
  have hA₀ := scalar_gap_coefficient_bounds hg hmu₀.1 hmu₀.2 hgap₀
  have hr0 : 0 < r := (by positivity : 0 < R / 2).trans_le hr
  have he : nu * A / r - nu₀ * A₀ / R =
      (nu - nu₀) * (A / r) + nu₀ * ((A - A₀) / r) + nu₀ * A₀ * (1 / r - 1 / R) := by
    ring
  change |nu * A / r - nu₀ * A₀ / R| ≤ _
  rw [he]
  have hAr : |A / r| ≤ 2 / (g * R) := by
    rw [abs_div, abs_of_nonneg hA.1, abs_of_pos hr0]
    exact (div_le_div₀ (by positivity : 0 ≤ 1 / g) hA.2
      (by positivity : 0 < R / 2) hr).trans_eq (by field_simp)
  have hAdr : |(A - A₀) / r| ≤ |mu - mu₀| * (2 / (g ^ 2 * R)) := by
    rw [abs_div, abs_of_pos hr0]
    exact (div_le_div₀ (by positivity : 0 ≤ |mu - mu₀| / g ^ 2)
      (scalar_gap_coefficient_difference hg hgap hgap₀)
      (by positivity : 0 < R / 2) hr).trans_eq (by field_simp)
  have hlast : |nu₀ * A₀ * (1 / r - 1 / R)| ≤ |nu₀| * d * (2 / (g * R ^ 2)) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hA₀.1]
    calc
      _ ≤ |nu₀| * (1 / g) * (2 * d / R ^ 2) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left hA₀.2 (abs_nonneg _))
          (scalar_reciprocal_radius_difference hR hr hd hrr) (abs_nonneg _)
          (mul_nonneg (abs_nonneg _) (by positivity))
      _ = _ := by ring
  calc
    _ ≤ |(nu - nu₀) * (A / r)| + |nu₀ * ((A - A₀) / r)| +
        |nu₀ * A₀ * (1 / r - 1 / R)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ |nu - nu₀| * (2 / (g * R)) +
        |nu₀| * (|mu - mu₀| * (2 / (g ^ 2 * R))) +
        |nu₀| * d * (2 / (g * R ^ 2)) := by
      rw [abs_mul, abs_mul]
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left hAr (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hAdr (abs_nonneg _))) hlast
    _ = _ := by ring

/-- Explicit comparison constant for γϰ; it depends only on blueshift
and the geometric gap. Paper `e1a0fd5`, lines 466–470. -/
@[expose] noncomputable def scalarStripCoefficientConstant (ui : ℝ) (S : SSFields) (g : ℝ) : ℝ :=
  (4 + 2 * (8 / Real.exp (-Bstar ui S) + 2)) / g ^ 2 + 2 / g

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The γϰ difference has precisely the n₀ F² d/r₀² scaling claimed in
the paper, with an explicit constant independent of ν₀ and all strip
parameters. The gap premise is supplied by G2.
Paper `e1a0fd5`, `eq:scalar-bound-strip-coefficient`, lines 466–470. -/
theorem scalar_strip_coefficient_difference {u a b F g : ℝ}
    (hu : ui ≤ u) (hu0 : u < 0) (hua : u < a) (hab : a ≤ b) (hb0 : b ≤ 0)
    (hg : 0 < g) (hF : 1 ≤ F) (hwidth : b - a ≤ S.r u b / 2)
    (hgap : ∀ s ∈ Icc a b, g ≤ 1 - S.mu u s)
    (htheta : ∀ s ∈ Icc a b, |S.theta u s| ≤ 2 * F) :
    |S.gamma u a * S.varkappa u a - S.gamma u b * S.varkappa u b| ≤
      scalarStripCoefficientConstant ui S g * (-S.nu u b) * F ^ 2 * (b - a) / S.r u b ^ 2 := by
  have hp : (u, b) ∈ pastTriangle ui := ⟨hu, hu0, (hua.trans_le hab).le, hb0⟩
  have hpA : (u, a) ∈ pastTriangle ui := ⟨hu, hu0, hua.le, hab.trans hb0⟩
  have hr := h.r_pos hp (hua.trans_le hab)
  have hn := neg_pos.mpr (h.nu_neg hp)
  have hR := h.scalar_strip_radius hu hu0 hua hab hb0 hwidth
  have hRd := h.scalar_radius_difference hu hu0 hua.le hab hb0
  have hF2 : 1 ≤ F ^ 2 := by nlinarith
  have hN := h.scalar_strip_nu_difference hu hu0 hua hab hb0 hg hwidth hgap
  have hN2 : |S.nu u a - S.nu u b| ≤
      (2 / g) * (-S.nu u b) * F ^ 2 * (b - a) / S.r u b := by
    calc
      _ ≤ _ := hN
      _ ≤ ((2 / g) * (-S.nu u b) * (b - a) / S.r u b) * F ^ 2 :=
        le_mul_of_one_le_right (by positivity) hF2
      _ = _ := by ring
  have hM := h.scalar_strip_mu_difference hu hu0 hua hab hb0 hF hwidth htheta
  have hmu := h.mu_bounds hpA
  have hmu₀ := h.mu_bounds hp
  have ht := scalar_transport_coefficient_difference hr hR.1 (sub_nonneg.mpr hab)
    (by rw [abs_of_nonneg hRd.1]; exact hRd.2) hg (hgap a (left_mem_Icc.mpr hab))
    (hgap b (right_mem_Icc.mpr hab)) ⟨hmu.1, hmu.2.le⟩ ⟨hmu₀.1, hmu₀.2.le⟩
    (nu := S.nu u a) (nu₀ := S.nu u b)
  have he (s : ℝ) : S.gamma u s * S.varkappa u s =
      S.nu u s * (S.mu u s / (1 - S.mu u s)) / S.r u s := by
    unfold SSFields.gamma gammaOf SSFields.varkappa varkappaOf
    ring
  rw [he a, he b]
  rw [abs_of_neg (h.nu_neg hp)] at ht
  calc
    _ ≤ _ := ht
    _ ≤ ((2 / g) * (-S.nu u b) * F ^ 2 * (b - a) / S.r u b) * (2 / (g * S.r u b)) +
        (-S.nu u b) * ((8 / Real.exp (-Bstar ui S) + 2) * F ^ 2 * (b - a) / S.r u b) *
          (2 / (g ^ 2 * S.r u b)) +
        (-S.nu u b) * (b - a) * (2 / (g * S.r u b ^ 2)) := by
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_right hN2 (by positivity))
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM hn.le) (by positivity))) le_rfl
    _ ≤ ((2 / g) * (-S.nu u b) * F ^ 2 * (b - a) / S.r u b) * (2 / (g * S.r u b)) +
        (-S.nu u b) * ((8 / Real.exp (-Bstar ui S) + 2) * F ^ 2 * (b - a) / S.r u b) *
          (2 / (g ^ 2 * S.r u b)) +
        ((-S.nu u b) * (b - a) * (2 / (g * S.r u b ^ 2))) * F ^ 2 := by
      exact add_le_add le_rfl (le_mul_of_one_le_right (by positivity) hF2)
    _ = _ := by unfold scalarStripCoefficientConstant; ring

end StandingFull

end AcExtensionPrinciple

end
