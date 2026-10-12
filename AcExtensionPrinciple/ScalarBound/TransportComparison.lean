module

public import AcExtensionPrinciple.ScalarBound.LambdaComparison

/-!
# Comparing incoming scalar derivatives and θ transport

Paper commit `e1a0fd5`, `equations.tex`
lines 483–496, `eq:scalar-bound-incoming-comparison` and
`eq:scalar-bound-transport-comparison`.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory

/-- Dividing the amplitude comparison by comparable radii.
Paper `e1a0fd5`, `eq:scalar-bound-incoming-comparison`, lines 483–488. -/
theorem scalar_quotient_difference {z z₀ r R d : ℝ}
    (hR : 0 < R) (hr : R / 2 ≤ r) (hd : 0 ≤ d) (hrr : |R - r| ≤ d) :
    |z / r - z₀ / R| ≤ (2 / R) * |z - z₀| + (2 * d / R) * |z₀ / R| := by
  have hr0 : 0 < r := (by positivity : 0 < R / 2).trans_le hr
  have he : z / r - z₀ / R = (z - z₀) / r + z₀ * (1 / r - 1 / R) := by ring
  rw [he]
  calc
    _ ≤ |(z - z₀) / r| + |z₀ * (1 / r - 1 / R)| := abs_add_le _ _
    _ ≤ |z - z₀| / (R / 2) + |z₀| * (2 * d / R ^ 2) := by
      rw [abs_div, abs_of_pos hr0, abs_mul]
      exact add_le_add (div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hr)
        (mul_le_mul_of_nonneg_left (scalar_reciprocal_radius_difference hR hr hd hrr) (abs_nonneg _))
    _ = _ := by rw [abs_div, abs_of_pos hR]; field_simp

/-- Multiplication by λ ≤ 1 keeps the scalar-derivative difference bound.
Paper `e1a0fd5`, `eq:scalar-bound-transport-comparison`, lines 490–496. -/
theorem scalar_product_difference {lam lam₀ p p₀ : ℝ} (hlam : |lam| ≤ 1) :
    |lam * p - lam₀ * p₀| ≤ |p - p₀| + |lam - lam₀| * |p₀| := by
  have he : lam * p - lam₀ * p₀ = lam * (p - p₀) + (lam - lam₀) * p₀ := by ring
  rw [he]
  exact (abs_add_le _ _).trans (by
    rw [abs_mul, abs_mul]
    simpa only [one_mul] using add_le_add
      (mul_le_mul_of_nonneg_right hlam (abs_nonneg (p - p₀)))
      (le_refl (|lam - lam₀| * |p₀|)))

/-- Explicit transport-difference constant. Paper `e1a0fd5`,
`eq:scalar-bound-transport-comparison`, lines 490–496. -/
@[expose] noncomputable def scalarStripTransportConstant (ui : ℝ) (S : SSFields) (g : ℝ) : ℝ :=
  scalarStripCoefficientConstant ui S g + 10

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Incoming scalar-derivative comparison on the bootstrapped strip.
Paper `e1a0fd5`, `eq:scalar-bound-incoming-comparison`, lines 483–488. -/
theorem scalar_strip_duphi_difference {u a b F : ℝ}
    (hu : ui ≤ u) (hu0 : u < 0) (hua : u < a) (hab : a ≤ b) (hb0 : b ≤ 0)
    (hF : 0 ≤ F) (hwidth : b - a ≤ S.r u b / 2)
    (htheta : ∀ s ∈ Icc a b, |S.theta u s| ≤ 2 * F) :
    |S.duphi u a - S.duphi u b| ≤
      8 * F * (-S.nu u b) * (b - a) / S.r u b ^ 2 +
        (2 * (b - a) / S.r u b) * |S.duphi u b| := by
  have hp : (u, b) ∈ pastTriangle ui := ⟨hu, hu0, (hua.trans_le hab).le, hb0⟩
  have hd := h.scalar_radius_difference hu hu0 hua.le hab hb0
  have hZ := h.scalar_strip_zeta_difference hu hu0 hua hab hb0 hF hwidth htheta
  have ht := scalar_quotient_difference (h.r_pos hp (hua.trans_le hab))
    (h.scalar_strip_radius hu hu0 hua hab hb0 hwidth).1 (sub_nonneg.mpr hab)
    (by rw [abs_of_nonneg hd.1]; exact hd.2) (z := S.zeta u a) (z₀ := S.zeta u b)
  change |S.duphi u a - S.duphi u b| ≤ (2 / S.r u b) * |S.zeta u a - S.zeta u b| +
    (2 * (b - a) / S.r u b) * |S.duphi u b| at ht
  calc
    _ ≤ _ := ht
    _ ≤ (2 / S.r u b) * (4 * F * (-S.nu u b) * (b - a) / S.r u b) +
        (2 * (b - a) / S.r u b) * |S.duphi u b| := by
      exact add_le_add (mul_le_mul_of_nonneg_left hZ
        (div_nonneg (by norm_num) (h.r_pos hp (hua.trans_le hab)).le)) le_rfl
    _ = _ := by ring

/-- The θ-transport difference has an explicit uniform constant.
The gap premise is discharged by G2; the amplitude premise is the
bootstrap. Paper `e1a0fd5`, `eq:scalar-bound-transport-comparison`, lines 490–496. -/
theorem scalar_strip_transport_difference {U a b F g u : ℝ}
    (hU : ui ≤ U) (hUa : U < a) (hab : a ≤ b) (hb0 : b ≤ 0)
    (hg : 0 < g) (hF : 1 ≤ F) (hwidth : b - a ≤ S.r U b / 2)
    (hgap : ∀ p ∈ Icc ui U ×ˢ Icc a b, g ≤ 1 - S.mu p.1 p.2)
    (htheta : ∀ p ∈ Icc ui U ×ˢ Icc a b, |S.theta p.1 p.2| ≤ 2 * F)
    (hu : u ∈ Icc ui U) :
    |-S.lam u a * S.duphi u a - (-S.lam u b * S.duphi u b)| ≤
      scalarStripTransportConstant ui S g * F ^ 2 * (b - a) *
        ((-S.nu u b) / S.r u b ^ 2 + |S.duphi u b| / S.r u b) := by
  have hU0 : U < 0 := hUa.trans_le (hab.trans hb0)
  have hua : u < a := hu.2.trans_lt hUa
  have hpA : (u, a) ∈ pastTriangle ui := ⟨hu.1, hu.2.trans_lt hU0, hua.le, hab.trans hb0⟩
  have hp : (u, b) ∈ pastTriangle ui := ⟨hu.1, hu.2.trans_lt hU0, (hua.trans_le hab).le, hb0⟩
  have hr := h.r_pos hp (hua.trans_le hab)
  have hn := neg_pos.mpr (h.nu_neg hp)
  have hmono := h.scalar_radius_in_antitone hu.2 hu.1 hU0 (hUa.le.trans hab) hb0
  have hD := h.scalar_strip_duphi_difference hu.1 hp.2.1 hua hab hb0 (by linarith)
    (by linarith) (fun s hs => htheta (u, s) ⟨hu, hs⟩)
  have hL := h.scalar_strip_lambda_difference hU hUa hab hb0 hg hF hwidth hgap htheta hu
  have hC : 0 ≤ scalarStripCoefficientConstant ui S g := by
    unfold scalarStripCoefficientConstant
    positivity
  have hP := scalar_product_difference (lam := -S.lam u a) (lam₀ := -S.lam u b)
    (p := S.duphi u a) (p₀ := S.duphi u b)
    (by rw [abs_neg, abs_of_pos (h.lam_pos hpA)]; exact (h.lam_bounds hpA).2)
  have hneg : -S.lam u a - (-S.lam u b) = -(S.lam u a - S.lam u b) := by ring
  rw [hneg, abs_neg] at hP
  have hF2 : F ≤ F ^ 2 := by nlinarith
  have hnum : 0 ≤ 8 * (-S.nu u b) * (b - a) / S.r u b ^ 2 := by positivity
  calc
    _ ≤ _ := hP
    _ ≤ 8 * F * (-S.nu u b) * (b - a) / S.r u b ^ 2 +
        (2 * (b - a) / S.r u b) * |S.duphi u b| +
        (scalarStripCoefficientConstant ui S g * F ^ 2 * (b - a) / S.r u b) * |S.duphi u b| :=
      add_le_add hD (mul_le_mul_of_nonneg_right hL (abs_nonneg _))
    _ ≤ 8 * F ^ 2 * (-S.nu u b) * (b - a) / S.r u b ^ 2 +
        (2 * F ^ 2 * (b - a) / S.r u b) * |S.duphi u b| +
        (scalarStripCoefficientConstant ui S g * F ^ 2 * (b - a) / S.r u b) * |S.duphi u b| := by
      gcongr <;> nlinarith
    _ ≤ _ := by
      unfold scalarStripTransportConstant
      have hnR : 0 ≤ (-S.nu u b) / S.r u b ^ 2 := by positivity
      have hpR : 0 ≤ |S.duphi u b| / S.r u b := by positivity
      have hbase : 0 ≤ F ^ 2 * (b - a) := mul_nonneg (sq_nonneg F) (sub_nonneg.mpr hab)
      have h₁ := mul_nonneg (mul_nonneg (by linarith : 0 ≤ scalarStripCoefficientConstant ui S g + 2) hbase) hnR
      have h₂ := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hbase) hpR
      have heDiff :
          (scalarStripCoefficientConstant ui S g + 10) * F ^ 2 * (b - a) *
            ((-S.nu u b) / S.r u b ^ 2 + |S.duphi u b| / S.r u b) -
          (8 * F ^ 2 * (-S.nu u b) * (b - a) / S.r u b ^ 2 +
            (2 * F ^ 2 * (b - a) / S.r u b) * |S.duphi u b| +
            (scalarStripCoefficientConstant ui S g * F ^ 2 * (b - a) / S.r u b) * |S.duphi u b|) =
          (scalarStripCoefficientConstant ui S g + 2) * (F ^ 2 * (b - a)) *
            ((-S.nu u b) / S.r u b ^ 2) +
          8 * (F ^ 2 * (b - a)) * (|S.duphi u b| / S.r u b) := by ring
      apply sub_nonneg.mp
      rw [heDiff]
      exact add_nonneg h₁ h₂

end StandingFull

end AcExtensionPrinciple

end
