module

public import AcExtensionPrinciple.Observability.InnerChartLogarithms
public import AcExtensionPrinciple.Observability.InnerChartMovingIntegral

/-!
# Inner-boundary logarithmic trace increments

Paper `e1a0fd5`, `equations.tex` line 1522 and lines 1460–1473, 1901.
The two logarithmic traces use the different transverse coefficient bounds.
-/

public section

namespace AcExtensionPrinciple.InnerCylinder

open Set MeasureTheory
open scoped NNReal

variable {b T K a s₀ s₁ : ℝ} {S : SSFields} {h : NormalizedChartData b T K S}
variable (c : InnerCylinder h a s₀ s₁)

/-- A uniform incoming log(-ν) increment bound on overlapping slices.
The coefficient premises are discharged by inner_coefficient_controls.
Paper `e1a0fd5`, lines 1460–1473 and 1901, AC justification at line 1522. -/
theorem nu_log_increment {C L V : ℝ≥0}
    (hv : LipschitzOnWith V c.v (Icc s₀ s₁))
    (hb : ∀ p ∈ h.innerAnnulus a, |innerNuCoefficient S p.1 p.2| ≤ C)
    (hl : ∀ t x y, x ≤ y → inSeg t x y ⊆ h.innerAnnulus a →
      LipschitzOnWith L (fun s => innerNuCoefficient S s t) (Icc x y))
    {x y : ℝ} (hx : x ∈ Icc s₀ s₁) (hy : y ∈ Icc s₀ s₁)
    (hxy : x ≤ y) (hover : c.v y ≤ x) :
    |Real.log (-S.nu x (c.v x)) - Real.log (-S.nu y (c.v y))| ≤
      ((C : ℝ) * V + L * T + C) * (y - x) := by
  have hvxy := c.v_strictMono.monotoneOn hx hy hxy
  have htx := c.triangle_annulus hx
  have hty := c.triangle_annulus hy
  have hcx : IntervalIntegrable (innerNuCoefficient S x) volume (c.v x) x :=
    ((h.inner_coefficients_continuous c.a_pos).1.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => htx ⟨ht.1, ht.2, le_rfl⟩)).intervalIntegrable_of_Icc
        (c.points x hx).2.1.le
  have hcy : IntervalIntegrable (innerNuCoefficient S y) volume (c.v y) y :=
    ((h.inner_coefficients_continuous c.a_pos).1.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => hty ⟨ht.1, ht.2, le_rfl⟩)).intervalIntegrable_of_Icc
        (c.points y hy).2.1.le
  have hi := inner_moving_integral_increment hvxy hover hxy hcx hcy
    (C := (C : ℝ)) (D := (L : ℝ) * (y - x))
    (fun z hz => hb (x, z) (htx ⟨hz.1, hz.2.trans hover, le_rfl⟩))
    (fun z hz => by
      have hseg : inSeg z x y ⊆ h.innerAnnulus a := by
        rintro ⟨s, t⟩ ⟨hs, ht⟩
        simp only [mem_singleton_iff] at ht
        subst t
        exact hty ⟨hz.1, hz.2.trans hs.1, hs.2⟩
      have hh := (hl z x y hxy hseg).dist_le_mul
        x (left_mem_Icc.mpr hxy) y (right_mem_Icc.mpr hxy)
      simpa only [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxy), neg_sub] using hh)
    (fun z hz => hb (y, z) (hty ⟨hover.trans hz.1, hz.2, le_rfl⟩))
  have hvbound : c.v y - c.v x ≤ (V : ℝ) * (y - x) := by
    have hh := hv.dist_le_mul x hx y hy
    simpa only [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hvxy),
      abs_of_nonpos (sub_nonpos.mpr hxy), neg_sub] using hh
  have hlen : x - c.v y ≤ T := by
    linarith [(c.source_mem hx).1.2.1, c.label_nonneg hy]
  have hcmp : (C : ℝ) * (c.v y - c.v x) +
      (L : ℝ) * (y - x) * (x - c.v y) + C * (y - x) ≤
      ((C : ℝ) * V + L * T + C) * (y - x) := by
    calc
      _ ≤ (C : ℝ) * (V * (y - x)) + (L * (y - x)) * T + C * (y - x) :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left hvbound C.2)
          (mul_le_mul_of_nonneg_left hlen (mul_nonneg L.2 (sub_nonneg.mpr hxy)))) le_rfl
      _ = _ := by ring
  rw [c.nu_log_representation hx, c.nu_log_representation hy]
  simpa only [neg_sub_neg, abs_sub_comm] using hi.trans hcmp

/-- A uniform outgoing log(λ) increment bound on overlapping slices.
The coefficient premises are discharged by inner_coefficient_controls.
Paper `e1a0fd5`, lines 1460–1473 and 1901, AC justification at line 1522. -/
theorem lam_log_increment {C L V : ℝ≥0}
    (hv : LipschitzOnWith V c.v (Icc s₀ s₁))
    (hb : ∀ p ∈ h.innerAnnulus a, |innerLamCoefficient S p.1 p.2| ≤ C)
    (hl : ∀ s x y, x ≤ y → outSeg s x y ⊆ h.innerAnnulus a →
      LipschitzOnWith L (innerLamCoefficient S s) (Icc x y))
    {x y : ℝ} (hx : x ∈ Icc s₀ s₁) (hy : y ∈ Icc s₀ s₁)
    (hxy : x ≤ y) (hover : c.v y ≤ x) :
    |Real.log (S.lam x (c.v x)) - Real.log (S.lam y (c.v y))| ≤
      ((C : ℝ) * V + L * V * T + C) * (y - x) := by
  have hvxy := c.v_strictMono.monotoneOn hx hy hxy
  have htx := c.triangle_annulus hx
  have hty := c.triangle_annulus hy
  have hcx : IntervalIntegrable (fun s => innerLamCoefficient S s (c.v x)) volume (c.v x) x :=
    ((h.inner_coefficients_continuous c.a_pos).2.comp
      (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => htx ⟨le_rfl, hs.1, hs.2⟩)).intervalIntegrable_of_Icc
        (c.points x hx).2.1.le
  have hcy : IntervalIntegrable (fun s => innerLamCoefficient S s (c.v y)) volume (c.v y) y :=
    ((h.inner_coefficients_continuous c.a_pos).2.comp
      (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => hty ⟨le_rfl, hs.1, hs.2⟩)).intervalIntegrable_of_Icc
        (c.points y hy).2.1.le
  have hi := inner_moving_integral_increment hvxy hover hxy hcx hcy
    (C := (C : ℝ)) (D := (L : ℝ) * (c.v y - c.v x))
    (fun z hz => hb (z, c.v x) (htx ⟨le_rfl, hz.1, hz.2.trans hover⟩))
    (fun z hz => by
      have hseg : outSeg z (c.v x) (c.v y) ⊆ h.innerAnnulus a := by
        rintro ⟨s, t⟩ ⟨hs, ht⟩
        simp only [mem_singleton_iff] at hs
        subst s
        exact htx ⟨ht.1, ht.2.trans hz.1, hz.2⟩
      have hh := (hl z (c.v x) (c.v y) hvxy hseg).dist_le_mul
        (c.v x) (left_mem_Icc.mpr hvxy) (c.v y) (right_mem_Icc.mpr hvxy)
      simpa only [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hvxy), neg_sub] using hh)
    (fun z hz => hb (z, c.v y) (hty ⟨le_rfl, hover.trans hz.1, hz.2⟩))
  have hvbound : c.v y - c.v x ≤ (V : ℝ) * (y - x) := by
    have hh := hv.dist_le_mul x hx y hy
    simpa only [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hvxy),
      abs_of_nonpos (sub_nonpos.mpr hxy), neg_sub] using hh
  have hlen : x - c.v y ≤ T := by
    linarith [(c.source_mem hx).1.2.1, c.label_nonneg hy]
  have hcmp : (C : ℝ) * (c.v y - c.v x) +
      (L : ℝ) * (c.v y - c.v x) * (x - c.v y) + C * (y - x) ≤
      ((C : ℝ) * V + L * V * T + C) * (y - x) := by
    have hprod := mul_le_mul hvbound hlen (sub_nonneg.mpr hover)
      (mul_nonneg V.2 (sub_nonneg.mpr hxy))
    have hprod' := mul_le_mul_of_nonneg_left hprod L.2
    calc
      _ ≤ (C : ℝ) * (V * (y - x)) + L * ((V * (y - x)) * T) + C * (y - x) := by
        have hl := mul_le_mul_of_nonneg_left hvbound C.2
        nlinarith
      _ = _ := by ring
  rw [c.lam_log_representation hx, c.lam_log_representation hy]
  exact hi.trans hcmp

end AcExtensionPrinciple.InnerCylinder

end
