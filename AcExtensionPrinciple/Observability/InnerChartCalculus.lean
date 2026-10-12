module

public import AcExtensionPrinciple.Observability.InnerChartCurve
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Calculus components for inner-boundary expansion regularity

Paper `e1a0fd5`, `equations.tex` lines 1460–1473 and 1877–1907.
The logarithmic expansion coefficients are smooth functions of three
bounded physical fields on a convex set with positive denominators.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory
open scoped NNReal

/-- A uniformly bounded primitive density controls every increment.
Paper `e1a0fd5`, characteristic AC/BV calculus at line 1522 and 1901. -/
theorem inner_primitive_increment {f g : ℝ → ℝ} {x y B : ℝ} (hxy : x ≤ y)
    (hp : IntervalPrimitive f g x y) (hb : ∀ z ∈ Icc x y, |g z| ≤ B) :
    |f y - f x| ≤ B * (y - x) := by
  rw [hp.2]
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := g) (a := x) (b := y) (fun z hz => by
      rw [uIoc_of_le hxy] at hz
      simpa only [Real.norm_eq_abs] using hb z ⟨hz.1.le, hz.2⟩)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hxy), mul_comm] using hi

/-- Uniform characteristic primitive bounds imply a uniform Lipschitz
constant on a segment. Paper `e1a0fd5`, line 1522 and 1901. -/
theorem inner_primitive_lipschitz {f g : ℝ → ℝ} {l r B : ℝ} (hB : 0 ≤ B)
    (hp : ∀ x ∈ Icc l r, ∀ y ∈ Icc l r, x ≤ y → IntervalPrimitive f g x y)
    (hb : ∀ z ∈ Icc l r, |g z| ≤ B) : LipschitzOnWith ⟨B, hB⟩ f (Icc l r) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  change dist (f x) (f y) ≤ B * dist x y
  rcases le_total x y with hxy | hyx
  · have hh := inner_primitive_increment hxy (hp x hx y hy hxy)
      (fun z hz => hb z ⟨hx.1.trans hz.1, hz.2.trans hy.2⟩)
    simpa only [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxy), neg_sub,
      abs_sub_comm] using hh
  · have hh := inner_primitive_increment hyx (hp y hy x hx hyx)
      (fun z hz => hb z ⟨hy.1.trans hz.1, hz.2.trans hx.2⟩)
    simpa only [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hyx)] using hh

/-- A convex bounded coefficient domain with both denominators separated
from zero. Its third coordinate is either λ or ν. Paper `e1a0fd5`,
`eq:logarithmic-expansions`, lines 1460–1473 and 1901. -/
@[expose] def innerCoefficientBox (δ d B : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p | δ ≤ p.1 ∧ d ≤ p.1 - 2 * p.2.1 ∧
    |p.1| ≤ B ∧ |p.2.1| ≤ B ∧ |p.2.2| ≤ B}

/-- The coefficient box is compact. Paper `e1a0fd5`, regularity input
at lines 1460–1473 and 1901. -/
theorem innerCoefficientBox_compact (δ d B : ℝ) : IsCompact (innerCoefficientBox δ d B) := by
  have hc : IsClosed (innerCoefficientBox δ d B) :=
    (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_const (continuous_fst.sub (continuous_const.mul
        (continuous_fst.comp continuous_snd)))).inter
      ((isClosed_le continuous_fst.abs continuous_const).inter
        ((isClosed_le (continuous_fst.comp continuous_snd).abs continuous_const).inter
          (isClosed_le (continuous_snd.comp continuous_snd).abs continuous_const))))
  apply ((isCompact_Icc : IsCompact (Icc (-B) B)).prod
    ((isCompact_Icc : IsCompact (Icc (-B) B)).prod
      (isCompact_Icc : IsCompact (Icc (-B) B)))).of_isClosed_subset hc
  intro p hp
  exact ⟨abs_le.mp hp.2.2.1, abs_le.mp hp.2.2.2.1, abs_le.mp hp.2.2.2.2⟩

/-- The denominator restrictions and box bounds form a convex domain.
Paper `e1a0fd5`, regularity input at lines 1460–1473 and 1901. -/
theorem innerCoefficientBox_convex (δ d B : ℝ) : Convex ℝ (innerCoefficientBox δ d B) := by
  intro p hp q hq x y hx hy hsum
  change δ ≤ x * p.1 + y * q.1 ∧
    d ≤ x * p.1 + y * q.1 - 2 * (x * p.2.1 + y * q.2.1) ∧
    |x * p.1 + y * q.1| ≤ B ∧ |x * p.2.1 + y * q.2.1| ≤ B ∧
    |x * p.2.2 + y * q.2.2| ≤ B
  rcases hp with ⟨hpδ, hpd, hpr, hpm, hpe⟩
  rcases hq with ⟨hqδ, hqd, hqr, hqm, hqe⟩
  have hδ := add_le_add (mul_le_mul_of_nonneg_left hpδ hx)
    (mul_le_mul_of_nonneg_left hqδ hy)
  have hd := add_le_add (mul_le_mul_of_nonneg_left hpd hx)
    (mul_le_mul_of_nonneg_left hqd hy)
  have hbox {u v : ℝ} (hu : |u| ≤ B) (hv : |v| ≤ B) : |x * u + y * v| ≤ B := by
    calc
      _ ≤ |x * u| + |y * v| := abs_add_le _ _
      _ = x * |u| + y * |v| := by rw [abs_mul, abs_mul, abs_of_nonneg hx, abs_of_nonneg hy]
      _ ≤ x * B + y * B := add_le_add (mul_le_mul_of_nonneg_left hu hx)
        (mul_le_mul_of_nonneg_left hv hy)
      _ = B := by rw [← add_mul, hsum, one_mul]
  rw [← add_mul, hsum, one_mul] at hδ hd
  exact ⟨hδ, by linarith,
    hbox hpr hqr, hbox hpm hqm, hbox hpe hqe⟩

/-- The common logarithmic coefficient as a smooth rational function
of radius, mass, and one expansion. Paper `e1a0fd5`,
`eq:logarithmic-expansions`, lines 1460–1473 and 1901. -/
@[expose] noncomputable def innerExpansionCoefficient (p : ℝ × ℝ × ℝ) : ℝ :=
  2 * p.2.1 * p.2.2 / ((p.1 - 2 * p.2.1) * p.1)

/-- The same rational map has a uniform Lipschitz constant on every
positive-denominator box. Paper `e1a0fd5`, lines 1460–1473 and 1901. -/
theorem innerExpansionCoefficient_lipschitz {δ d B : ℝ} (hδ : 0 < δ) (hd : 0 < d) :
    ∃ L : ℝ≥0, LipschitzOnWith L innerExpansionCoefficient (innerCoefficientBox δ d B) := by
  have hn : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => 2 * p.2.1 * p.2.2)
      (innerCoefficientBox δ d B) := by fun_prop
  have hden : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => (p.1 - 2 * p.2.1) * p.1)
      (innerCoefficientBox δ d B) := by fun_prop
  exact (hn.div hden (fun p hp => mul_ne_zero (hd.trans_le hp.2.1).ne'
    (hδ.trans_le hp.1).ne')).exists_lipschitzOnWith (by decide)
      (innerCoefficientBox_convex δ d B) (innerCoefficientBox_compact δ d B)

/-- The rational form agrees with the reduced logarithmic coefficient.
Paper `e1a0fd5`, `eq:logarithmic-expansions`, lines 1460–1473 and 1901. -/
theorem innerExpansionCoefficient_eq (S : SSFields) {s t E : ℝ} (hr : S.r s t ≠ 0)
    (hg : 1 - S.mu s t ≠ 0) :
    innerExpansionCoefficient (S.r s t, S.m s t, E) =
      S.mu s t * E / ((1 - S.mu s t) * S.r s t) := by
  have hgap : S.r s t - 2 * S.m s t ≠ 0 := by
    have he : S.r s t - 2 * S.m s t = (1 - S.mu s t) * S.r s t := by
      unfold SSFields.mu massRatio
      field_simp [hr]
    rw [he]
    exact mul_ne_zero hg hr
  unfold innerExpansionCoefficient SSFields.mu massRatio
  field_simp [hr, hgap]

end AcExtensionPrinciple

end
