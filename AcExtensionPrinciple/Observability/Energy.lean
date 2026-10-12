module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic

/-!
# AC boundary energy and amplitude estimates

Helpers for paper `e1a0fd5`, `equations.tex` lines 1501, 1518,
1524–1528 (`eq:observability-shifted-stability`, `eq:observability-axis-amplitude`).
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory

/-- The quadratic balance has the advertised one-sided bounds; paper `e1a0fd5`,
`equations.tex` line 1518. -/
theorem shifted_balance_bounds (x y : ℝ) :
    -(x ^ 2 + y ^ 2) ≤ x * y - y ^ 2 / 2 ∧
      x * y - y ^ 2 / 2 ≤ (x ^ 2 + y ^ 2) / 2 := by
  constructor <;> nlinarith [sq_nonneg (x - y), sq_nonneg (x + y)]

/-- AC stability on every initial subinterval; paper `e1a0fd5`,
`eq:observability-shifted-stability`, lines 1501, 1518. Square integrability is
the finite-energy case; the infinite-energy estimate is vacuous. -/
theorem shifted_energy_stability {F x y : ℝ → ℝ} {T s : ℝ}
    (hs : s ∈ Icc 0 T) (hF : AbsolutelyContinuousOnInterval F 0 T)
    (hx : IntervalIntegrable (fun u ↦ x u ^ 2) volume 0 T)
    (hy : IntervalIntegrable (fun u ↦ y u ^ 2) volume 0 T)
    (hder : ∀ᵐ u ∂volume, u ∈ Ioo 0 T → deriv F u = x u * y u - y u ^ 2 / 2) :
    F 0 - (∫ u in 0..T, x u ^ 2 + y u ^ 2) ≤ F s ∧
      F s ≤ F 0 + (∫ u in 0..T, x u ^ 2 + y u ^ 2) / 2 := by
  have hT : 0 ≤ T := hs.1.trans hs.2
  have hsub : uIcc 0 s ⊆ uIcc 0 T := by
    rw [uIcc_of_le hs.1, uIcc_of_le hT]
    exact Icc_subset_Icc le_rfl hs.2
  have hFs := hF.mono hsub
  have he := hx.add hy
  have hes := he.mono_set hsub
  have hmono : (∫ u in 0..s, x u ^ 2 + y u ^ 2) ≤
      ∫ u in 0..T, x u ^ 2 + y u ^ 2 := by
    apply intervalIntegral.integral_mono_interval le_rfl hs.1 hs.2
    · exact ae_of_all _ (by intro u; positivity)
    · exact he
  have hl : (∫ u in 0..s, -(x u ^ 2 + y u ^ 2)) ≤ ∫ u in 0..s, deriv F u := by
    apply intervalIntegral.integral_mono_ae_restrict hs.1 hes.neg hFs.intervalIntegrable_deriv
    rw [Filter.EventuallyLE, ← restrict_Ioo_eq_restrict_Icc,
      ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hder] with u hu hus
    rw [hu ⟨hus.1, hus.2.trans_le hs.2⟩]
    exact (shifted_balance_bounds _ _).1
  have hu : (∫ u in 0..s, deriv F u) ≤ ∫ u in 0..s, (x u ^ 2 + y u ^ 2) / 2 := by
    apply intervalIntegral.integral_mono_ae_restrict hs.1 hFs.intervalIntegrable_deriv
      (hes.div_const 2)
    rw [Filter.EventuallyLE, ← restrict_Ioo_eq_restrict_Icc,
      ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hder] with u hu hus
    rw [hu ⟨hus.1, hus.2.trans_le hs.2⟩]
    exact (shifted_balance_bounds _ _).2
  rw [intervalIntegral.integral_neg, hFs.integral_deriv_eq_sub] at hl
  rw [intervalIntegral.integral_div, hFs.integral_deriv_eq_sub] at hu
  constructor <;> linarith

/-- Cauchy–Schwarz for a real primitive, proved by integrating its variance;
paper `e1a0fd5`, calculus step at `equations.tex` lines 1524–1528. -/
theorem primitive_sq_le {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b)
    (hf2 : IntervalIntegrable (fun u ↦ f u ^ 2) volume a b) :
    (∫ u in a..b, f u) ^ 2 ≤ (b - a) * (∫ u in a..b, f u ^ 2) := by
  rcases hab.eq_or_lt with rfl | hab
  · simp
  let c := (∫ u in a..b, f u) / (b - a)
  have hc : c * (b - a) = ∫ u in a..b, f u := by
    dsimp [c]
    exact div_mul_cancel₀ _ (sub_pos.mpr hab).ne'
  have hpos : 0 ≤ ∫ u in a..b, f u ^ 2 - 2 * c * f u + c ^ 2 := by
    apply intervalIntegral.integral_nonneg hab.le
    intro u _
    nlinarith [sq_nonneg (f u - c)]
  rw [intervalIntegral.integral_add (hf2.sub (hf.const_mul _)) intervalIntegrable_const,
    intervalIntegral.integral_sub hf2 (hf.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at hpos
  simp only [smul_eq_mul] at hpos
  have := mul_nonneg (sub_pos.mpr hab).le hpos
  nlinarith [sq_nonneg (∫ u in a..b, f u)]

/-- The two boundary primitives have combined constant `√(2sE)`; paper
`e1a0fd5`, `eq:observability-axis-amplitude`, lines 1524–1528. -/
theorem axis_amplitude_cauchy_schwarz {P x : ℝ → ℝ} {T s t : ℝ}
    (ht : 0 ≤ t) (hts : t ≤ s) (hsT : s ≤ T)
    (hP : AbsolutelyContinuousOnInterval P 0 T)
    (hx : IntervalIntegrable x volume 0 T)
    (hx2 : IntervalIntegrable (fun u ↦ x u ^ 2) volume 0 T)
    (hy2 : IntervalIntegrable (fun u ↦ deriv P u ^ 2) volume 0 T) :
    |P s - P 0| + |∫ u in t..s, x u| ≤
      Real.sqrt (2 * s * (∫ u in 0..T, x u ^ 2 + deriv P u ^ 2)) := by
  have hs : 0 ≤ s := ht.trans hts
  have hT := hs.trans hsT
  have hsub0 : uIcc 0 s ⊆ uIcc 0 T := by
    rw [uIcc_of_le hs, uIcc_of_le hT]
    exact Icc_subset_Icc le_rfl hsT
  have hsubt : uIcc t s ⊆ uIcc 0 T := by
    rw [uIcc_of_le hts, uIcc_of_le hT]
    exact Icc_subset_Icc ht hsT
  have hPs := hP.mono hsub0
  have hpy := primitive_sq_le hs hPs.intervalIntegrable_deriv (hy2.mono_set hsub0)
  rw [hPs.integral_deriv_eq_sub, sub_zero] at hpy
  have hpx := primitive_sq_le hts (hx.mono_set hsubt) (hx2.mono_set hsubt)
  have hxmono : (∫ u in t..s, x u ^ 2) ≤ ∫ u in 0..T, x u ^ 2 := by
    exact intervalIntegral.integral_mono_interval ht hts hsT
      (ae_of_all _ (fun u ↦ sq_nonneg (x u))) hx2
  have hymono : (∫ u in 0..s, deriv P u ^ 2) ≤ ∫ u in 0..T, deriv P u ^ 2 := by
    exact intervalIntegral.integral_mono_interval le_rfl hs hsT
      (ae_of_all _ (fun u ↦ sq_nonneg (deriv P u))) hy2
  have hxnon : 0 ≤ ∫ u in t..s, x u ^ 2 :=
    intervalIntegral.integral_nonneg hts (by intros; positivity)
  have hxb : (∫ u in t..s, x u) ^ 2 ≤ s * (∫ u in 0..T, x u ^ 2) := by
    nlinarith [mul_nonneg ht hxnon, mul_le_mul_of_nonneg_left hxmono hs]
  have hyb : (P s - P 0) ^ 2 ≤ s * (∫ u in 0..T, deriv P u ^ 2) :=
    hpy.trans (mul_le_mul_of_nonneg_left hymono hs)
  apply (Real.le_sqrt (by positivity) (by
    apply mul_nonneg (by positivity)
    exact intervalIntegral.integral_nonneg hT (by intros; positivity))).mpr
  rw [intervalIntegral.integral_add hx2 hy2]
  nlinarith [sq_abs (P s - P 0), sq_abs (∫ u in t..s, x u),
    sq_nonneg (|P s - P 0| - |∫ u in t..s, x u|)]

end AcExtensionPrinciple

end
