module

public import AcExtensionPrinciple.Weighted.CauchySchwarz
public import AcExtensionPrinciple.Weighted.ClassNorms
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Local finite energy for an incoming integral formula

Calculus helpers, paper `e1a0fd5`, `eq:frozen-solution-operators`,
`equations.tex` lines 1265–1276. On a radius cutoff, geometric
coefficients are bounded, the source is L², and the initial weighted energy
controls the initial L² norm. The lemmas below establish Volterra finiteness before the energy
identity is integrated.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory
open scoped ENNReal

/-- The square of an integral is bounded by interval length times the
lower integral of the square, including infinite right-hand sides.
Paper `e1a0fd5`, lines 1268–1276, local finiteness of the incoming formula. -/
theorem incoming_integral_sq_le {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : Measurable f) :
    ENNReal.ofReal ((∫ s in a..b, f s) ^ 2) ≤
      ENNReal.ofReal (b - a) * ∫⁻ s in Ioc a b, ENNReal.ofReal (|f s| ^ 2) := by
  let μ := volume.restrict (Ioc a b)
  have hs := lintegral_sqrt_mul_sq_le
    (μ := μ) ((hf.norm.pow_const 2).ennreal_ofReal.aemeasurable)
    ((measurable_const : Measurable (fun _ : ℝ => (1 : ℝ≥0∞))).aemeasurable)
  have hroot (s : ℝ) : ENNReal.ofReal (|f s| ^ 2) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal |f s| := by
    rw [ENNReal.ofReal_pow (abs_nonneg _), ← ENNReal.rpow_natCast,
      ← ENNReal.rpow_mul]
    norm_num
  simp only [Real.norm_eq_abs, hroot, ENNReal.one_rpow, mul_one,
    lintegral_const] at hs
  simp only [μ, Measure.restrict_apply_univ, Real.volume_Ioc, one_mul] at hs
  have hn := enorm_integral_le_lintegral_enorm (μ := μ) f
  simp only [Real.enorm_eq_ofReal_abs] at hn
  have hsq := pow_le_pow_left' hn 2
  rw [← ENNReal.ofReal_pow (abs_nonneg _), sq_abs] at hsq
  rw [intervalIntegral.integral_of_le hab]
  exact hsq.trans (hs.trans_eq (mul_comm _ _))

/-- Uniform local L² control of an incoming primitive on a rectangle.
Paper `e1a0fd5`, lines 1268–1276. A finite source-square integral implies
finite energy of its primitive; no pointwise source bound is required. -/
theorem incoming_primitive_energy_lt_top {a b c d : ℝ} {H : ℝ × ℝ → ℝ}
    (hH : Measurable H)
    (hsource : (∫⁻ v in Icc c d, ∫⁻ s in Icc a b,
      ENNReal.ofReal (|H (s, v)| ^ 2)) < ⊤) :
    (∫⁻ u in Icc a b, ∫⁻ v in Icc c d,
      ENNReal.ofReal ((∫ s in a..u, H (s, v)) ^ 2)) < ⊤ := by
  have hbound (u : ℝ) (hu : u ∈ Icc a b) (v : ℝ) :
      ENNReal.ofReal ((∫ s in a..u, H (s, v)) ^ 2) ≤
        ENNReal.ofReal (b - a) * ∫⁻ s in Icc a b, ENNReal.ofReal (|H (s, v)| ^ 2) := by
    apply (incoming_integral_sq_le (f := fun s => H (s, v)) hu.1
      (hH.comp (measurable_id.prodMk measurable_const))).trans
    apply mul_le_mul (ENNReal.ofReal_le_ofReal (sub_le_sub_right hu.2 a)) ?_ zero_le zero_le
    exact lintegral_mono_set (Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl hu.2))
  calc
    _ ≤ ∫⁻ _u in Icc a b, ∫⁻ v in Icc c d, ENNReal.ofReal (b - a) *
        ∫⁻ s in Icc a b, ENNReal.ofReal (|H (s, v)| ^ 2) := by
      apply setLIntegral_mono' measurableSet_Icc
      intro u hu
      exact lintegral_mono (fun v => hbound u hu v)
    _ < ⊤ := by
      simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (ENNReal.mul_lt_top hsource ENNReal.ofReal_lt_top)

/-- Finite cutoff energy follows from a bounded integrating-factor formula, finite initial L²
energy, and finite source L² energy. Paper `e1a0fd5`, lines 1268–1276, preliminary finiteness for
energy integration. The geometry discharges `hformula`, `hω`, and the two local L² premises; this is
an internal calculus lemma, not Proposition 3.4 with extra assumptions. -/
theorem frozen_cutoff_energy_lt_top_of_formula {a b c d K C : ℝ}
    {J₀ : ℝ → ℝ} {H Z ω : ℝ × ℝ → ℝ}
    (hC : 0 ≤ C) (hH : Measurable H) (hJ₀ : Measurable J₀)
    (hinitial : (∫⁻ v in Icc c d, ENNReal.ofReal (J₀ v ^ 2)) < ⊤)
    (hsource : (∫⁻ v in Icc c d, ∫⁻ s in Icc a b,
      ENNReal.ofReal (|H (s, v)| ^ 2)) < ⊤)
    (hformula : ∀ u ∈ Icc a b, ∀ v ∈ Icc c d,
      |Z (u, v)| ≤ K * (|J₀ v| + |∫ s in a..u, H (s, v)|))
    (hω : ∀ u ∈ Icc a b, ∀ v ∈ Icc c d, ω (u, v) ≤ C) :
    (∫⁻ u in Icc a b, ∫⁻ v in Icc c d,
      ENNReal.ofReal (ω (u, v) * |Z (u, v)| ^ 2)) < ⊤ := by
  have hp := incoming_primitive_energy_lt_top hH hsource
  have hpoint (u : ℝ) (hu : u ∈ Icc a b) (v : ℝ) (hv : v ∈ Icc c d) :
      ω (u, v) * |Z (u, v)| ^ 2 ≤
        (2 * C * K ^ 2) * (J₀ v ^ 2 + (∫ s in a..u, H (s, v)) ^ 2) := by
    have hs := pow_le_pow_left₀ (abs_nonneg _) (hformula u hu v hv) 2
    have ht : (|J₀ v| + |∫ s in a..u, H (s, v)|) ^ 2 ≤
        2 * (J₀ v ^ 2 + (∫ s in a..u, H (s, v)) ^ 2) := by
      nlinarith [sq_nonneg (|J₀ v| - |∫ s in a..u, H (s, v)|),
        sq_abs (J₀ v), sq_abs (∫ s in a..u, H (s, v))]
    calc
      _ ≤ C * |Z (u, v)| ^ 2 := mul_le_mul_of_nonneg_right (hω u hu v hv) (sq_nonneg _)
      _ ≤ C * (K ^ 2 * (|J₀ v| + |∫ s in a..u, H (s, v)|) ^ 2) := by
        rw [← mul_pow]
        exact mul_le_mul_of_nonneg_left hs hC
      _ ≤ C * (K ^ 2 * (2 * (J₀ v ^ 2 + (∫ s in a..u, H (s, v)) ^ 2))) := by
        gcongr
      _ = _ := by ring
  calc
    _ ≤ ∫⁻ u in Icc a b, ∫⁻ v in Icc c d, ENNReal.ofReal (2 * C * K ^ 2) *
        (ENNReal.ofReal (J₀ v ^ 2) + ENNReal.ofReal ((∫ s in a..u, H (s, v)) ^ 2)) := by
      apply setLIntegral_mono' measurableSet_Icc
      intro u hu
      apply setLIntegral_mono' measurableSet_Icc
      intro v hv
      rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
        ← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal (hpoint u hu v hv)
    _ < ⊤ := by
      simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      have hsum : (∫⁻ u in Icc a b, ∫⁻ v in Icc c d,
          ENNReal.ofReal (J₀ v ^ 2) + ENNReal.ofReal ((∫ s in a..u, H (s, v)) ^ 2)) =
          (∫⁻ u in Icc a b, ∫⁻ v in Icc c d, ENNReal.ofReal (J₀ v ^ 2)) +
          ∫⁻ u in Icc a b, ∫⁻ v in Icc c d,
            ENNReal.ofReal ((∫ s in a..u, H (s, v)) ^ 2) := by
        simp_rw [lintegral_add_left (hJ₀.pow_const 2).ennreal_ofReal]
        exact lintegral_add_left measurable_const _
      rw [hsum]
      apply ENNReal.add_lt_top.mpr
      refine ⟨?_, hp⟩
      rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc]
      exact ENNReal.mul_lt_top hinitial ENNReal.ofReal_lt_top

end AcExtensionPrinciple

end
