module

public import AcExtensionPrinciple.Observability.Energy
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Hardy's inequality for an AC primitive

This module proves a regularized Hardy estimate.
Paper `e1a0fd5`, `eq:observability-primitive-hardy`,
`equations.tex` lines 1832–1845. Regularizing the denominator avoids assuming
integrability of the singular left side before proving it.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory Filter
open scoped Topology ENNReal

/-- Hardy's estimate with a positive denominator regularization; paper
`e1a0fd5`, `eq:observability-primitive-hardy`, lines 1832–1845. -/
theorem primitive_hardy_regularized {P : ℝ → ℝ} {L ε : ℝ}
    (hL : 0 ≤ L) (hε : 0 < ε) (hP : AbsolutelyContinuousOnInterval P 0 L)
    (hP0 : P 0 = 0)
    (h2 : IntervalIntegrable (fun ξ ↦ deriv P ξ ^ 2) volume 0 L) :
    (∫ ξ in 0..L, P ξ ^ 2 / (ξ + ε) ^ 2) ≤
      4 * (∫ ξ in 0..L, deriv P ξ ^ 2) := by
  have hn : ∀ ξ ∈ uIcc 0 L, ξ + ε ≠ 0 := by
    intro ξ hξ
    rw [uIcc_of_le hL] at hξ
    linarith [hξ.1]
  have hg : AbsolutelyContinuousOnInterval (fun ξ ↦ (ξ + ε)⁻¹) 0 L :=
    ((contDiffOn_id.add contDiffOn_const).inv hn).absolutelyContinuousOnInterval
  have hdg (ξ : ℝ) (hξ : ξ ∈ uIcc 0 L) :
      deriv (fun ξ ↦ (ξ + ε)⁻¹) ξ = -(1 / (ξ + ε) ^ 2) := by
    convert ((hasDerivAt_id ξ).add_const ε).inv (hn ξ hξ) |>.deriv using 1
    · rfl
    · simp only [id_eq, neg_div]
  have hu : ContinuousOn (fun ξ ↦ P ξ / (ξ + ε)) (uIcc 0 L) :=
    hP.continuousOn.div (continuousOn_id.add continuousOn_const) hn
  have hu2 : IntervalIntegrable (fun ξ ↦ (P ξ / (ξ + ε)) ^ 2) volume 0 L :=
    (hu.pow 2).intervalIntegrable
  have hH : IntervalIntegrable (fun ξ ↦ P ξ ^ 2 / (ξ + ε) ^ 2) volume 0 L := by
    simpa only [div_pow] using hu2
  have hJ : IntervalIntegrable (fun ξ ↦ P ξ / (ξ + ε) * deriv P ξ) volume 0 L :=
    hP.intervalIntegrable_deriv.continuousOn_mul hu
  have hparts := (hP.fun_mul hP).integral_mul_deriv_eq_deriv_mul hg
  have hleft : (∫ ξ in 0..L, (P ξ * P ξ) * deriv (fun ξ ↦ (ξ + ε)⁻¹) ξ) =
      -(∫ ξ in 0..L, P ξ ^ 2 / (ξ + ε) ^ 2) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro ξ hξ
    change P ξ * P ξ * deriv (fun ξ ↦ (ξ + ε)⁻¹) ξ = -(P ξ ^ 2 / (ξ + ε) ^ 2)
    rw [hdg ξ hξ]
    ring
  have hright : (∫ ξ in 0..L, deriv (fun ξ ↦ P ξ * P ξ) ξ * (ξ + ε)⁻¹) =
      2 * (∫ ξ in 0..L, P ξ / (ξ + ε) * deriv P ξ) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hP.ae_differentiableAt] with ξ hξD hξ
    have hd : deriv (fun ξ ↦ P ξ * P ξ) ξ = deriv P ξ * P ξ + P ξ * deriv P ξ :=
      ((hξD (uIoc_subset_uIcc hξ)).hasDerivAt.mul
        (hξD (uIoc_subset_uIcc hξ)).hasDerivAt).deriv
    rw [hd]
    ring
  rw [hleft, hright, hP0] at hparts
  simp only [zero_mul, sub_zero] at hparts
  have hend : 0 ≤ P L * P L * (L + ε)⁻¹ :=
    mul_nonneg (mul_self_nonneg _) (by positivity)
  let μ := volume.restrict (Ioc 0 L)
  have huLp : MemLp (fun ξ ↦ P ξ / (ξ + ε)) 2 μ := by
    apply (memLp_two_iff_integrable_sq _).mpr
    · simpa only [μ, uIoc_of_le hL, IntegrableOn] using hu2.def'
    · simpa only [μ, uIoc_of_le hL, IntegrableOn] using
        hu.intervalIntegrable.def'.aestronglyMeasurable
  have hdLp : MemLp (deriv P) 2 μ := by
    apply (memLp_two_iff_integrable_sq (measurable_deriv P).aestronglyMeasurable).mpr
    simpa only [μ, uIoc_of_le hL, IntegrableOn] using h2.def'
  have hcs := integral_mul_norm_le_Lp_mul_Lq
    (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩ :
      Real.HolderConjugate 2 2) (by simpa using huLp) (by simpa using hdLp)
  have hJabs : (∫ ξ in 0..L, P ξ / (ξ + ε) * deriv P ξ) ≤
      ∫ ξ, ‖P ξ / (ξ + ε)‖ * ‖deriv P ξ‖ ∂μ := by
    rw [intervalIntegral.integral_of_le hL]
    apply integral_mono
    · simpa only [μ, uIoc_of_le hL, IntegrableOn] using hJ.def'
    · exact huLp.norm.integrable_mul hdLp.norm
    · intro ξ
      simpa only [Real.norm_eq_abs, abs_mul] using le_abs_self
        (P ξ / (ξ + ε) * deriv P ξ)
  have hcs' : (∫ ξ in 0..L, P ξ / (ξ + ε) * deriv P ξ) ≤
      Real.sqrt (∫ ξ in 0..L, P ξ ^ 2 / (ξ + ε) ^ 2) *
      Real.sqrt (∫ ξ in 0..L, deriv P ξ ^ 2) := by
    have hh := hJabs.trans hcs
    simpa only [Real.norm_eq_abs, Real.rpow_two, sq_abs, div_pow,
      ← Real.sqrt_eq_rpow, intervalIntegral.integral_of_le hL, μ] using hh
  have hH0 : 0 ≤ ∫ ξ in 0..L, P ξ ^ 2 / (ξ + ε) ^ 2 :=
    intervalIntegral.integral_nonneg hL (by intros; positivity)
  have hE0 : 0 ≤ ∫ ξ in 0..L, deriv P ξ ^ 2 :=
    intervalIntegral.integral_nonneg hL (by intros; positivity)
  have hsH := Real.sq_sqrt hH0
  have hsE := Real.sq_sqrt hE0
  have hbound : (∫ ξ in 0..L, P ξ ^ 2 / (ξ + ε) ^ 2) ≤
      2 * (Real.sqrt (∫ ξ in 0..L, P ξ ^ 2 / (ξ + ε) ^ 2) *
        Real.sqrt (∫ ξ in 0..L, deriv P ξ ^ 2)) := by linarith
  have hsq := mul_self_le_mul_self hH0 hbound
  nlinarith [mul_nonneg (Real.sqrt_nonneg (∫ ξ in 0..L, P ξ ^ 2 / (ξ + ε) ^ 2))
    (Real.sqrt_nonneg (∫ ξ in 0..L, deriv P ξ ^ 2))]

/-- Hardy's inequality with the singular integral interpreted as a nonnegative
Lebesgue integral (and therefore with its finiteness proved); paper `e1a0fd5`,
`eq:observability-primitive-hardy`, lines 1832–1845. -/
theorem primitive_hardy {P : ℝ → ℝ} {L : ℝ}
    (hL : 0 ≤ L) (hP : AbsolutelyContinuousOnInterval P 0 L) (hP0 : P 0 = 0)
    (h2 : IntervalIntegrable (fun ξ ↦ deriv P ξ ^ 2) volume 0 L) :
    (∫⁻ ξ in Ioc 0 L, ENNReal.ofReal (P ξ ^ 2 / ξ ^ 2)) ≤
      ENNReal.ofReal (4 * (∫ ξ in 0..L, deriv P ξ ^ 2)) := by
  let ε : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  let f : ℕ → ℝ → ℝ≥0∞ := fun n ξ ↦ ENNReal.ofReal (P ξ ^ 2 / (ξ + ε n) ^ 2)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hi (n : ℕ) : IntervalIntegrable
      (fun ξ ↦ P ξ ^ 2 / (ξ + ε n) ^ 2) volume 0 L := by
    apply ContinuousOn.intervalIntegrable
    apply (hP.continuousOn.pow 2).div
      ((continuousOn_id.add continuousOn_const).pow 2)
    intro ξ hξ
    rw [uIcc_of_le hL] at hξ
    exact pow_ne_zero _ (ne_of_gt (add_pos_of_nonneg_of_pos hξ.1 (hε n)))
  have hm (n : ℕ) : AEMeasurable (f n) (volume.restrict (Ioc 0 L)) := by
    exact (show Integrable (fun ξ ↦ P ξ ^ 2 / (ξ + ε n) ^ 2)
      (volume.restrict (Ioc 0 L)) by
        simpa only [uIoc_of_le hL, IntegrableOn] using (hi n).def').aestronglyMeasurable
          |>.aemeasurable.ennreal_ofReal
  have hmono : ∀ᵐ ξ ∂volume.restrict (Ioc 0 L), Monotone (fun n ↦ f n ξ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with ξ hξ
    intro n m hnm
    apply ENNReal.ofReal_le_ofReal
    have hem : ε m ≤ ε n := by
      apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (n : ℝ) + 1)
      exact_mod_cast Nat.add_le_add_right hnm 1
    apply div_le_div_of_nonneg_left (sq_nonneg _)
      (sq_pos_of_pos (add_pos hξ.1 (hε m)))
    nlinarith [hε n, hε m, hξ.1]
  have heps : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : ∀ᵐ ξ ∂volume.restrict (Ioc 0 L),
      Tendsto (fun n ↦ f n ξ) atTop (𝓝 (ENNReal.ofReal (P ξ ^ 2 / ξ ^ 2))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with ξ hξ
    have hh := (tendsto_const_nhds (x := P ξ ^ 2)).div
      ((tendsto_const_nhds (x := ξ)).add heps |>.pow 2)
      (by simpa using pow_ne_zero 2 hξ.1.ne')
    simpa only [f, Function.comp_def, Pi.div_apply, Pi.pow_apply, add_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hh
  have hl := lintegral_tendsto_of_tendsto_of_monotone hm hmono hlim
  apply le_of_tendsto hl
  apply Eventually.of_forall
  intro n
  have hnon : ∀ᵐ ξ ∂volume.restrict (Ioc 0 L), 0 ≤ P ξ ^ 2 / (ξ + ε n) ^ 2 :=
    ae_of_all _ (by intro ξ; positivity)
  have hreal : (∫⁻ ξ in Ioc 0 L, f n ξ) =
      ENNReal.ofReal (∫ ξ in 0..L, P ξ ^ 2 / (ξ + ε n) ^ 2) := by
    rw [intervalIntegral.integral_of_le hL]
    exact (ofReal_integral_eq_lintegral_ofReal
      (by simpa only [uIoc_of_le hL, IntegrableOn] using (hi n).def') hnon).symm
  rw [hreal]
  exact ENNReal.ofReal_le_ofReal (primitive_hardy_regularized hL (hε n) hP hP0 h2)

/-- The stated `L²(0,L)` Hardy estimate, including finiteness of its left side;
paper `e1a0fd5`, `eq:observability-primitive-hardy`, lines 1832–1845. -/
theorem l2_primitive_hardy {f : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 L))) :
    IntegrableOn (fun ξ ↦ (∫ t in 0..ξ, f t) ^ 2 / ξ ^ 2) (Ioc 0 L) ∧
    (∫ ξ in 0..L, (∫ t in 0..ξ, f t) ^ 2 / ξ ^ 2) ≤
      4 * (∫ ξ in 0..L, f ξ ^ 2) := by
  have hfi : IntervalIntegrable f volume 0 L :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hL).mpr
      (hf.integrable (by norm_num))
  have hfi2 : IntervalIntegrable (fun ξ ↦ f ξ ^ 2) volume 0 L :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hL).mpr hf.integrable_sq
  let P : ℝ → ℝ := fun ξ ↦ ∫ t in 0..ξ, f t
  have hP : AbsolutelyContinuousOnInterval P 0 L :=
    hfi.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hP0 : P 0 = 0 := by simp [P]
  have hda : ∀ᵐ ξ ∂volume, ξ ∈ uIcc 0 L → deriv P ξ = f ξ := by
    filter_upwards [hfi.ae_hasDerivAt_integral] with ξ hξ hmem
    exact (hξ hmem 0 (by simp)).deriv
  have heq : (fun ξ ↦ f ξ ^ 2) =ᵐ[volume.restrict (uIoc 0 L)]
      (fun ξ ↦ deriv P ξ ^ 2) := by
    change ∀ᵐ ξ ∂volume.restrict (uIoc 0 L), f ξ ^ 2 = deriv P ξ ^ 2
    rw [ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [hda] with ξ hξ hmem
    rw [hξ (uIoc_subset_uIcc hmem)]
  have h2 := hfi2.congr_ae heq
  have henergy : (∫ ξ in 0..L, deriv P ξ ^ 2) = ∫ ξ in 0..L, f ξ ^ 2 := by
    exact intervalIntegral.integral_congr_ae_restrict heq.symm
  have hb := primitive_hardy hL hP hP0 h2
  rw [henergy] at hb
  have hmeas : AEStronglyMeasurable (fun ξ ↦ P ξ ^ 2 / ξ ^ 2)
      (volume.restrict (Ioc 0 L)) := by
    have hPm : AEStronglyMeasurable P (volume.restrict (Ioc 0 L)) := by
      simpa only [uIoc_of_le hL, IntegrableOn] using
        hP.continuousOn.intervalIntegrable.def'.aestronglyMeasurable
    convert (hPm.pow 2).mul
      ((measurable_id.pow_const 2).inv).aestronglyMeasurable using 1
    funext ξ
    simp [div_eq_mul_inv]
  have hnon : ∀ᵐ ξ ∂volume.restrict (Ioc 0 L), 0 ≤ P ξ ^ 2 / ξ ^ 2 :=
    ae_of_all _ (by intro ξ; positivity)
  have hint : Integrable (fun ξ ↦ P ξ ^ 2 / ξ ^ 2) (volume.restrict (Ioc 0 L)) :=
    (lintegral_ofReal_ne_top_iff_integrable hmeas hnon).mp
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb)
  refine ⟨hint, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnon,
    ← intervalIntegral.integral_of_le hL] at hb
  have hE0 : 0 ≤ 4 * (∫ ξ in 0..L, f ξ ^ 2) := by
    apply mul_nonneg (by norm_num)
    exact intervalIntegral.integral_nonneg hL (by intros; positivity)
  exact (ENNReal.ofReal_le_ofReal_iff hE0).mp hb

end AcExtensionPrinciple

end
