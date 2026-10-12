module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic

/-!
# Bounded integrating factors for incoming transport

Helpers for paper commit `e1a0fd5`, `equations.tex` lines 1100–1124
(`eq:renormalized-remainder-pointwise`).
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory Filter

/-- Exponentiation preserves AC on a compact interval; paper `e1a0fd5`,
`equations.tex` lines 1100–1124, integrating-factor step. -/
theorem ac_exp {A : ℝ → ℝ} {a b : ℝ}
    (hA : AbsolutelyContinuousOnInterval A a b) :
    AbsolutelyContinuousOnInterval (fun x ↦ Real.exp (A x)) a b := by
  obtain ⟨C, hC⟩ := isCompact_uIcc.exists_bound_of_continuousOn hA.continuousOn
  obtain ⟨K, hK⟩ := (Real.contDiff_exp.contDiffOn (s := Icc (-C) C)).exists_lipschitzOnWith
    (by norm_num : (1 : WithTop ℕ∞) ≠ 0) (convex_Icc _ _) isCompact_Icc
  apply hK.comp_absolutelyContinuousOnInterval ?_ hA
  intro x hx
  have hb := hC x hx
  simpa only [Real.norm_eq_abs, abs_le, mem_Icc] using hb

/-- Variation of constants for AC transport with integrable coefficient and
source; paper `e1a0fd5`, `equations.tex` lines 1100–1124
(`eq:renormalized-remainder-transport`). -/
theorem ac_transport_integrating_factor {J a S : ℝ → ℝ} {uᵢ u : ℝ}
    (hJ : AbsolutelyContinuousOnInterval J uᵢ u)
    (ha : IntervalIntegrable a volume uᵢ u)
    (hODE : ∀ᵐ t ∂volume, t ∈ uIcc uᵢ u →
      HasDerivAt J (a t * J t + S t) t) (hzero : J uᵢ = 0) :
    J u = Real.exp (∫ t in uᵢ..u, a t) *
      ∫ t in uᵢ..u, Real.exp (-(∫ s in uᵢ..t, a s)) * S t := by
  let A (t : ℝ) := ∫ s in uᵢ..t, a s
  have hA : AbsolutelyContinuousOnInterval A uᵢ u :=
    ha.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hE := ac_exp hA.fun_neg
  have hP := hE.fun_mul hJ
  have hderiv : deriv (fun t ↦ Real.exp (-A t) * J t) =ᵐ[volume.restrict (uIoc uᵢ u)]
      (fun t ↦ Real.exp (-A t) * S t) := by
    filter_upwards [ae_restrict_of_ae hODE, ae_restrict_of_ae ha.ae_hasDerivAt_integral,
      ae_restrict_mem measurableSet_uIoc] with t ht hAt hmem
    have hmem' := uIoc_subset_uIcc hmem
    have hdA : HasDerivAt A (a t) t := hAt hmem' uᵢ (by simp)
    have hp := (hdA.fun_neg.exp).fun_mul (ht hmem')
    rw [hp.deriv]
    ring
  have heq := hP.integral_deriv_eq_sub
  rw [intervalIntegral.integral_congr_ae_restrict hderiv] at heq
  simp only [A, intervalIntegral.integral_same, neg_zero, Real.exp_zero, one_mul,
    hzero, sub_zero] at heq
  rw [heq]
  rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]

/-- The remainder's variation-of-constants bound with a bounded incoming
integrating factor; paper `e1a0fd5`, `equations.tex` lines 1100–1124
(`eq:renormalized-remainder-pointwise`). Finite integrals are stated as
`IntervalIntegrable`, so the bound does not use the default value of an
undefined Bochner integral. -/
theorem ac_transport_bound {J a S g : ℝ → ℝ} {uᵢ u C Λ : ℝ}
    (hu : uᵢ ≤ u) (hJ : AbsolutelyContinuousOnInterval J uᵢ u)
    (ha : IntervalIntegrable a volume uᵢ u) (hg : IntervalIntegrable g volume uᵢ u)
    (hODE : ∀ᵐ t ∂volume, t ∈ Icc uᵢ u → HasDerivAt J (a t * J t + S t) t)
    (hzero : J uᵢ = 0) (hapos : ∀ᵐ t ∂volume, t ∈ Icc uᵢ u → 0 ≤ a t)
    (hΛ : (∫ t in uᵢ..u, a t) ≤ Λ)
    (hsource : ∀ᵐ t ∂volume, t ∈ Icc uᵢ u → 0 ≤ g t ∧ |S t| ≤ C * g t) :
    |J u| ≤ C * Real.exp Λ * (∫ t in uᵢ..u, g t) := by
  let A (t : ℝ) := ∫ s in uᵢ..t, a s
  have hA : AbsolutelyContinuousOnInterval A uᵢ u :=
    ha.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hODE' : ∀ᵐ t ∂volume, t ∈ uIcc uᵢ u →
      HasDerivAt J (a t * J t + S t) t := by
    simpa only [uIcc_of_le hu] using hODE
  have hS : IntervalIntegrable S volume uᵢ u := by
    refine (hJ.intervalIntegrable_deriv.sub
      (ha.mul_continuousOn hJ.continuousOn)).congr_ae ?_
    filter_upwards [ae_restrict_of_ae hODE', ae_restrict_mem measurableSet_uIoc]
      with t ht hmem
    have hd := (ht (uIoc_subset_uIcc hmem)).deriv
    simp only [hd]
    ring
  have hE := ac_exp hA.fun_neg
  have hi : IntervalIntegrable (fun t ↦ Real.exp (-A t) * S t) volume uᵢ u :=
    hS.continuousOn_mul hE.continuousOn
  have hAnonneg (t : ℝ) (ht : t ∈ Icc uᵢ u) : 0 ≤ A t := by
    apply intervalIntegral.integral_nonneg_of_ae_restrict ht.1
    filter_upwards [ae_restrict_of_ae hapos, ae_restrict_mem measurableSet_Icc] with s hs hmem
    exact hs ⟨hmem.1, hmem.2.trans ht.2⟩
  have hb : |∫ t in uᵢ..u, Real.exp (-A t) * S t| ≤ C * ∫ t in uᵢ..u, g t := by
    calc
      _ ≤ ∫ t in uᵢ..u, |Real.exp (-A t) * S t| :=
        intervalIntegral.abs_integral_le_integral_abs hu
      _ ≤ ∫ t in uᵢ..u, C * g t := by
        apply intervalIntegral.integral_mono_ae_restrict hu hi.abs (hg.const_mul C)
        filter_upwards [ae_restrict_of_ae hsource, ae_restrict_mem measurableSet_Icc]
          with t hs ht
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        calc
          _ ≤ 1 * |S t| := mul_le_mul_of_nonneg_right
            (by simpa using Real.exp_le_exp.mpr (neg_nonpos.mpr (hAnonneg t ht))) (abs_nonneg _)
          _ ≤ C * g t := by simpa using (hs ht).2
      _ = _ := intervalIntegral.integral_const_mul _ _
  rw [ac_transport_integrating_factor hJ ha hODE' hzero, abs_mul,
    abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (∫ t in uᵢ..u, a t) * (C * ∫ t in uᵢ..u, g t) :=
      mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ ≤ Real.exp Λ * (C * ∫ t in uᵢ..u, g t) :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hΛ) ((abs_nonneg _).trans hb)
    _ = _ := by ring

/-- The same incoming transport bound with a possibly infinite source
integral; paper `e1a0fd5`, `eq:renormalized-remainder-pointwise`,
`equations.tex` lines 1100–1124. No integrability assumption on `g` is needed. -/
theorem ac_transport_lintegral_bound {J a S g : ℝ → ℝ} {uᵢ u C Λ : ℝ}
    (hu : uᵢ ≤ u) (hJ : AbsolutelyContinuousOnInterval J uᵢ u)
    (ha : IntervalIntegrable a volume uᵢ u)
    (hODE : ∀ᵐ t ∂volume, t ∈ Icc uᵢ u → HasDerivAt J (a t * J t + S t) t)
    (hzero : J uᵢ = 0) (hapos : ∀ᵐ t ∂volume, t ∈ Icc uᵢ u → 0 ≤ a t)
    (hΛ : (∫ t in uᵢ..u, a t) ≤ Λ)
    (hsource : ∀ᵐ t ∂volume, t ∈ Icc uᵢ u → 0 ≤ g t ∧ |S t| ≤ C * g t) :
    ENNReal.ofReal |J u| ≤ ENNReal.ofReal (C * Real.exp Λ) *
      ∫⁻ t in Ioc uᵢ u, ENNReal.ofReal (g t) := by
  have hODE' : ∀ᵐ t ∂volume, t ∈ uIcc uᵢ u →
      HasDerivAt J (a t * J t + S t) t := by
    simpa only [uIcc_of_le hu] using hODE
  have hAnonneg (t : ℝ) (ht : t ∈ Icc uᵢ u) : 0 ≤ ∫ s in uᵢ..t, a s := by
    apply intervalIntegral.integral_nonneg_of_ae_restrict ht.1
    filter_upwards [ae_restrict_of_ae hapos, ae_restrict_mem measurableSet_Icc] with s hs hmem
    exact hs ⟨hmem.1, hmem.2.trans ht.2⟩
  have hnorm := enorm_integral_le_lintegral_enorm
    (μ := volume.restrict (Ioc uᵢ u))
    (fun t ↦ Real.exp (-(∫ s in uᵢ..t, a s)) * S t)
  simp only [Real.enorm_eq_ofReal_abs] at hnorm
  have hbound : (∫⁻ t in Ioc uᵢ u,
      ENNReal.ofReal |Real.exp (-(∫ s in uᵢ..t, a s)) * S t|) ≤
      ENNReal.ofReal C * ∫⁻ t in Ioc uᵢ u, ENNReal.ofReal (g t) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_of_ae hsource, ae_restrict_mem measurableSet_Ioc]
      with t hs ht
    have ht' := Ioc_subset_Icc_self ht
    calc
      _ ≤ ENNReal.ofReal (C * g t) := by
        apply ENNReal.ofReal_le_ofReal
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        calc
          _ ≤ 1 * |S t| := mul_le_mul_of_nonneg_right
            (by simpa using Real.exp_le_exp.mpr (neg_nonpos.mpr (hAnonneg t ht')))
            (abs_nonneg _)
          _ ≤ _ := by simpa using (hs ht').2
      _ = _ := by
        rw [mul_comm C, ENNReal.ofReal_mul (hs ht').1, mul_comm]
  rw [ac_transport_integrating_factor hJ ha hODE' hzero, abs_mul,
    abs_of_pos (Real.exp_pos _), ENNReal.ofReal_mul (Real.exp_pos _).le]
  have hnorm' : ENNReal.ofReal |∫ t in uᵢ..u,
      Real.exp (-(∫ s in uᵢ..t, a s)) * S t| ≤
      ∫⁻ t in Ioc uᵢ u, ENNReal.ofReal |Real.exp (-(∫ s in uᵢ..t, a s)) * S t| := by
    rw [intervalIntegral.integral_of_le hu]
    exact hnorm
  calc
    _ ≤ ENNReal.ofReal (Real.exp (∫ t in uᵢ..u, a t)) *
        (ENNReal.ofReal C * ∫⁻ t in Ioc uᵢ u, ENNReal.ofReal (g t)) := by
      exact mul_le_mul le_rfl (hnorm'.trans hbound) zero_le zero_le
    _ ≤ ENNReal.ofReal (Real.exp Λ) *
        (ENNReal.ofReal C * ∫⁻ t in Ioc uᵢ u, ENNReal.ofReal (g t)) := by
      exact mul_le_mul (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hΛ))
        le_rfl zero_le zero_le
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_comm C]

end AcExtensionPrinciple

end
