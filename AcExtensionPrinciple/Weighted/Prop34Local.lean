module

public import AcExtensionPrinciple.Weighted.Prop34Source
public import AcExtensionPrinciple.Weighted.Prop34Measure
public import AcExtensionPrinciple.ACDatum.OutgoingCalculus

/-!
# Local finite energy of the actual frozen formula

Paper `e1a0fd5`, `eq:frozen-solution-operators`, lines 1265–1276. The coefficient,
integrating-factor and weight bounds are discharged from the class; finite source and initial energy
are the input norms.
-/

public section

namespace AcExtensionPrinciple.StandingFull

open Set Filter MeasureTheory
open scoped ENNReal

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Weighted initial energy implies initial L² on every off-axis interval.
Paper `e1a0fd5`, `eq:renormalized-initial-energy`, lines 1112–1124 and 1275. -/
theorem frozen_initial_square_lt_top {u₀ c : ℝ} {J₀ : ℝ → ℝ}
    (hi : ui ≤ u₀) (hu₀ : u₀ < 0) (hc : u₀ < c) (_hc0 : c ≤ 0)
    (hinitial : (∫⁻ v in Ioc u₀ 0, ENNReal.ofReal
      (S.r u₀ v * J₀ v ^ 2 / ((1 - S.mu u₀ v) ^ 2 * S.lam u₀ v))) < ⊤) :
    (∫⁻ v in Icc c 0, ENNReal.ofReal (J₀ v ^ 2)) < ⊤ := by
  let d := Real.exp (-Bstar ui S) * (c - u₀)
  have hd : 0 < d := mul_pos (Real.exp_pos _) (sub_pos.mpr hc)
  have hsub : Icc c 0 ⊆ Ioc u₀ 0 := fun v hv => ⟨hc.trans_le hv.1, hv.2⟩
  have hb (v : ℝ) (hv : v ∈ Icc c 0) :
      J₀ v ^ 2 ≤ d⁻¹ * (S.r u₀ v * J₀ v ^ 2 /
        ((1 - S.mu u₀ v) ^ 2 * S.lam u₀ v)) := by
    have hp : (u₀, v) ∈ pastTriangle ui := ⟨hi, hu₀, (hsub hv).1.le, hv.2⟩
    have hr := h.r_pos hp (hsub hv).1
    have hl := h.lam_pos hp
    have hg := sub_pos.mpr (h.mu_bounds hp).2
    have hgap : 1 - S.mu u₀ v ≤ 1 := by linarith [(h.mu_bounds hp).1]
    have hden : (1 - S.mu u₀ v) ^ 2 * S.lam u₀ v ≤ 1 := by
      have hs : (1 - S.mu u₀ v) ^ 2 ≤ 1 := by nlinarith
      exact (mul_le_mul_of_nonneg_right hs hl.le).trans
        (by simpa using (h.lam_bounds hp).2)
    have hdr : d ≤ S.r u₀ v :=
      (mul_le_mul_of_nonneg_left (sub_le_sub_right hv.1 u₀)
        (Real.exp_pos _).le).trans (h.radius_bounds hp).1
    have hw : d ≤ S.r u₀ v / ((1 - S.mu u₀ v) ^ 2 * S.lam u₀ v) :=
      hdr.trans ((le_div_iff₀ (mul_pos (sq_pos_of_pos hg) hl)).mpr
        (mul_le_of_le_one_right hr.le hden))
    have hs := mul_le_mul_of_nonneg_right hw (sq_nonneg (J₀ v))
    calc
      _ = d⁻¹ * (d * J₀ v ^ 2) := by rw [← mul_assoc, inv_mul_cancel₀ hd.ne', one_mul]
      _ ≤ d⁻¹ * ((S.r u₀ v / ((1 - S.mu u₀ v) ^ 2 * S.lam u₀ v)) * J₀ v ^ 2) :=
        mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hd.le)
      _ = _ := by ring
  calc
    _ ≤ ∫⁻ v in Icc c 0, ENNReal.ofReal d⁻¹ * ENNReal.ofReal
        (S.r u₀ v * J₀ v ^ 2 / ((1 - S.mu u₀ v) ^ 2 * S.lam u₀ v)) := by
      apply setLIntegral_mono' measurableSet_Icc
      intro v hv
      rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hd.le)]
      exact ENNReal.ofReal_le_ofReal (hb v hv)
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal d⁻¹ * ∫⁻ v in Ioc u₀ 0, ENNReal.ofReal
        (S.r u₀ v * J₀ v ^ 2 / ((1 - S.mu u₀ v) ^ 2 * S.lam u₀ v)) := by
      gcongr
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hinitial

/-- The incoming source multiplier has a measurable extension and a finite
bound on each proper rectangle. Paper `e1a0fd5`, lines 1268–1276. -/
theorem frozen_source_coefficient_rectangle {u₀ b c : ℝ}
    (hi : ui ≤ u₀) (hab : u₀ ≤ b) (hbc : b < c) (hc0 : c ≤ 0) :
    ∃ A : ℝ × ℝ → ℝ, Measurable A ∧
      EqOn (fun p => 3 * S.kappa p.1 p.2 * S.nu p.1 p.2 * S.dvphi p.1 p.2) A
        (Icc u₀ b ×ˢ Icc c 0) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ Icc u₀ b ×ˢ Icc c 0, |A p| ≤ C := by
  classical
  let K := Icc u₀ b ×ˢ Icc c 0
  have hb0 : b < 0 := hbc.trans_le hc0
  have hsub : K ⊆ pastTriangle ui := fun p hp =>
    ⟨hi.trans hp.1.1, hp.1.2.trans_lt hb0,
      (hp.1.2.trans_lt (hbc.trans_le hp.2.1)).le, hp.2.2⟩
  have hr := h.regularCenter.continuous_r.mono hsub
  have hm := h.regularCenter.continuous_m.mono hsub
  have hl := h.regularCenter.continuous_lam.mono hsub
  have hn := h.regularCenter.continuous_nu.mono hsub
  have hmu : ContinuousOn (fun p => S.mu p.1 p.2) K :=
    (hm.const_mul 2).div hr (fun p hp =>
      (h.r_pos (hsub hp) (hp.1.2.trans_lt (hbc.trans_le hp.2.1))).ne')
  have hk : ContinuousOn (fun p => S.kappa p.1 p.2) K :=
    hl.div (continuousOn_const.sub hmu) (fun p hp => (sub_pos.mpr (h.mu_bounds (hsub hp)).2).ne')
  have hdv := (h.dvphi_continuous_rectangle (hi.trans hab) hc0 hb0 hbc le_rfl).mono
    (show K ⊆ Icc ui b ×ˢ Icc c 0 from fun p hp =>
      ⟨⟨hi.trans hp.1.1, hp.1.2⟩, hp.2⟩)
  let A₀ := fun p : ℝ × ℝ => 3 * S.kappa p.1 p.2 * S.nu p.1 p.2 * S.dvphi p.1 p.2
  have hA₀ : ContinuousOn A₀ K := ((hk.const_mul 3).mul hn).mul hdv
  let A := K.piecewise A₀ (fun _ => 0)
  have hA : Measurable A := hA₀.measurable_piecewise continuousOn_const
    (measurableSet_Icc.prod measurableSet_Icc)
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hA₀
  refine ⟨A, hA, fun p hp => (piecewise_eq_of_mem K A₀ (fun _ => 0) hp).symm,
    max C 0, le_max_right _ _, ?_⟩
  intro p hp
  have he : A p = A₀ p := piecewise_eq_of_mem K A₀ (fun _ => 0) hp
  rw [he]
  have hb : |A₀ p| ≤ C := by simpa only [Real.norm_eq_abs] using hC p hp
  exact hb.trans (le_max_left C 0)

/-- Finite initial and source energies give finite energy of the literal frozen formula on every
off-axis rectangle. All coefficient bounds come from the class. Paper `e1a0fd5`, lines 1268–1276. -/
theorem weightedFrozenSolution_rectangle_energy_lt_top {u₀ U b c : ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hab : u₀ ≤ b) (hbU : b ≤ U)
    (hbc : b < c) (hc0 : c ≤ 0) {J₀ : ℝ → ℝ} {F : ℝ × ℝ → ℝ}
    (hJ₀ : Measurable J₀) (hF : Measurable F)
    (hinitial : (∫⁻ v in Ioc u₀ 0, ENNReal.ofReal
      (S.r u₀ v * J₀ v ^ 2 / ((1 - S.mu u₀ v) ^ 2 * S.lam u₀ v))) < ⊤)
    (hsource : weightedSourceNormSq S u₀ U F < ⊤) :
    (∫⁻ u in Icc u₀ b, ∫⁻ v in Icc c 0,
      ENNReal.ofReal (weightedRemainderDensity S (u, v) *
        |weightedFrozenSolution S u₀ J₀ F (u, v)| ^ 2)) < ⊤ := by
  have hgap0 := h.initialGap_pos
  obtain ⟨A, hA, heA, C, hC0, hC⟩ := h.frozen_source_coefficient_rectangle hi hab hbc hc0
  let H := fun p => A p * F p
  have hH : Measurable H := hA.mul hF
  have hHs : (∫⁻ v in Icc c 0, ∫⁻ s in Icc u₀ b,
      ENNReal.ofReal (|H (s, v)| ^ 2)) < ⊤ := by
    calc
      _ ≤ ∫⁻ v in Icc c 0, ∫⁻ s in Icc u₀ b,
          ENNReal.ofReal (C ^ 2) * ENNReal.ofReal (|F (s, v)| ^ 2) := by
        apply setLIntegral_mono' measurableSet_Icc
        intro v hv
        apply setLIntegral_mono' measurableSet_Icc
        intro s hs
        rw [← ENNReal.ofReal_mul (sq_nonneg C)]
        apply ENNReal.ofReal_le_ofReal
        dsimp only [H]
        rw [abs_mul, mul_pow]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (hC _ ⟨hs, hv⟩) 2)
          (sq_nonneg _)
      _ = ENNReal.ofReal (C ^ 2) * ∫⁻ v in Icc c 0, ∫⁻ s in Icc u₀ b,
          ENNReal.ofReal (|F (s, v)| ^ 2) := by
        simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (h.weighted_source_rectangle_square_lt_top hi hU hbU hbc hF hsource)
  let D := weightedTruncatedDomain u₀ U
  have hsub := weightedTruncatedDomain_subset_triangle hi hU
  obtain ⟨d, hd, hbounds⟩ := h.regularCenter.localBV.expansion_bounds D
    (isCompact_weightedTruncatedDomain u₀ U) hsub
  let g := weightedGapConstant ui S
  have hg : 0 < g := h.weightedGapConstant_pos
  let K := (1 / initialGap ui S + 1) / Real.exp (-Bstar ui S)
  apply frozen_cutoff_energy_lt_top_of_formula
    (K := K) (C := (1 / d) / (g ^ 2 * d)) (by positivity) hH hJ₀
    (h.frozen_initial_square_lt_top hi (hab.trans_lt (hbU.trans_lt hU))
      (hab.trans_lt hbc) hc0 hinitial) hHs
  · intro u hu v hv
    have hp : (u, v) ∈ pastTriangle ui :=
      ⟨hi.trans hu.1, hu.2.trans_lt (hbU.trans_lt hU),
        (hu.2.trans_lt (hbc.trans_le hv.1)).le, hv.2⟩
    have hip : (u₀, v) ∈ pastTriangle ui :=
      ⟨hi, hab.trans_lt (hbU.trans_lt hU), (hab.trans_lt (hbc.trans_le hv.1)).le, hv.2⟩
    have he : (∫ s in u₀..u, H (s, v)) =
        ∫ s in u₀..u, 3 * S.kappa s v * S.nu s v * S.dvphi s v * F (s, v) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le hu.1] at hs
      dsimp only [H]
      rw [← heA ⟨⟨hs.1, hs.2.trans hu.2⟩, hv⟩]
    rw [he]
    dsimp only [weightedFrozenSolution]
    rw [abs_div, abs_of_pos (h.kappa_pos hp)]
    have hn : |S.kappa u₀ v * J₀ v + ∫ s in u₀..u,
        3 * S.kappa s v * S.nu s v * S.dvphi s v * F (s, v)| ≤
          (1 / initialGap ui S + 1) * (|J₀ v| + |∫ s in u₀..u,
            3 * S.kappa s v * S.nu s v * S.dvphi s v * F (s, v)|) := by
      apply (abs_add_le _ _).trans
      rw [abs_mul, abs_of_pos (h.kappa_pos hip)]
      have hk := mul_le_mul_of_nonneg_right (h.kappa_upper hip) (abs_nonneg (J₀ v))
      have hki : 0 ≤ 1 / initialGap ui S := by positivity
      nlinarith [abs_nonneg (J₀ v), mul_nonneg hki (abs_nonneg (∫ s in u₀..u,
        3 * S.kappa s v * S.nu s v * S.dvphi s v * F (s, v)))]
    calc
      _ ≤ ((1 / initialGap ui S + 1) * (|J₀ v| + |∫ s in u₀..u,
          3 * S.kappa s v * S.nu s v * S.dvphi s v * F (s, v)|)) /
            Real.exp (-Bstar ui S) :=
        div_le_div₀ (by positivity) hn (Real.exp_pos _) (h.kappa_lower hp)
      _ = _ := by dsimp only [K]; ring
  · intro u hu v hv
    have hpD : (u, v) ∈ D := ⟨hu.1, hu.2.trans hbU,
      (hu.2.trans_lt (hbc.trans_le hv.1)).le, hv.2⟩
    have hden : g ^ 2 * d ≤ (1 - S.mu u v) ^ 2 * S.lam u v :=
      mul_le_mul (pow_le_pow_left₀ hg.le (h.mass_gap_lower (hsub hpD)) 2)
        (hbounds (u, v) hpD).1 hd.le (sq_nonneg _)
    exact div_le_div₀ (by positivity) (hbounds (u, v) hpD).2 (by positivity) hden

end AcExtensionPrinciple.StandingFull

end
