module

public import AcExtensionPrinciple.Weighted.Prop34FrozenEnergy
public import AcExtensionPrinciple.Weighted.Prop34IncomingDomain
public import AcExtensionPrinciple.Weighted.Prop34Measurable

/-!
# Global frozen energy bounds from the incoming formula

Paper `e1a0fd5`, `eq:frozen-solution-operators`, lines 1265–1276.
Proper incoming segments exhaust the triangle. The estimates require
finite source energy, with no prior global energy hypothesis on Z.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped ENNReal

/-- Convert a nonnegative incoming integral to its lower integral.
Paper `e1a0fd5`, lines 1268–1276, incoming energy integration. -/
theorem incoming_ofReal_integral_eq_lintegral {a b : ℝ} {f : ℝ → ℝ}
    (hab : a ≤ b) (hf : IntervalIntegrable f volume a b)
    (hnn : ∀ x ∈ Icc a b, 0 ≤ f x) :
    ENNReal.ofReal (∫ x in a..b, f x) = ∫⁻ x in Icc a b, ENNReal.ofReal (f x) := by
  rw [intervalIntegral.integral_of_le hab, ← restrict_Ioc_eq_restrict_Icc]
  exact ofReal_integral_eq_lintegral_ofReal
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hf)
    ((ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _
      (fun x hx => hnn x ⟨hx.1.le, hx.2⟩)))

/-- Convert a real ray bound to the extended nonnegative form used by
Tonelli. Paper `e1a0fd5`, lines 1268–1276. -/
theorem incoming_lintegral_bound_of_real {a b E A B : ℝ} {q g : ℝ → ℝ}
    (hab : a ≤ b) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hq : IntervalIntegrable q volume a b) (hg : IntervalIntegrable g volume a b)
    (hq0 : ∀ x ∈ Icc a b, 0 ≤ q x) (hg0 : ∀ x ∈ Icc a b, 0 ≤ g x)
    (hbound : (∫ x in a..b, q x) ≤ A * E + B * ∫ x in a..b, g x) :
    (∫⁻ x in Icc a b, ENNReal.ofReal (q x)) ≤
      ENNReal.ofReal A * ENNReal.ofReal E +
        ENNReal.ofReal B * ∫⁻ x in Icc a b, ENNReal.ofReal (g x) := by
  rw [← incoming_ofReal_integral_eq_lintegral hab hq hq0,
    ← incoming_ofReal_integral_eq_lintegral hab hg hg0]
  exact (ENNReal.ofReal_le_ofReal hbound).trans (by
    simpa only [ENNReal.ofReal_mul hA, ENNReal.ofReal_mul hB] using
      (ENNReal.ofReal_add_le : ENNReal.ofReal (A * E + B * ∫ x in a..b, g x) ≤ _))

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Both energy densities are continuous on every proper incoming segment.
Paper `e1a0fd5`, lines 1268–1276. -/
theorem weighted_densities_continuous_in {a b v : ℝ}
    (_hab : a ≤ b) (ha : ui ≤ a) (hb : b < 0) (hbv : b < v) (hv : v ≤ 0) :
    ContinuousOn (fun x => weightedRemainderDensity S (x, v)) (Icc a b) ∧
      ContinuousOn (fun x => weightedSourceDensity S (x, v)) (Icc a b) := by
  have hsub := inSeg_subset_triangle ha hb hbv.le hv
  have hp (x : ℝ) (hx : x ∈ Icc a b) : (x, v) ∈ pastTriangle ui :=
    ⟨ha.trans hx.1, hx.2.trans_lt hb, (hx.2.trans_lt hbv).le, hv⟩
  have hr := continuous_in h.regularCenter.continuous_r hsub
  have hm := continuous_in h.regularCenter.continuous_m hsub
  have hl := continuous_in h.regularCenter.continuous_lam hsub
  have hn := continuous_in h.regularCenter.continuous_nu hsub
  have hmu : ContinuousOn (fun x => S.mu x v) (Icc a b) :=
    (hm.const_mul 2).div hr
      (fun x hx => (h.r_pos (hp x hx) (hx.2.trans_lt hbv)).ne')
  have ht := hn.neg.div ((continuousOn_const.sub hmu).pow 2)
    (fun x hx => (sq_pos_of_pos (sub_pos.mpr (h.mu_bounds (hp x hx)).2)).ne')
  constructor
  · apply (ht.div hl (fun x hx => (h.lam_pos (hp x hx)).ne')).congr
    intro x _
    simp [weightedRemainderDensity, div_div]
  · apply (ht.mul hl).congr
    intro x _
    simp [weightedSourceDensity, div_mul_eq_mul_div]

/-- The actual frozen formula obeys the lower-integral energy estimate on
almost every ray of each off-axis rectangle. Paper `e1a0fd5`,
`eq:frozen-solution-operators`, lines 1265–1276. -/
theorem weightedFrozenSolution_ray_lintegral_bound_ae {u₀ U b c δ ε : ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (hab : u₀ ≤ b) (hbU : b ≤ U)
    (hbc : b < c) (hc0 : c ≤ 0) (hδ : δ < 1 / 3)
    (hsmall : WeightedLateSmallness ui S u₀ δ ε)
    (J₀ : ℝ → ℝ) {F : ℝ × ℝ → ℝ} (hF : Measurable F)
    (hsource : weightedSourceNormSq S u₀ U F < ⊤) :
    ∀ᵐ v ∂volume.restrict (Icc c 0),
      (∫⁻ s in Icc u₀ b, ENNReal.ofReal (weightedRemainderDensity S (s, v) *
        |weightedFrozenSolution S u₀ J₀ F (s, v)| ^ 2)) ≤
      ENNReal.ofReal (((1 - 3 * δ) / 2)⁻¹) * ENNReal.ofReal
        (S.r u₀ v * J₀ v ^ 2 / ((1 - S.mu u₀ v) ^ 2 * S.lam u₀ v)) +
      ENNReal.ofReal ((18 * ε ^ 2 / (1 - 3 * δ)) * ((1 - 3 * δ) / 2)⁻¹) *
        ∫⁻ s in Icc u₀ b, ENNReal.ofReal (weightedSourceDensity S (s, v) * |F (s, v)| ^ 2) := by
  filter_upwards [h.weightedFrozenSolution_ray_energy_bound_ae hi hU hab hbU hbc hc0
      hδ hsmall J₀ hF hsource,
    h.weightedFrozenSolution_ac_ae_of_finite_source hi hU hab hbU hbc J₀ hF hsource,
    h.weighted_source_square_integrable_ae_rectangle hi hU hab hbU hbc hF hsource,
    ae_restrict_mem measurableSet_Icc] with v hbound hJ hFs hv
  have hc : 0 < 1 - 3 * δ := by linarith
  obtain ⟨hw, hs⟩ := h.weighted_densities_continuous_in hab hi (hbU.trans_lt hU)
    (hbc.trans_le hv.1) hv.2
  have hq : IntervalIntegrable (fun s => weightedRemainderDensity S (s, v) *
      |weightedFrozenSolution S u₀ J₀ F (s, v)| ^ 2) volume u₀ b :=
    (hw.mul (by simpa only [uIcc_of_le hab, sq_abs] using
      hJ.1.continuousOn.fun_pow 2)).intervalIntegrable_of_Icc hab
  have hg : IntervalIntegrable (fun s => weightedSourceDensity S (s, v) * |F (s, v)| ^ 2)
      volume u₀ b := by
    simpa only [sq_abs] using hFs.continuousOn_mul
      (by simpa only [uIcc_of_le hab] using hs)
  have hp (s : ℝ) (hs : s ∈ Icc u₀ b) : (s, v) ∈ pastTriangle ui :=
    ⟨hi.trans hs.1, (hs.2.trans hbU).trans_lt hU,
      (hs.2.trans_lt (hbc.trans_le hv.1)).le, hv.2⟩
  apply incoming_lintegral_bound_of_real hab (by positivity) (by positivity) hq hg
  · intro s hs
    unfold weightedRemainderDensity
    exact mul_nonneg (div_nonneg (neg_pos.mpr (h.nu_neg (hp s hs))).le
      (mul_nonneg (sq_nonneg _) (h.lam_pos (hp s hs)).le)) (sq_nonneg _)
  · intro s hs
    unfold weightedSourceDensity
    exact mul_nonneg (div_nonneg (mul_nonneg (neg_pos.mpr (h.nu_neg (hp s hs))).le
      (h.lam_pos (hp s hs)).le) (sq_nonneg _)) (sq_nonneg _)
  · convert hbound using 1
    simp only [div_eq_mul_inv]
    ring

end StandingFull

end AcExtensionPrinciple

end
