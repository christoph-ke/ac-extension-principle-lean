module

public import AcExtensionPrinciple.ScalarBound.StripCoefficients
public import AcExtensionPrinciple.Reduced.OutgoingRay

/-!
# Normalized incoming-expansion comparisons on strips

Paper commit `e1a0fd5`, `equations.tex`
lines 441–470, `eq:scalar-bound-strip-geometry`. The lower ratio bound
completes the displayed comparison; the main amplitude proof needs only
the monotonicity and difference bounds.
-/

public section

namespace AcExtensionPrinciple.StandingFull

open Set MeasureTheory

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The outgoing logarithmic ν identity, recovered from the integral
class. Paper `e1a0fd5`, `eq:logarithmic-expansions`, lines 445–450. -/
theorem scalar_log_neg_nu_primitive {u a b : ℝ} (hu : ui ≤ u) (hu0 : u < 0)
    (hua : u < a) (hab : a ≤ b) (hb0 : b ≤ 0) :
    IntervalPrimitive (fun v => Real.log (-S.nu u v))
      (fun v => S.kappa u v * S.varkappa u v) a b := by
  have hP : ∀ s ∈ Icc a b, IntervalPrimitive (S.nu u) (S.radiusCoeff u) a s :=
    fun s hs => h.regularCenter.localBV.nu_out u a s hs.1
      (outSeg_subset_offAxis hu hu0 hua (hs.2.trans hb0))
  have hn : ∀ s ∈ Icc a b, S.nu u s < 0 := fun s hs =>
    h.nu_neg (p := (u, s)) ⟨hu, hu0, (hua.trans_le hs.1).le, hs.2.trans hb0⟩
  have hac := positive_ac_log (intervalPrimitive_ac hab hP).neg
    (fun s hs => neg_pos.mpr (hn s (by simpa only [uIcc_of_le hab] using hs)))
  apply ac_integral_eq_sub hab hac
  filter_upwards [intervalPrimitive_ae_hasDerivAt hab hP] with s hs
  intro hsI
  exact OutgoingRay.log_neg_nu (r := S.r u) (m := S.m u) (lam := S.lam u)
    ((hs hsI).congr_deriv (S.radiusCoeff_eq u s)) (hn s ⟨hsI.1.le, hsI.2.le⟩)

/-- Uniform comparability, monotonicity and closeness of ν/ν₀.
The gap premise is G2. Paper `e1a0fd5`, `eq:scalar-bound-strip-geometry`, lines 445–470. -/
theorem scalar_strip_nu_ratio {u a b g : ℝ}
    (hu : ui ≤ u) (hu0 : u < 0) (hua : u < a) (hab : a ≤ b) (hb0 : b ≤ 0)
    (hg : 0 < g) (hwidth : b - a ≤ S.r u b / 2)
    (hgap : ∀ s ∈ Icc a b, g ≤ 1 - S.mu u s) :
    Real.exp (-1 / g) ≤ S.nu u a / S.nu u b ∧ S.nu u a / S.nu u b ≤ 1 ∧
      |S.nu u a / S.nu u b - 1| ≤ (2 / g) * (b - a) / S.r u b := by
  have hp : (u, b) ∈ pastTriangle ui := ⟨hu, hu0, (hua.trans_le hab).le, hb0⟩
  have hpA : (u, a) ∈ pastTriangle ui := ⟨hu, hu0, hua.le, hab.trans hb0⟩
  have hnA := h.nu_neg hpA
  have hnB := h.nu_neg hp
  change S.nu u a < 0 at hnA
  change S.nu u b < 0 at hnB
  have hr := h.r_pos hp (hua.trans_le hab)
  have hN := h.scalar_strip_neg_nu hu hu0 hua hab hb0
  have hi := h.scalar_log_neg_nu_primitive hu hu0 hua hab hb0
  have hI : (∫ s in a..b, S.kappa u s * S.varkappa u s) ≤ 1 / g := by
    have ht : (∫ s in a..b, S.kappa u s * S.varkappa u s) ≤
        (2 / (g * S.r u b)) * (b - a) := by
      calc
        _ ≤ ∫ s in a..b, 2 / (g * S.r u b) :=
          intervalIntegral.integral_mono_on hab hi.1 intervalIntegrable_const (by
            intro s hs
            have hps : (u, s) ∈ pastTriangle ui :=
              ⟨hu, hu0, (hua.trans_le hs.1).le, hs.2.trans hb0⟩
            have hm := h.mu_bounds hps
            have hl := h.lam_bounds hps
            have hrS := h.scalar_strip_radius hu hu0 (hua.trans_le hs.1) hs.2 hb0
              (by linarith [hs.1])
            have hden : g * S.r u b / 2 ≤ (1 - S.mu u s) * S.r u s := by
              have ht := mul_le_mul (hgap s hs) hrS.1 (by positivity : 0 ≤ S.r u b / 2)
                (sub_pos.mpr hm.2).le
              nlinarith
            have hnum : S.lam u s * S.mu u s ≤ 1 :=
              (mul_le_mul_of_nonneg_right hl.2 hm.1).trans (by simpa using hm.2.le)
            have hd := div_le_div₀ zero_le_one hnum (by positivity : 0 < g * S.r u b / 2) hden
            have he : S.kappa u s * S.varkappa u s =
                S.lam u s * S.mu u s / ((1 - S.mu u s) * S.r u s) := by
              unfold SSFields.kappa kappaOf SSFields.varkappa varkappaOf
              simp only [div_eq_mul_inv, mul_inv_rev]
              ring
            rw [he]
            exact hd.trans_eq (by field_simp))
        _ = _ := by simp only [intervalIntegral.integral_const, smul_eq_mul]; ring
    calc
      _ ≤ _ := ht
      _ ≤ (2 / (g * S.r u b)) * (S.r u b / 2) :=
        mul_le_mul_of_nonneg_left hwidth (by positivity)
      _ = _ := by field_simp
  have hlog : -1 / g ≤ Real.log (S.nu u a / S.nu u b) := by
    have he := hi.2
    dsimp only at he
    rw [show S.nu u a / S.nu u b = (-S.nu u a) / (-S.nu u b) by ring,
      Real.log_div (neg_ne_zero.mpr hnA.ne) (neg_ne_zero.mpr hnB.ne)]
    simp only [neg_div] at ⊢
    linarith
  have hratio : 0 < S.nu u a / S.nu u b := div_pos_of_neg_of_neg hnA hnB
  refine ⟨?_, ?_, ?_⟩
  · exact (Real.exp_le_exp.mpr hlog).trans_eq (Real.exp_log hratio)
  · rw [show S.nu u a / S.nu u b = (-S.nu u a) / (-S.nu u b) by ring]
    exact (div_le_one (neg_pos.mpr hnB)).mpr hN.2
  · have he : S.nu u a / S.nu u b - 1 = (S.nu u a - S.nu u b) / S.nu u b := by
      field_simp [hnB.ne]
    rw [he, abs_div, abs_of_neg hnB]
    have ht := div_le_div_of_nonneg_right
      (h.scalar_strip_nu_difference hu hu0 hua hab hb0 hg hwidth hgap) (neg_pos.mpr hnB).le
    exact ht.trans_eq (by field_simp [hnB.ne])

end AcExtensionPrinciple.StandingFull

end
