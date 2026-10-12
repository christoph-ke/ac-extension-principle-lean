module

public import AcExtensionPrinciple.Observability.PropA4VolterraDomination

/-!
# Single incoming potential integrals on the exterior domain

Paper `e1a0fd5`, lines 1793–1811. The incoming radius separation and
positive kernel comparison give the half-power and negative-half-power
tails used in the radial scalar derivative estimate.
-/

public section

namespace AcExtensionPrinciple
namespace PropA4

open Set MeasureTheory

/-- The potential has the pointwise radius-cubed bound on entered exterior
rays. Paper `e1a0fd5`, lines 1757–1759 and 1793–1811. -/
theorem potential_le_radius_power {b T K P s t : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P) (ht : 0 ≤ t)
    (hp : (s, t) ∈ chartInterior (chartCylinder h.g T) S) (hcut : 32 * P ≤ S.r s t)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P) :
    chartPotential S s t ≤ 4 * P * S.r s t ^ (-3 : ℝ) := by
  have hg := exterior_geometry_of_mass_bound h hP ht hp hcut hmass
  have hv := potential_le_radial_density h hP ht hp hcut hmass
  rw [Real.rpow_neg hp.2.le, Real.rpow_ofNat _ 3]
  have hn : 4 * P * S.lam s t ≤ 4 * P := by nlinarith only [hP, hg.2.2.2]
  exact hv.trans (by simpa only [div_eq_mul_inv] using
    div_le_div_of_nonneg_right hn (pow_nonneg hp.2.le 3))

/-- Positive one-dimensional kernels preserve absolute-value domination.
The premises are discharged by chart continuity on characteristic segments.
Paper `e1a0fd5`, lines 1793–1811. -/
theorem interval_abs_integral_le_of_domination {V F G : ℝ → ℝ} {s t : ℝ}
    (hts : t ≤ s) (hV : ContinuousOn V (Icc t s))
    (hF : ContinuousOn F (Icc t s)) (hG : ContinuousOn G (Icc t s))
    (hpos : ∀ x ∈ Icc t s, 0 ≤ V x) (hbound : ∀ x ∈ Icc t s, |F x| ≤ G x) :
    |∫ x in t..s, V x * F x| ≤ ∫ x in t..s, V x * G x := by
  have hi : IntervalIntegrable (fun x => V x * F x) volume t s := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hts]
    exact hV.mul hF
  have hj : IntervalIntegrable (fun x => V x * G x) volume t s := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hts]
    exact hV.mul hG
  have hup := intervalIntegral.integral_mono_on hts hi hj (fun x hx =>
    mul_le_mul_of_nonneg_left ((le_abs_self (F x)).trans (hbound x hx)) (hpos x hx))
  have hlo := intervalIntegral.integral_mono_on hts hi.neg hj (fun x hx => by
    have hh := mul_le_mul_of_nonneg_left ((neg_le_abs (F x)).trans (hbound x hx)) (hpos x hx)
    simpa only [Pi.neg_apply, mul_neg] using hh)
  simp only [Pi.neg_apply] at hlo
  rw [intervalIntegral.integral_neg] at hlo
  exact abs_le.mpr ⟨by linarith only [hlo], hup⟩

/-- Exact incoming radial-power tail for the chart's actual potential.
Paper `e1a0fd5`, lines 1793–1811. -/
theorem incoming_power_kernel_le {b T K P s t q : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P) (ht : 0 ≤ t)
    (hp : (s, t) ∈ chartInterior (chartCylinder h.g T) S) (hcut : 32 * P ≤ S.r s t)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P) (hq : q < 2) :
    (∫ σ in t..s, chartPotential S σ t * S.r σ t ^ q) ≤
      8 * P / (2 - q) * S.r s t ^ (q - 2) := by
  have htri := h.volterra_triangle_subset ht hp
  have hline : MapsTo (fun σ : ℝ => (σ, t)) (Icc t s) (chartTriangle t s) :=
    fun σ hσ => ⟨le_rfl, hσ.1, hσ.2⟩
  have hPc : ContinuousOn (fun p : ℝ × ℝ => chartPotential S p.1 p.2) (chartTriangle t s) :=
    continuous_potential_on h htri
  have hRc : ContinuousOn (fun p : ℝ × ℝ => S.r p.1 p.2 ^ q) (chartTriangle t s) :=
    (h.continuous_r.mono (fun p hp => (htri hp).1)).rpow_const
      (fun p hp => Or.inl (htri hp).2.ne')
  have hfc : ContinuousOn (fun σ => chartPotential S σ t * S.r σ t ^ q) (Icc t s) :=
    (hPc.mul hRc).comp (f := fun σ : ℝ => (σ, t)) (by fun_prop) hline
  have hpos : ∀ σ ∈ Icc t s, 0 < S.r s t + (s - σ) / 2 := by
    intro σ hσ
    linarith only [hp.2, hσ.2]
  have hgc : ContinuousOn (fun σ : ℝ => 4 * P * (S.r s t + (s - σ) / 2) ^ (q - 3))
      (Icc t s) :=
    continuousOn_const.mul ((show Continuous (fun σ : ℝ => S.r s t + (s - σ) / 2)
      by fun_prop).continuousOn.rpow_const (fun σ hσ => Or.inl (hpos σ hσ).ne'))
  have hi : IntervalIntegrable (fun σ => chartPotential S σ t * S.r σ t ^ q) volume t s := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hp.1.2.2.2]
    exact hfc
  have hj : IntervalIntegrable (fun σ : ℝ => 4 * P * (S.r s t + (s - σ) / 2) ^ (q - 3))
      volume t s := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hp.1.2.2.2]
    exact hgc
  have hm := intervalIntegral.integral_mono_on hp.1.2.2.2 hi hj (fun σ hσ => by
    have hσint := htri (hline hσ)
    have hrord := (h.volterra_radius_order ht hp hσ ⟨le_rfl, hσ.1⟩).1
    have hpot := potential_le_radius_power h hP ht hσint (hcut.trans hrord) hmass
    have hsep := incoming_radius_separation h hP ht hp hcut hmass hσ
    have hpow := Real.rpow_le_rpow_of_nonpos (hpos σ hσ) hsep (by linarith only [hq] : q - 3 ≤ 0)
    calc
      _ ≤ (4 * P * S.r σ t ^ (-3 : ℝ)) * S.r σ t ^ q :=
        mul_le_mul_of_nonneg_right hpot (Real.rpow_nonneg hσint.2.le q)
      _ = 4 * P * S.r σ t ^ (q - 3) := by
        rw [mul_assoc, ← Real.rpow_add hσint.2]
        congr 2
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity))
  rw [intervalIntegral.integral_const_mul] at hm
  have hb := incoming_affine_power_integral_le hp.2 hp.1.2.2.2
    (by linarith only [hq] : q - 1 < 1)
  rw [show (q - 1) - 2 = q - 3 by ring, show (q - 1) - 1 = q - 2 by ring] at hb
  apply hm.trans
  apply (mul_le_mul_of_nonneg_left hb (show 0 ≤ 4 * P by positivity)).trans_eq
  have hq0 : 2 - q ≠ 0 := by linarith only [hq]
  rw [show 1 - (q - 1) = 2 - q by ring]
  field_simp [hq0]
  ring

/-- A weighted input bound gives the single incoming potential tail.
Paper `e1a0fd5`, lines 1793–1811. -/
theorem incoming_weighted_integral_bound {b T K P s t q A : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P) (ht : 0 ≤ t)
    (hp : (s, t) ∈ chartInterior (chartCylinder h.g T) S) (hcut : 32 * P ≤ S.r s t)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P)
    (hq : q < 2) (hA : 0 ≤ A) {F : ℝ × ℝ → ℝ}
    (hF : ContinuousOn F (chartTriangle t s))
    (hbound : ∀ p ∈ chartTriangle t s, |F p| ≤ A * S.r p.1 p.2 ^ q) :
    |∫ σ in t..s, chartPotential S σ t * F (σ, t)| ≤
      A * (8 * P / (2 - q) * S.r s t ^ (q - 2)) := by
  have htri := h.volterra_triangle_subset ht hp
  have hline : MapsTo (fun σ : ℝ => (σ, t)) (Icc t s) (chartTriangle t s) :=
    fun σ hσ => ⟨le_rfl, hσ.1, hσ.2⟩
  have hPc : ContinuousOn (fun p : ℝ × ℝ => chartPotential S p.1 p.2) (chartTriangle t s) :=
    continuous_potential_on h htri
  have hRc : ContinuousOn (fun p : ℝ × ℝ => S.r p.1 p.2 ^ q) (chartTriangle t s) :=
    (h.continuous_r.mono (fun p hp => (htri hp).1)).rpow_const
      (fun p hp => Or.inl (htri hp).2.ne')
  have hV := hPc.comp (f := fun σ : ℝ => (σ, t)) (by fun_prop) hline
  have hFc := hF.comp (f := fun σ : ℝ => (σ, t)) (by fun_prop) hline
  have hGc : ContinuousOn (fun σ : ℝ => A * S.r σ t ^ q) (Icc t s) :=
    (continuousOn_const.mul hRc).comp
    (f := fun σ : ℝ => (σ, t)) (by fun_prop) hline
  have hm := interval_abs_integral_le_of_domination hp.1.2.2.2 hV hFc hGc
    (fun σ hσ => h.potential_nonneg (htri (hline hσ)).1) (fun σ hσ => hbound _ (hline hσ))
  have he : (∫ σ in t..s, chartPotential S σ t * (A * S.r σ t ^ q)) =
      A * (∫ σ in t..s, chartPotential S σ t * S.r σ t ^ q) := by
    simp only [mul_left_comm _ A, intervalIntegral.integral_const_mul]
  dsimp only [Function.comp_def] at hm
  rw [he] at hm
  exact hm.trans (mul_le_mul_of_nonneg_left
    (incoming_power_kernel_le h hP ht hp hcut hmass hq) hA)

end PropA4
end AcExtensionPrinciple

end
