module

public import AcExtensionPrinciple.LateCylinder.Source
public import AcExtensionPrinciple.Decay.RadiusTransport

/-!
# Dilution of the nonlinear remainder

Paper `e1a0fd5`, `eq:remainder-dilution`, equations.tex lines 808–815.
The old remainder propagates with the homogeneous λ factor; the new
exterior source is small. Incoming radius growth dilutes the old term.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory

/-- A small cubic source and a positive mass gap bound the datum source.
Paper `e1a0fd5`, `eq:small-exterior-source`, lines 800–812. -/
theorem datum_source_bound_of_cubic {r nu mu A B eps g : ℝ}
    (hr : 0 < r) (hn : nu < 0) (hg : 0 < g) (hgap : g ≤ 1 - mu)
    (hB : 0 ≤ B * eps) (hs : |A * (A ^ 2 - 3 * mu)| ≤ B * eps) :
    |-(gammaOf nu mu) / r ^ 2 * A * (A ^ 2 - 3 * mu)| ≤
      (B * eps / g) * (-nu / r ^ 2) := by
  have hgap0 : 0 < 1 - mu := hg.trans_le hgap
  have he : |-(gammaOf nu mu) / r ^ 2 * A * (A ^ 2 - 3 * mu)| =
      (-nu / r ^ 2) * (|A * (A ^ 2 - 3 * mu)| / (1 - mu)) := by
    rw [mul_assoc, abs_mul, abs_div]
    simp only [gammaOf, abs_neg, abs_div, abs_of_neg hn,
      abs_of_pos hgap0, abs_of_pos (sq_pos_of_pos hr)]
    ring
  rw [he, mul_comm (B * eps / g)]
  exact mul_le_mul_of_nonneg_left (div_le_div₀ hB hs hg hgap)
    (div_nonneg (neg_nonneg.mpr hn.le) (sq_nonneg r))

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Restart the remainder integral at any earlier cone, with its exact
homogeneous factor. Paper `e1a0fd5`, `eq:remainder-dilution`, lines 808–812. -/
theorem radial_remainder_restart {u0 u v : ℝ}
    (hu0 : ui ≤ u0) (hu : u0 ≤ u) (hu1 : u < 0) (huv : u < v) (hv : v ≤ 0) :
    radialDatumRemainderIntegral ui S u v =
      (S.lam u0 v / S.lam u v) ^ 2 * radialDatumRemainderIntegral ui S u0 v +
        (∫ s in u0..u, S.lam s v ^ 2 * radialDatumSource S s v) / S.lam u v ^ 2 := by
  have hui := hu0.trans hu
  have hF := h.radialDatumSource_continuous_in hui le_rfl hu1 huv hv
  have hL := continuous_in h.regularCenter.continuous_lam
    (inSeg_subset_triangle le_rfl hu1 huv.le hv)
  have hi := ((hL.pow 2).mul hF).intervalIntegrable_of_Icc (μ := volume) hui
  have hi0 := hi.mono_set (show uIcc ui u0 ⊆ uIcc ui u by
    rw [uIcc_of_le hu0, uIcc_of_le hui]; exact Icc_subset_Icc le_rfl hu)
  have hi1 := hi.mono_set (show uIcc u0 u ⊆ uIcc ui u by
    rw [uIcc_of_le hu, uIcc_of_le hui]; exact Icc_subset_Icc hu0 le_rfl)
  have he := intervalIntegral.integral_add_adjacent_intervals hi0 hi1
  dsimp only [Pi.mul_apply, Pi.pow_apply] at he
  have hl0 := h.lam_pos (p := (u0, v))
    ⟨hu0, hu.trans_lt hu1, (hu.trans_lt huv).le, hv⟩
  have hl1 := h.lam_pos (p := (u, v)) ⟨hui, hu1, huv.le, hv⟩
  dsimp [radialDatumRemainderIntegral]
  rw [← he]
  field_simp [hl0.ne', hl1.ne']

/-- Radius growth along any incoming segment, from the uniform geometric
lower bound for -ν. Paper `e1a0fd5`, line 814. -/
theorem late_incoming_radius_growth {K u0 u v : ℝ}
    (hnu : ∀ p ∈ pastTriangle ui, K⁻¹ ≤ -S.nu p.1 p.2)
    (hu0 : ui ≤ u0) (hu : u0 ≤ u) (hu1 : u < 0) (huv : u < v) (hv : v ≤ 0) :
    S.r u v + K⁻¹ * (u - u0) ≤ S.r u0 v := by
  apply radius_lower_bound_of_incoming_transport hu
    (h.regularCenter.localBV.radius_in v u0 u hu
      (inSeg_subset_triangle hu0 hu1 huv.le hv)) rfl
  intro s hs
  exact hnu (s, v) ⟨hu0.trans hs.1, hs.2.trans_lt hu1,
    (hs.2.trans_lt huv).le, hv⟩

/-- Remainder dilution on a small-source incoming segment. The scalar and
interpolation constants B,D are supplied by the class theorems; λ and gap
bounds L,g come from Lemma 1.1. Paper `e1a0fd5`,
`eq:remainder-dilution`, lines 808–812. -/
theorem remainder_dilution_of_bounds {B D L g eps u0 u v : ℝ}
    (hB : 0 ≤ B) (_hD : 0 ≤ D) (hL : 0 < L) (hg : 0 < g) (heps : 0 ≤ eps)
    (hlower : ∀ p ∈ pastTriangle ui, L ≤ S.lam p.1 p.2)
    (hgap : ∀ p ∈ pastTriangle ui, g ≤ 1 - S.mu p.1 p.2)
    (hrem : |radialDatumRemainderIntegral ui S u0 v| ≤ D / S.r u0 v)
    (hs : ∀ s ∈ Icc u0 u,
      |outgoingAmplitude S s v * (outgoingAmplitude S s v ^ 2 - 3 * S.mu s v)| ≤ B * eps)
    (hu0 : ui ≤ u0) (hu : u0 ≤ u) (hu1 : u < 0) (huv : u < v) (hv : v ≤ 0) :
    |radialDatumRemainderIntegral ui S u v| ≤
      (D / L ^ 2) / S.r u0 v + (B / (g * L ^ 2)) * eps / S.r u v := by
  have hp : ∀ s ∈ Icc u0 u, (s, v) ∈ pastTriangle ui := fun s hs =>
    ⟨hu0.trans hs.1, hs.2.trans_lt hu1, (hs.2.trans_lt huv).le, hv⟩
  have hr0 := h.r_pos (hp u0 ⟨le_rfl, hu⟩) (hu.trans_lt huv)
  have hru := h.r_pos (hp u ⟨hu, le_rfl⟩) huv
  have hF := h.radialDatumSource_continuous_in hu hu0 hu1 huv hv
  have hGc : IntervalIntegrable (fun s => -S.nu s v / S.r s v ^ 2) volume u0 u :=
    (h.reciprocal_radius_primitive hu hu0 hu1 huv hv).1
  have hLc := continuous_in h.regularCenter.continuous_lam
    (inSeg_subset_triangle hu0 hu1 huv.le hv)
  have hnew : |(∫ s in u0..u, S.lam s v ^ 2 * radialDatumSource S s v) / S.lam u v ^ 2| ≤
      (B * eps / g / L ^ 2) * ∫ s in u0..u, -S.nu s v / S.r s v ^ 2 := by
    apply weighted_source_integral_bound hu (by positivity) hL
      (hlower (u, v) (hp u ⟨hu, le_rfl⟩))
      (fun s hs => ⟨(h.lam_pos (hp s hs)).le, (h.lam_bounds (hp s hs)).2⟩)
      (hF.intervalIntegrable_of_Icc (μ := volume) hu) hGc
      (by simpa only [uIcc_of_le hu] using hLc)
      (fun s hs => div_nonneg (neg_nonneg.mpr (h.nu_neg (hp s hs)).le) (sq_nonneg _))
    intro s hss
    exact datum_source_bound_of_cubic (h.r_pos (hp s hss) (hss.2.trans_lt huv))
      (h.nu_neg (hp s hss)) hg (hgap (s, v) (hp s hss)) (mul_nonneg hB heps) (hs s hss)
  have hrecip : (∫ s in u0..u, -S.nu s v / S.r s v ^ 2) ≤ 1 / S.r u v := by
    rw [← (h.reciprocal_radius_primitive hu hu0 hu1 huv hv).2]
    exact sub_le_self _ (one_div_nonneg.mpr hr0.le)
  have hnew' := hnew.trans (mul_le_mul_of_nonneg_left hrecip
    (show 0 ≤ B * eps / g / L ^ 2 by positivity))
  have hlam0 := h.lam_pos (hp u0 ⟨le_rfl, hu⟩)
  have hlamu := h.lam_pos (hp u ⟨hu, le_rfl⟩)
  have hratio : S.lam u0 v / S.lam u v ≤ 1 / L :=
    div_le_div₀ (by norm_num) (h.lam_bounds (hp u0 ⟨le_rfl, hu⟩)).2 hL
      (hlower (u, v) (hp u ⟨hu, le_rfl⟩))
  have hratio0 : 0 ≤ S.lam u0 v / S.lam u v := by positivity
  have hratiosq : (S.lam u0 v / S.lam u v) ^ 2 ≤ 1 / L ^ 2 := by
    calc
      _ ≤ (1 / L) ^ 2 := by gcongr
      _ = _ := by ring
  rw [h.radial_remainder_restart hu0 hu hu1 huv hv]
  calc
    _ ≤ |(S.lam u0 v / S.lam u v) ^ 2 * radialDatumRemainderIntegral ui S u0 v| +
        |(∫ s in u0..u, S.lam s v ^ 2 * radialDatumSource S s v) / S.lam u v ^ 2| :=
      abs_add_le _ _
    _ ≤ (1 / L ^ 2) * (D / S.r u0 v) + (B * eps / g / L ^ 2) * (1 / S.r u v) := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
      exact add_le_add (mul_le_mul hratiosq hrem (abs_nonneg _) (by positivity)) hnew'
    _ = _ := by ring

end StandingFull

end AcExtensionPrinciple

end
