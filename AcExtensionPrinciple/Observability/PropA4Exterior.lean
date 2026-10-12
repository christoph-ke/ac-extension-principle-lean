module

public import AcExtensionPrinciple.Observability.PropA4Mass
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Exterior geometry with an enclosed-mass bound

Paper `e1a0fd5`, `eq:observability-exterior-geometry`, lines 1713–1728.
Comparison with `1-2P/r` avoids differentiating the mass bound P or
introducing logarithmic integrals as extra hypotheses.
-/

public section

namespace AcExtensionPrinciple
namespace PropA4

open Set MeasureTheory

/-- Exact derivative of the expansion divided by the comparison gap.
Paper `e1a0fd5`, lines 1722–1728. -/
theorem expansion_ratio_hasDerivAt {f r : ℝ → ℝ} {m v P x : ℝ}
    (hr : r x ≠ 0) (hm : r x - 2 * m ≠ 0) (hP : r x - 2 * P ≠ 0)
    (hR : HasDerivAt r v x)
    (hF : HasDerivAt f (2 * m * v * f x / (r x * (r x - 2 * m))) x) :
    HasDerivAt (fun y => f y * r y / (r y - 2 * P))
      (2 * f x * v * r x * (m - P) / ((r x - 2 * m) * (r x - 2 * P) ^ 2)) x := by
  apply ((hF.mul hR).div (hR.sub_const (2 * P)) hP).congr_deriv
  simp only [Pi.mul_apply]
  field_simp
  ring

/-- Outward comparison of an expansion with `1-2P/r`. All differential
premises come from the radius and expansion primitives. Paper `e1a0fd5`,
lines 1722–1728. -/
theorem expansion_ratio_antitone {f r m v : ℝ → ℝ} {a c P : ℝ}
    (hP : 0 ≤ P) (hf : ContinuousOn f (Icc a c)) (hr : ContinuousOn r (Icc a c))
    (hbound : ∀ x ∈ Icc a c, m x ≤ P ∧ 2 * P < r x ∧ 0 ≤ f x)
    (hv : ∀ x ∈ Ioo a c, 0 ≤ v x)
    (hR : ∀ x ∈ Ioo a c, HasDerivAt r (v x) x)
    (hF : ∀ x ∈ Ioo a c,
      HasDerivAt f (2 * m x * v x * f x / (r x * (r x - 2 * m x))) x) :
    AntitoneOn (fun x => f x * r x / (r x - 2 * P)) (Icc a c) := by
  have hcut (x : ℝ) (hx : x ∈ Icc a c) : 0 < r x - 2 * P := by
    linarith [(hbound x hx).2.1]
  have hd (x : ℝ) (hx : x ∈ Ioo a c) :=
    expansion_ratio_hasDerivAt
      (show r x ≠ 0 by linarith [(hbound x ⟨hx.1.le, hx.2.le⟩).2.1])
      (show r x - 2 * m x ≠ 0 by
        linarith [(hbound x ⟨hx.1.le, hx.2.le⟩).1, (hbound x ⟨hx.1.le, hx.2.le⟩).2.1])
      (hcut x ⟨hx.1.le, hx.2.le⟩).ne' (hR x hx) (hF x hx)
  apply antitoneOn_of_deriv_nonpos (convex_Icc a c)
    ((hf.mul hr).div (hr.sub continuousOn_const) (fun x hx => (hcut x hx).ne'))
  · intro x hx
    rw [interior_Icc] at hx
    exact (hd x hx).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    change deriv (fun y => f y * r y / (r y - 2 * P)) x ≤ 0
    rw [(hd x hx).deriv]
    have hh := hbound x ⟨hx.1.le, hx.2.le⟩
    apply div_nonpos_of_nonpos_of_nonneg
    · exact mul_nonpos_of_nonneg_of_nonpos (by
        have hr0 : 0 ≤ r x := by linarith
        have hf0 := hh.2.2
        have hv0 := hv x hx
        positivity) (by linarith)
    · have hm0 : 0 ≤ r x - 2 * m x := by linarith
      positivity

/-- Inward comparison along an incoming ray. Paper `e1a0fd5`,
lines 1722–1728; the radius derivative is now nonpositive. -/
theorem expansion_ratio_monotone {f r m v : ℝ → ℝ} {a c P : ℝ}
    (hP : 0 ≤ P) (hf : ContinuousOn f (Icc a c)) (hr : ContinuousOn r (Icc a c))
    (hbound : ∀ x ∈ Icc a c, m x ≤ P ∧ 2 * P < r x ∧ 0 ≤ f x)
    (hv : ∀ x ∈ Ioo a c, v x ≤ 0)
    (hR : ∀ x ∈ Ioo a c, HasDerivAt r (v x) x)
    (hF : ∀ x ∈ Ioo a c,
      HasDerivAt f (2 * m x * v x * f x / (r x * (r x - 2 * m x))) x) :
    MonotoneOn (fun x => f x * r x / (r x - 2 * P)) (Icc a c) := by
  have hcut (x : ℝ) (hx : x ∈ Icc a c) : 0 < r x - 2 * P := by
    linarith [(hbound x hx).2.1]
  have hd (x : ℝ) (hx : x ∈ Ioo a c) :=
    expansion_ratio_hasDerivAt
      (show r x ≠ 0 by linarith [(hbound x ⟨hx.1.le, hx.2.le⟩).2.1])
      (show r x - 2 * m x ≠ 0 by
        linarith [(hbound x ⟨hx.1.le, hx.2.le⟩).1, (hbound x ⟨hx.1.le, hx.2.le⟩).2.1])
      (hcut x ⟨hx.1.le, hx.2.le⟩).ne' (hR x hx) (hF x hx)
  apply monotoneOn_of_deriv_nonneg (convex_Icc a c)
    ((hf.mul hr).div (hr.sub continuousOn_const) (fun x hx => (hcut x hx).ne'))
  · intro x hx
    rw [interior_Icc] at hx
    exact (hd x hx).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    change 0 ≤ deriv (fun y => f y * r y / (r y - 2 * P)) x
    rw [(hd x hx).deriv]
    have hh := hbound x ⟨hx.1.le, hx.2.le⟩
    apply div_nonneg
    · have hleft : 2 * f x * v x * r x ≤ 0 := by
        have hr0 : 0 ≤ r x := by linarith
        have hf0 := hh.2.2
        exact mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos (by positivity) (hv x hx)) hr0
      exact mul_nonneg_of_nonpos_of_nonpos hleft (by linarith)
    · have hm0 : 0 ≤ r x - 2 * m x := by linarith
      positivity

/-- Continuity of the radius mixed coefficient follows from the chart
geometry on positive-radius segments. Paper `e1a0fd5`, lines 1722–1728. -/
theorem continuous_radiusCoeff_on {b T K : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) {D : Set (ℝ × ℝ)}
    (hD : D ⊆ chartInterior (chartCylinder h.g T) S) :
    ContinuousOn (fun q => S.radiusCoeff q.1 q.2) D := by
  have hr := h.continuous_r.mono (fun q hq => (hD hq).1)
  have hm := h.continuous_m.mono (fun q hq => (hD hq).1)
  have hl := h.continuous_lam.mono (fun q hq => (hD hq).1)
  have hn := h.continuous_nu.mono (fun q hq => (hD hq).1)
  have hμ : ContinuousOn (fun q => S.mu q.1 q.2) D :=
    (continuousOn_const.mul hm).div hr (fun q hq => (hD hq).2.ne')
  exact ((hμ.mul hl).mul hn).div ((continuousOn_const.sub hμ).mul hr)
    (fun q hq => mul_ne_zero (h.gap_pos (hD hq).1).ne' (hD hq).2.ne')

/-- Off-axis algebra of the mixed radius coefficient. Paper `e1a0fd5`,
lines 1722–1728 and `eq:observability-chart-equations`. -/
theorem radiusCoeff_eq_mass {S : SSFields} {s t : ℝ} (hr : S.r s t ≠ 0) :
    S.radiusCoeff s t =
      2 * S.m s t * S.lam s t * S.nu s t / (S.r s t * (S.r s t - 2 * S.m s t)) := by
  unfold SSFields.radiusCoeff SSFields.mu massRatio
  field_simp

/-- The incoming expansion is bounded below by the comparison gap on an
exterior outgoing segment. The mass-bound premise is discharged by
`total_mass_bound` in the small-observation argument. Paper `e1a0fd5`,
`eq:observability-exterior-geometry`, lines 1722–1728. -/
theorem exterior_neg_nu_lower {b T K P s t : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 ≤ P)
    (hq : (s, t) ∈ chartInterior (chartCylinder h.g T) S)
    (hcut : 2 * P < S.r s t)
    (hmass : ∀ z ∈ Icc t s, S.m s z ≤ P) :
    1 - 2 * P / S.r s t ≤ -S.nu s t := by
  have hs : s ∈ Icc 0 T := ⟨hq.1.1, hq.1.2.1⟩
  have hts := hq.1.2.2.2
  have hseg : outSeg s t s ⊆ chartInterior (chartCylinder h.g T) S := by
    rintro ⟨x, z⟩ hmem
    have hx : x = s := by simpa using hmem.1
    subst x
    have hh := h.out_subset hs hq.1.2.2.1 le_rfl hmem
    refine ⟨hh, hq.2.trans_le (h.radius_t_mono hmem.2.1
      (h.out_subset hs hq.1.2.2.1 (hmem.2.2.trans le_rfl)))⟩
  have hcontR : ContinuousOn (S.r s) (Icc t s) := h.continuous_r.comp
    (continuous_const.prodMk continuous_id).continuousOn (fun z hz => (hseg ⟨by simp, hz⟩).1)
  have hcontN : ContinuousOn (fun z => -S.nu s z) (Icc t s) :=
    (h.continuous_nu.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun z hz => (hseg ⟨by simp, hz⟩).1)).neg
  have hcontC : ContinuousOn (S.radiusCoeff s) (Icc t s) :=
    (continuous_radiusCoeff_on h hseg).comp
      (continuous_const.prodMk continuous_id).continuousOn (fun z hz => ⟨by simp, hz⟩)
  have hcontL : ContinuousOn (S.lam s) (Icc t s) := h.continuous_lam.comp
    (continuous_const.prodMk continuous_id).continuousOn (fun z hz => (hseg ⟨by simp, hz⟩).1)
  have hbound (z : ℝ) (hz : z ∈ Icc t s) :
      S.m s z ≤ P ∧ 2 * P < S.r s z ∧ 0 ≤ -S.nu s z := by
    have hmem := hseg (show (s, z) ∈ outSeg s t s from ⟨by simp, hz⟩)
    refine ⟨hmass z hz, hcut.trans_le ?_, (neg_pos.mpr (h.signs s z hmem.1).2.1).le⟩
    exact h.radius_t_mono hz.1 (h.out_subset hs hq.1.2.2.1 hz.2)
  have hR (z : ℝ) (hz : z ∈ Ioo t s) : HasDerivAt (S.r s) (S.lam s z) z :=
    intervalPrimitive_hasDerivAt hz hcontL (fun y hy =>
      h.equations.radius_t s t y hy.1 (h.out_subset hs hq.1.2.2.1 hy.2))
  have hN (z : ℝ) (hz : z ∈ Ioo t s) : HasDerivAt (fun z => -S.nu s z)
      (2 * S.m s z * S.lam s z * (-S.nu s z) /
        (S.r s z * (S.r s z - 2 * S.m s z))) z := by
    have hd := (intervalPrimitive_hasDerivAt hz hcontC (fun y hy =>
      h.equations.nu_t s t y hy.1 (fun q hq' => hseg ⟨hq'.1, hq'.2.1, hq'.2.2.trans hy.2⟩))).neg
    apply hd.congr_deriv
    rw [radiusCoeff_eq_mass (s := s) (t := z)
      (hseg (show (s, z) ∈ outSeg s t s from ⟨by simp, hz.1.le, hz.2.le⟩)).2.ne']
    ring
  have hmono := expansion_ratio_antitone hP hcontN hcontR hbound
    (fun z hz => (h.signs s z (hseg ⟨by simp, hz.1.le, hz.2.le⟩).1).1.le) hR hN
  have hcomp := hmono ⟨le_rfl, hts⟩ ⟨hts, le_rfl⟩ hts
  change -S.nu s s * S.r s s / (S.r s s - 2 * P) ≤
    -S.nu s t * S.r s t / (S.r s t - 2 * P) at hcomp
  rw [(h.boundary_gauge s hs).2.1] at hcomp
  simp only [neg_neg, one_mul] at hcomp
  have hbcut := (hbound s ⟨hts, le_rfl⟩).2.1
  have hright : 1 ≤ -S.nu s t * S.r s t / (S.r s t - 2 * P) := by
    have hb : 1 ≤ S.r s s / (S.r s s - 2 * P) := by
      rw [le_div_iff₀ (show 0 < S.r s s - 2 * P by linarith)]
      linarith
    exact hb.trans hcomp
  have hh := (le_div_iff₀ (show 0 < S.r s t - 2 * P by linarith)).mp hright
  have heq : 1 - 2 * P / S.r s t = (S.r s t - 2 * P) / S.r s t := by
    field_simp [hq.2.ne']
  rw [heq, div_le_iff₀ hq.2]
  nlinarith

/-- The outgoing expansion is bounded below by the same comparison gap
on entered incoming rays. Its mass-bound premise is discharged by
`total_mass_bound`. Paper `e1a0fd5`, `eq:observability-exterior-geometry`,
lines 1722–1728. -/
theorem exterior_lam_lower {b T K P s t : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 ≤ P) (ht : 0 ≤ t)
    (hq : (s, t) ∈ chartInterior (chartCylinder h.g T) S)
    (hcut : 2 * P < S.r s t)
    (hmass : ∀ σ ∈ Icc t s, S.m σ t ≤ P) :
    1 - 2 * P / S.r s t ≤ S.lam s t := by
  have hts := hq.1.2.2.2
  have htI : t ∈ Icc 0 T := ⟨ht, hts.trans hq.1.2.1⟩
  have htri := h.volterra_triangle_subset ht hq
  have hseg : inSeg t t s ⊆ chartInterior (chartCylinder h.g T) S :=
    (chartTriangle_in_subset le_rfl le_rfl le_rfl).trans htri
  have hcontR : ContinuousOn (fun σ => S.r σ t) (Icc t s) := h.continuous_r.comp
    (continuous_id.prodMk continuous_const).continuousOn (fun σ hσ => (hseg ⟨hσ, by simp⟩).1)
  have hcontL : ContinuousOn (fun σ => S.lam σ t) (Icc t s) := h.continuous_lam.comp
    (continuous_id.prodMk continuous_const).continuousOn (fun σ hσ => (hseg ⟨hσ, by simp⟩).1)
  have hcontC : ContinuousOn (fun σ => S.radiusCoeff σ t) (Icc t s) :=
    (continuous_radiusCoeff_on h hseg).comp
      (continuous_id.prodMk continuous_const).continuousOn (fun σ hσ => ⟨hσ, by simp⟩)
  have hcontN : ContinuousOn (fun σ => S.nu σ t) (Icc t s) := h.continuous_nu.comp
    (continuous_id.prodMk continuous_const).continuousOn (fun σ hσ => (hseg ⟨hσ, by simp⟩).1)
  have hbound (σ : ℝ) (hσ : σ ∈ Icc t s) :
      S.m σ t ≤ P ∧ 2 * P < S.r σ t ∧ 0 ≤ S.lam σ t := by
    have hmem := hseg (show (σ, t) ∈ inSeg t t s from ⟨hσ, by simp⟩)
    exact ⟨hmass σ hσ, hcut.trans_le (h.volterra_radius_order ht hq hσ ⟨le_rfl, hσ.1⟩).1,
      (h.signs σ t hmem.1).1.le⟩
  have hR (σ : ℝ) (hσ : σ ∈ Ioo t s) :
      HasDerivAt (fun σ => S.r σ t) (S.nu σ t) σ :=
    intervalPrimitive_hasDerivAt hσ hcontN (fun y hy =>
      h.equations.radius_s t t y hy.1
        (fun q hq' => (hseg ⟨⟨hq'.1.1, hq'.1.2.trans hy.2⟩, hq'.2⟩).1))
  have hL (σ : ℝ) (hσ : σ ∈ Ioo t s) : HasDerivAt (fun σ => S.lam σ t)
      (2 * S.m σ t * S.nu σ t * S.lam σ t /
        (S.r σ t * (S.r σ t - 2 * S.m σ t))) σ := by
    have hd := intervalPrimitive_hasDerivAt hσ hcontC (fun y hy =>
      h.equations.lam_s t t y hy.1
        (fun q hq' => hseg ⟨⟨hq'.1.1, hq'.1.2.trans hy.2⟩, hq'.2⟩))
    apply hd.congr_deriv
    rw [radiusCoeff_eq_mass (s := σ) (t := t)
      (hseg (show (σ, t) ∈ inSeg t t s from ⟨⟨hσ.1.le, hσ.2.le⟩, by simp⟩)).2.ne']
    ring
  have hmono := expansion_ratio_monotone hP hcontL hcontR hbound
    (fun σ hσ => (h.signs σ t
      (hseg (show (σ, t) ∈ inSeg t t s from ⟨⟨hσ.1.le, hσ.2.le⟩, by simp⟩)).1).2.1.le) hR hL
  have hcomp := hmono ⟨le_rfl, hts⟩ ⟨hts, le_rfl⟩ hts
  change S.lam t t * S.r t t / (S.r t t - 2 * P) ≤
    S.lam s t * S.r s t / (S.r s t - 2 * P) at hcomp
  rw [(h.boundary_gauge t htI).2.2] at hcomp
  simp only [one_mul] at hcomp
  have hbcut := (hbound t ⟨le_rfl, hts⟩).2.1
  have hright : 1 ≤ S.lam s t * S.r s t / (S.r s t - 2 * P) := by
    have hb : 1 ≤ S.r t t / (S.r t t - 2 * P) := by
      rw [le_div_iff₀ (show 0 < S.r t t - 2 * P by linarith)]
      linarith
    exact hb.trans hcomp
  have hh := (le_div_iff₀ (show 0 < S.r s t - 2 * P by linarith)).mp hright
  have heq : 1 - 2 * P / S.r s t = (S.r s t - 2 * P) / S.r s t := by
    field_simp [hq.2.ne']
  rw [heq, div_le_iff₀ hq.2]
  nlinarith

/-- All three exterior geometric bounds follow from the enclosed-mass
bound, with no new geometric assumptions. In A.4, `P = (K+2)M` comes
from `total_mass_bound`. Paper `e1a0fd5`,
`eq:observability-exterior-geometry`, lines 1713–1728. -/
theorem exterior_geometry_of_mass_bound {b T K P s t : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P) (ht : 0 ≤ t)
    (hq : (s, t) ∈ chartInterior (chartCylinder h.g T) S)
    (hcut : 32 * P ≤ S.r s t)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P) :
    (1 / 2 ≤ 1 - S.mu s t ∧ 1 - S.mu s t ≤ 1) ∧
      (1 / 2 ≤ -S.nu s t ∧ -S.nu s t ≤ 1) ∧
      (1 / 2 ≤ S.lam s t ∧ S.lam s t ≤ 1) := by
  have h2P : 2 * P < S.r s t := by linarith
  have hsmall : 2 * P / S.r s t ≤ 1 / 16 := by
    rw [div_le_iff₀ hq.2]
    linarith
  have hμ : S.mu s t ≤ 1 / 16 := by
    change 2 * S.m s t / S.r s t ≤ 1 / 16
    exact (div_le_div_of_nonneg_right (by linarith [hmass s t hq.1]) hq.2.le).trans hsmall
  have htri := h.volterra_triangle_subset ht hq
  have hν := exterior_neg_nu_lower h hP.le hq h2P (fun z hz => hmass s z
    (htri (show (s, z) ∈ chartTriangle t s from ⟨hz.1, hz.2, le_rfl⟩)).1)
  have hlam := exterior_lam_lower h hP.le ht hq h2P (fun σ hσ => hmass σ t
    (htri (show (σ, t) ∈ chartTriangle t s from ⟨le_rfl, hσ.1, hσ.2⟩)).1)
  exact ⟨⟨by linarith, by linarith [(h.signs s t hq.1).2.2]⟩,
    ⟨by linarith, h.neg_nu_le_one hq⟩, ⟨by linarith, (h.lam_bounds ht hq).2⟩⟩

/-- The potential bound in the outgoing characteristic measure; multiplying
by `dz` gives `P dz ≤ 4M*/r³ dr`. Paper `e1a0fd5`, lines 1734–1738. -/
theorem potential_le_radial_density {b T K P s t : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P) (ht : 0 ≤ t)
    (hq : (s, t) ∈ chartInterior (chartCylinder h.g T) S)
    (hcut : 32 * P ≤ S.r s t)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P) :
    chartPotential S s t ≤ 4 * P * S.lam s t / S.r s t ^ 3 := by
  have hgeo := exterior_geometry_of_mass_bound h hP ht hq hcut hmass
  have hgap := h.gap_pos hq.1
  have hl := (h.signs s t hq.1).1
  have hm0 : 0 ≤ S.m s t := by
    have hh := (h.signs s t hq.1).2.2
    change 0 ≤ 2 * S.m s t / S.r s t at hh
    have hh' := (le_div_iff₀ hq.2).mp hh
    linarith
  have hnum : S.m s t * (-S.nu s t) ≤ 2 * P * (1 - S.mu s t) := by
    have hh := mul_le_mul_of_nonneg_left hgeo.2.1.2 hm0
    nlinarith [hmass s t hq.1, hgeo.1.1]
  have heq : chartPotential S s t =
      2 * S.m s t * (-S.nu s t) * S.lam s t / ((1 - S.mu s t) * S.r s t ^ 3) := by
    unfold chartPotential SSFields.mu massRatio
    field_simp
  rw [heq, div_le_iff₀ (mul_pos hgap (pow_pos hq.2 3))]
  have heq' : (4 * P * S.lam s t / S.r s t ^ 3) *
      ((1 - S.mu s t) * S.r s t ^ 3) = 4 * P * S.lam s t * (1 - S.mu s t) := by
    field_simp [hq.2.ne']
  rw [heq']
  have hh := mul_le_mul_of_nonneg_right hnum (show 0 ≤ 2 * S.lam s t by positivity)
  nlinarith

/-- Incoming travel in the exterior gives the affine radius lower bound
used in the power and oscillation kernels. Paper `e1a0fd5`, lines 1734–1738. -/
theorem incoming_radius_separation {b T K P s t σ : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P) (ht : 0 ≤ t)
    (hq : (s, t) ∈ chartInterior (chartCylinder h.g T) S)
    (hcut : 32 * P ≤ S.r s t)
    (hmass : ∀ x z, (x, z) ∈ chartCylinder h.g T → S.m x z ≤ P)
    (hσ : σ ∈ Icc t s) : S.r s t + (s - σ) / 2 ≤ S.r σ t := by
  have htri := h.volterra_triangle_subset ht hq
  have hseg : inSeg t σ s ⊆ chartInterior (chartCylinder h.g T) S :=
    (chartTriangle_in_subset le_rfl hσ.1 le_rfl).trans htri
  have hi := h.equations.radius_s t σ s hσ.2 (fun q hq' => (hseg hq').1)
  have hcomp := intervalIntegral.integral_mono_on hσ.2 hi.1
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (-1 / 2 : ℝ)) volume σ s)
    (fun x hx => by
      have hmem := hseg (show (x, t) ∈ inSeg t σ s from ⟨hx, by simp⟩)
      have hr := (h.volterra_radius_order ht hq ⟨hσ.1.trans hx.1, hx.2⟩
        ⟨le_rfl, hσ.1.trans hx.1⟩).1
      have hgeo := exterior_geometry_of_mass_bound h hP ht hmem (hcut.trans hr) hmass
      linarith [hgeo.2.1.1])
  rw [intervalIntegral.integral_const] at hcomp
  simp only [smul_eq_mul] at hcomp
  linarith [hi.2]

end PropA4
end AcExtensionPrinciple

end
