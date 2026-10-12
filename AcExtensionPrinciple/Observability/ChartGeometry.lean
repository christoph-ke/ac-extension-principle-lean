module

public import AcExtensionPrinciple.Observability.LemmaA2Volterra

/-!
# Geometric consequences in the normalized chart

Paper `e1a0fd5`, `equations.tex` lines 1451, 1460–1473, 1520.
These bounds are derived from characteristic equations and boundary normalization.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory

/-- A nonpositive characteristic integrand has nonpositive integral. Paper
`e1a0fd5`, `equations.tex` lines 1451 and 1520. -/
theorem chart_integral_nonpos {f : ℝ → ℝ} {a c : ℝ} (hac : a ≤ c)
    (hf : ∀ x ∈ Icc a c, f x ≤ 0) : (∫ x in a..c, f x) ≤ 0 := by
  have hh := intervalIntegral.integral_nonneg (μ := volume) hac
    (fun x hx => neg_nonneg.mpr (hf x hx))
  rw [intervalIntegral.integral_neg] at hh
  linarith

namespace NormalizedChartData

variable {b T K : ℝ} {S : SSFields} (h : NormalizedChartData b T K S)

include h

/-- The radius mixed coefficient is nonpositive. Paper `e1a0fd5`, `equations.tex` line 1451 (the
geometric bounds) and `eq:observability-chart-equations`. -/
theorem radiusCoeff_nonpos {s t : ℝ}
    (hq : (s, t) ∈ chartInterior (chartCylinder h.g T) S) : S.radiusCoeff s t ≤ 0 := by
  have hs := h.signs s t hq.1
  unfold SSFields.radiusCoeff
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hs.2.2 hs.1.le) hs.2.1.le)
    (mul_nonneg (h.gap_pos hq.1).le hq.2.le)

/-- The outgoing radius increases along an outgoing segment. Paper `e1a0fd5`,
`equations.tex` lines 1460–1473, 1520. -/
theorem radius_t_mono {s a c : ℝ} (hac : a ≤ c)
    (hseg : outSeg s a c ⊆ chartCylinder h.g T) : S.r s a ≤ S.r s c := by
  have hi := (h.equations.radius_t s a c hac hseg).2
  have hp : 0 ≤ ∫ z in a..c, S.lam s z := by
    apply intervalIntegral.integral_nonneg hac
    intro z hz
    exact (h.signs s z (hseg (show (s, z) ∈ outSeg s a c from ⟨by simp, hz⟩))).1.le
  linarith

/-- The radius decreases along an incoming segment. Paper `e1a0fd5`,
`equations.tex` lines 1460–1473, 1520. -/
theorem radius_s_antitone {t a c : ℝ} (hac : a ≤ c)
    (hseg : inSeg t a c ⊆ chartCylinder h.g T) : S.r c t ≤ S.r a t := by
  have hi := (h.equations.radius_s t a c hac hseg).2
  have hp : (∫ σ in a..c, S.nu σ t) ≤ 0 := by
    apply chart_integral_nonpos hac
    intro σ hσ
    exact (h.signs σ t (hseg (show (σ, t) ∈ inSeg t a c from ⟨hσ, by simp⟩))).2.1.le
  linarith

/-- Every integration point is at least as far from the axis as the left side
of Volterra's formula. Paper `e1a0fd5`, `equations.tex` line 1520. -/
theorem volterra_radius_order {s t σ z : ℝ} (ht : 0 ≤ t)
    (hq : (s, t) ∈ chartInterior (chartCylinder h.g T) S)
    (hσ : σ ∈ Icc t s) (hz : z ∈ Icc t σ) :
    S.r s t ≤ S.r σ t ∧ S.r σ t ≤ S.r σ z := by
  have htri := h.volterra_triangle_subset ht hq
  exact ⟨h.radius_s_antitone hσ.2
    (fun q hq => (htri (chartTriangle_in_subset le_rfl hσ.1 le_rfl hq)).1),
    h.radius_t_mono hz.1
      (fun q hq => (htri (chartTriangle_out_subset le_rfl hz.2 hσ.2 hq)).1)⟩

/-- A compact pre-axis triangle lies in `r ≥ η > 0`, with the explicit choice
`η = r(c,a)`. Paper `e1a0fd5`, cutoff argument at lines 1524–1530. -/
theorem triangle_radius_floor {a c : ℝ} (ha : 0 ≤ a) (hac : a ≤ c)
    (hc : c ≤ T) (hg : h.g c < a) :
    ∃ η, 0 < η ∧ ∀ q ∈ chartTriangle a c, η ≤ S.r q.1 q.2 := by
  have htri := h.triangle_subset ha hac hc hg
  have hpoint := htri (show (c, a) ∈ chartTriangle a c from ⟨le_rfl, hac, le_rfl⟩)
  refine ⟨S.r c a, hpoint.2, ?_⟩
  intro q hq
  have hh := h.volterra_radius_order ha hpoint ⟨hq.1.trans hq.2.1, hq.2.2⟩
    ⟨hq.1, hq.2.1⟩
  exact hh.1.trans hh.2

/-- The incoming expansion has magnitude at most one. Paper `e1a0fd5`, `equations.tex` line 1451
(the geometric bounds), `eq:observability-boundary-gauge`. -/
theorem neg_nu_le_one {s t : ℝ}
    (hq : (s, t) ∈ chartInterior (chartCylinder h.g T) S) : -S.nu s t ≤ 1 := by
  have hs : s ∈ Icc 0 T := ⟨hq.1.1, hq.1.2.1⟩
  have hgt : h.g s < t := by
    rcases hq.1.2.2.1.eq_or_lt with he | he
    · have hz := (h.axis_values s hs).1
      rw [he] at hz
      linarith [hq.2]
    · exact he
  have hseg : outSeg s t s ⊆ chartInterior (chartCylinder h.g T) S := by
    intro q hq'
    have hmem := h.out_subset hs hgt.le le_rfl hq'
    refine ⟨hmem, ?_⟩
    have hx : q.1 = s := by simpa using hq'.1
    have hy : t ≤ q.2 := hq'.2.1
    apply h.radius_pos hmem
    simpa [hx] using hgt.trans_le hy
  have hi := (h.equations.nu_t s t s hq.1.2.2.2 hseg).2
  have hp : (∫ z in t..s, S.radiusCoeff s z) ≤ 0 := by
    apply chart_integral_nonpos hq.1.2.2.2
    intro z hz
    exact h.radiusCoeff_nonpos (hseg (show (s, z) ∈ outSeg s t s from ⟨by simp, hz⟩))
  rw [(h.boundary_gauge s hs).2.1] at hi
  linarith

/-- The outgoing expansion lies between `1/K` and one on incoming rays entering during the interval.
Paper `e1a0fd5`, line 1451 (the geometric bounds), lines 1460–1473. -/
theorem lam_bounds {s t : ℝ} (ht : 0 ≤ t)
    (hq : (s, t) ∈ chartInterior (chartCylinder h.g T) S) :
    K⁻¹ ≤ S.lam s t ∧ S.lam s t ≤ 1 := by
  have htri := h.volterra_triangle_subset ht hq
  have hts := hq.1.2.2.2
  have htI : t ∈ Icc 0 T := ⟨ht, hts.trans hq.1.2.1⟩
  have hK : 0 < K := by linarith [h.K_ge_one]
  have hl : 0 < S.lam s t := (h.signs s t hq.1).1
  have hratio := h.incoming_ratio s t ht hts hq.1.2.1 hq.1
  rw [(h.boundary_gauge t htI).2.2] at hratio
  have hlow : K⁻¹ ≤ S.lam s t := by
    rw [← one_div, div_le_iff₀ hK]
    have hh := (div_le_iff₀ hl).mp hratio
    simpa [mul_comm] using hh
  have hi := (h.equations.lam_s t t s hts
    ((chartTriangle_in_subset le_rfl le_rfl le_rfl).trans htri)).2
  have hp : (∫ σ in t..s, S.radiusCoeff σ t) ≤ 0 := by
    apply chart_integral_nonpos hts
    intro σ hσ
    exact h.radiusCoeff_nonpos (htri ⟨le_rfl, hσ.1, hσ.2⟩)
  change S.lam s t - S.lam t t = ∫ σ in t..s, S.radiusCoeff σ t at hi
  rw [(h.boundary_gauge t htI).2.2] at hi
  exact ⟨hlow, by linarith⟩

end NormalizedChartData

end AcExtensionPrinciple

end
