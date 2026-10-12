module

public import AcExtensionPrinciple.Observability.InnerChartCoefficientBounds
public import AcExtensionPrinciple.Observability.InnerChartCoordinates

/-!
# Inner-boundary logarithmic expansion representations

Paper `e1a0fd5`, `equations.tex` lines 1460–1473 and 1877–1907.
Outer boundary normalization fixes the integration constants.
-/

public section

namespace AcExtensionPrinciple.InnerCylinder

open Set Filter MeasureTheory
open scoped NNReal

variable {b T K a s₀ s₁ : ℝ} {S : SSFields} {h : NormalizedChartData b T K S}
variable (c : InnerCylinder h a s₀ s₁)

/-- Every inner boundary label has already entered the outer cylinder.
Paper `e1a0fd5`, lines 1692–1698 and 1877–1907. -/
theorem label_nonneg {s : ℝ} (hs : s ∈ Icc s₀ s₁) : 0 ≤ c.v s :=
  (PropA4.axis_label_nonneg h ⟨(c.source_mem hs).1.1, (c.source_mem hs).1.2.1⟩
    (c.late.trans hs.1)).trans (c.points s hs).1.le

/-- The pre-axis triangle with vertex on the inner cylinder stays in
r≥a and on entered rays. Paper `e1a0fd5`, lines 1877–1907 and 1522. -/
theorem triangle_annulus {s : ℝ} (hs : s ∈ Icc s₀ s₁) :
    chartTriangle (c.v s) s ⊆ h.innerAnnulus a := by
  have hp := c.source_mem hs
  have ht := c.label_nonneg hs
  have htri := h.volterra_triangle_subset ht hp
  intro q hq
  have hr := h.volterra_radius_order ht hp
    ⟨hq.1.trans hq.2.1, hq.2.2⟩ ⟨hq.1, hq.2.1⟩
  refine ⟨(htri hq).1, ?_, ht.trans hq.1⟩
  rw [← (c.points s hs).2.2]
  exact hr.1.trans hr.2

/-- The inner level curve is increasing. Paper `e1a0fd5`, the tangent
at lines 1887–1891. -/
theorem v_strictMono : StrictMonoOn c.v (Icc s₀ s₁) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) c.continuous_v
  intro s hs
  have hsI : s ∈ Ioo s₀ s₁ := by simpa only [interior_Icc] using hs
  rw [(c.tangent s hsI).deriv]
  exact div_pos (c.density_continuous_positive.2 s (Ioo_subset_Icc_self hsI))
    (h.signs _ _ (c.source_mem (Ioo_subset_Icc_self hsI)).1).1

/-- The regular inner level curve is Lipschitz on its compact interval.
Paper `e1a0fd5`, lines 1887–1891 and 1901. -/
theorem v_lipschitz : ∃ V : ℝ≥0, LipschitzOnWith V c.v (Icc s₀ s₁) := by
  rcases c.ordered.eq_or_lt with he | he
  · refine ⟨0, LipschitzOnWith.of_dist_le_mul ?_⟩
    intro x hx y hy
    have hxy : x = y := by rw [← he] at hx hy; linarith [hx.1, hx.2, hy.1, hy.2]
    simp [hxy]
  · have hl := h.continuous_lam.comp (continuousOn_id.prodMk c.continuous_v)
      (fun _ hs => (c.source_mem hs).1)
    exact cylinder_interval_lipschitz he c.continuous_v
      (c.density_continuous_positive.1.div hl
        (fun _ hs => (h.signs _ _ (c.source_mem hs).1).1.ne')) c.tangent

/-- The outgoing log(-ν) primitive has the regular reduced coefficient.
Paper `e1a0fd5`, `eq:logarithmic-expansions`, lines 1460–1473 and 1901. -/
theorem nu_log_primitive {s : ℝ} (hs : s ∈ Icc s₀ s₁) :
    IntervalPrimitive (fun t => Real.log (-S.nu s t)) (innerNuCoefficient S s) (c.v s) s := by
  have hvs := (c.points s hs).2.1.le
  have hseg : outSeg s (c.v s) s ⊆ chartInterior (chartCylinder h.g T) S :=
    (chartTriangle_out_subset le_rfl le_rfl le_rfl).trans
      ((c.triangle_annulus hs).trans (h.innerAnnulus_subset c.a_pos))
  have hsmall {t : ℝ} (ht : t ∈ Icc (c.v s) s) :
      outSeg s (c.v s) t ⊆ chartInterior (chartCylinder h.g T) S :=
    fun p hp => hseg ⟨hp.1, hp.2.1, hp.2.2.trans ht.2⟩
  have hn := intervalPrimitive_ac hvs
    (fun t ht => h.equations.nu_t s (c.v s) t ht.1 (hsmall ht))
  have hp : ∀ t ∈ uIcc (c.v s) s, 0 < -S.nu s t := by
    intro t ht
    rw [uIcc_of_le hvs] at ht
    exact neg_pos.mpr (h.signs _ _ (hseg ⟨by simp, ht⟩).1).2.1
  have hlog := positive_ac_log hn.neg hp
  apply ac_integral_eq_sub hvs hlog
  have hN := intervalPrimitive_ae_hasDerivAt hvs
    (fun t ht => h.equations.nu_t s (c.v s) t ht.1 (hsmall ht))
  filter_upwards [hN] with t ht htI
  have hmem := hseg (show (s, t) ∈ outSeg s (c.v s) s from
    ⟨by simp, htI.1.le, htI.2.le⟩)
  apply ((ht htI).neg.log (neg_pos.mpr (h.signs _ _ hmem.1).2.1).ne').congr_deriv
  rw [innerNuCoefficient, innerExpansionCoefficient_eq S hmem.2.ne' (h.gap_pos hmem.1).ne']
  unfold SSFields.radiusCoeff
  simp only [Pi.neg_apply]
  field_simp [(h.signs _ _ hmem.1).2.1.ne]

/-- The incoming log(λ) primitive has the regular reduced coefficient.
Paper `e1a0fd5`, `eq:logarithmic-expansions`, lines 1460–1473 and 1901. -/
theorem lam_log_primitive {s : ℝ} (hs : s ∈ Icc s₀ s₁) :
    IntervalPrimitive (fun x => Real.log (S.lam x (c.v s)))
      (fun x => innerLamCoefficient S x (c.v s)) (c.v s) s := by
  have hvs := (c.points s hs).2.1.le
  have hseg : inSeg (c.v s) (c.v s) s ⊆ chartInterior (chartCylinder h.g T) S :=
    (chartTriangle_in_subset le_rfl le_rfl le_rfl).trans
      ((c.triangle_annulus hs).trans (h.innerAnnulus_subset c.a_pos))
  have hsmall {x : ℝ} (hx : x ∈ Icc (c.v s) s) :
      inSeg (c.v s) (c.v s) x ⊆ chartInterior (chartCylinder h.g T) S :=
    fun p hp => hseg ⟨⟨hp.1.1, hp.1.2.trans hx.2⟩, hp.2⟩
  have hl := intervalPrimitive_ac hvs
    (fun x hx => h.equations.lam_s (c.v s) (c.v s) x hx.1 (hsmall hx))
  have hp : ∀ x ∈ uIcc (c.v s) s, 0 < S.lam x (c.v s) := by
    intro x hx
    rw [uIcc_of_le hvs] at hx
    exact (h.signs _ _ (hseg ⟨hx, by simp⟩).1).1
  have hlog := positive_ac_log hl hp
  apply ac_integral_eq_sub hvs hlog
  have hL := intervalPrimitive_ae_hasDerivAt hvs
    (fun x hx => h.equations.lam_s (c.v s) (c.v s) x hx.1 (hsmall hx))
  filter_upwards [hL] with x hx hxI
  have hmem := hseg (show (x, c.v s) ∈ inSeg (c.v s) (c.v s) s from
    ⟨⟨hxI.1.le, hxI.2.le⟩, by simp⟩)
  apply ((hx hxI).log (h.signs _ _ hmem.1).1.ne').congr_deriv
  rw [innerLamCoefficient, innerExpansionCoefficient_eq S hmem.2.ne' (h.gap_pos hmem.1).ne']
  unfold SSFields.radiusCoeff
  field_simp [(h.signs _ _ hmem.1).1.ne']

/-- Outer gauge normalization fixes the log(-ν) integration constant.
Paper `e1a0fd5`, `eq:observability-boundary-gauge`, lines 1460–1473 and 1901. -/
theorem nu_log_representation {s : ℝ} (hs : s ∈ Icc s₀ s₁) :
    Real.log (-S.nu s (c.v s)) = -(∫ t in c.v s..s, innerNuCoefficient S s t) := by
  have he := (c.nu_log_primitive hs).2
  dsimp only at he
  have hsI : s ∈ Icc 0 T := ⟨(c.source_mem hs).1.1, (c.source_mem hs).1.2.1⟩
  rw [(h.boundary_gauge s hsI).2.1] at he
  simp only [neg_neg, Real.log_one] at he
  linarith

/-- Outer entry normalization fixes the log(λ) integration constant.
Paper `e1a0fd5`, `eq:observability-boundary-gauge`, lines 1460–1473 and 1901. -/
theorem lam_log_representation {s : ℝ} (hs : s ∈ Icc s₀ s₁) :
    Real.log (S.lam s (c.v s)) = ∫ x in c.v s..s, innerLamCoefficient S x (c.v s) := by
  have he := (c.lam_log_primitive hs).2
  dsimp only at he
  have htI : c.v s ∈ Icc 0 T :=
    ⟨c.label_nonneg hs, (c.points s hs).2.1.le.trans ((c.source_mem hs).1.2.1)⟩
  rw [(h.boundary_gauge (c.v s) htI).2.2] at he
  simpa only [Real.log_one, sub_zero] using he

end AcExtensionPrinciple.InnerCylinder

end
