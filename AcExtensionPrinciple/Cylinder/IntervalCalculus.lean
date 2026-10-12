module

public import AcExtensionPrinciple.Cylinder.CompactCurve

/-!
# Closed interval regularity from continuous differential coefficients

Calculus discharges for paper `e1a0fd5`, lines 731–737.
Ordinary derivatives are required only in the interval interior; endpoint
one-sided derivatives follow from continuous traces and continuous coefficients.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology NNReal

/-- Continuous interior differential data extend to relative derivatives at both endpoints.
Paper `e1a0fd5`, calculus input to lines 731–737. -/
theorem cylinder_interval_hasDerivWithinAt {f g : ℝ → ℝ} {a b x : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (g x) x) (hx : x ∈ Icc a b) :
    HasDerivWithinAt f (g x) (Icc a b) x := by
  have hdiff : DifferentiableOn ℝ f (Ioo a b) :=
    fun y hy => (hd y hy).differentiableAt.differentiableWithinAt
  rcases hx.1.eq_or_lt with he | hax
  · subst x
    have hq := hg a (left_mem_Icc.mpr hab.le)
    rw [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsGE hab] at hq
    have hlim := hq.mono_left (nhdsWithin_mono a Ioi_subset_Ici_self)
    have hlimD : Tendsto (deriv f) (𝓝[>] a) (𝓝 (g a)) := by
      apply hlim.congr'
      filter_upwards [Ioo_mem_nhdsGT hab] with y hy
      exact (hd y hy).deriv.symm
    exact (hasDerivWithinAt_Ici_of_tendsto_deriv hdiff
      ((hf a (left_mem_Icc.mpr hab.le)).mono Ioo_subset_Icc_self)
      (Ioo_mem_nhdsGT hab) hlimD).mono Icc_subset_Ici_self
  · rcases hx.2.eq_or_lt with he | hxb
    · subst x
      have hq := hg b (right_mem_Icc.mpr hab.le)
      rw [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsLE hab] at hq
      have hlim := hq.mono_left (nhdsWithin_mono b Iio_subset_Iic_self)
      have hlimD : Tendsto (deriv f) (𝓝[<] b) (𝓝 (g b)) := by
        apply hlim.congr'
        filter_upwards [Ioo_mem_nhdsLT hab] with y hy
        exact (hd y hy).deriv.symm
      exact (hasDerivWithinAt_Iic_of_tendsto_deriv hdiff
        ((hf b (right_mem_Icc.mpr hab.le)).mono Ioo_subset_Icc_self)
        (Ioo_mem_nhdsLT hab) hlimD).mono Icc_subset_Iic_self
    · exact (hd x ⟨hax, hxb⟩).hasDerivWithinAt

/-- Continuous differential coefficients give C¹ regularity on a closed interval.
Paper `e1a0fd5`, calculus input to lines 731–737. -/
theorem cylinder_interval_contDiffOn {f g : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (g x) x) : ContDiffOn ℝ 1 f (Icc a b) := by
  rw [contDiffOn_one_iff_derivWithin (uniqueDiffOn_Icc hab)]
  refine ⟨fun x hx => (cylinder_interval_hasDerivWithinAt hab hf hg hd hx).differentiableWithinAt,
    ?_⟩
  apply hg.congr
  intro x hx
  exact (cylinder_interval_hasDerivWithinAt hab hf hg hd hx).derivWithin
    ((uniqueDiffOn_Icc hab) x hx)

/-- Continuous interior differential data give a finite compact-interval Lipschitz constant.
Paper `e1a0fd5`, linear transport regularity used at lines 731–737. -/
theorem cylinder_interval_lipschitz {f g : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (g x) x) :
    ∃ K : ℝ≥0, LipschitzOnWith K f (Icc a b) :=
  (cylinder_interval_contDiffOn hab hf hg hd).exists_lipschitzOnWith
    (by decide) (convex_Icc _ _) isCompact_Icc

end AcExtensionPrinciple

end
