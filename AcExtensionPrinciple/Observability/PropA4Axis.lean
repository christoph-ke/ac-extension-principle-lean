module

public import AcExtensionPrinciple.Observability.PropA4Amplitude

/-!
# Quantitative regularity of the late axis label

Paper `e1a0fd5`, `eq:observability-axis-label-bounds`, lines 1692–1698.
The axis estimates follow from the characteristic radius primitives and
continuity of the expansions, including at the axis.
-/

public section

namespace AcExtensionPrinciple
namespace PropA4

open Set Filter MeasureTheory
open scoped Topology

/-- The incoming expansion bound extends to the axis by continuity.
Paper `e1a0fd5`, lines 1694–1698. -/
theorem neg_nu_le_one_closed {b T K s t : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hq : (s, t) ∈ chartCylinder h.g T) :
    -S.nu s t ≤ 1 := by
  have hs : s ∈ Icc 0 T := ⟨hq.1, hq.2.1⟩
  have hc : ContinuousOn (fun z => -S.nu s z) (Icc (h.g s) s) :=
    (h.continuous_nu.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun z hz => h.out_subset hs le_rfl le_rfl
        (show (s, z) ∈ outSeg s (h.g s) s from ⟨by simp, hz⟩))).neg
  have ht : t ∈ closure (Ioc (h.g s) s) := by
    rw [closure_Ioc (h.axis_before_boundary s hs).ne]
    exact hq.2.2
  apply ContinuousWithinAt.closure_le ht
    ((hc t hq.2.2).mono Ioc_subset_Icc_self) continuousWithinAt_const
  intro z hz
  have hmem : (s, z) ∈ chartCylinder h.g T := ⟨hs.1, hs.2, hz.1.le, hz.2⟩
  exact h.neg_nu_le_one ⟨hmem, h.radius_pos hmem hz.1⟩

/-- The entry comparison also bounds the axis expansion from below.
Paper `e1a0fd5`, lines 1694–1698. -/
theorem lam_lower_closed {b T K s t : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (ht : 0 ≤ t)
    (hq : (s, t) ∈ chartCylinder h.g T) : K⁻¹ ≤ S.lam s t := by
  have hK : 0 < K := by linarith [h.K_ge_one]
  have hl := (h.signs s t hq).1
  have he := h.incoming_ratio s t ht hq.2.2.2 hq.2.1 hq
  rw [(h.boundary_gauge t ⟨ht, hq.2.2.2.trans hq.2.1⟩).2.2] at he
  have hh := (div_le_iff₀ hl).mp he
  rw [inv_eq_one_div, div_le_iff₀ hK]
  simpa only [mul_comm] using hh

/-- On nearby late slices the axis increment is at most `K` times
the time increment. The overlap premise is local and follows from
`g(s) < s` and continuity. Paper `e1a0fd5`, lines 1694–1698. -/
theorem axis_increment_le_of_overlap {b T K x y : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hx : x ∈ Icc (K * b) T)
    (hy : y ∈ Icc (K * b) T) (hxy : x ≤ y) (hover : h.g y ≤ x) :
    h.g y - h.g x ≤ K * (y - x) := by
  have hKb : 0 ≤ K * b := mul_nonneg (by linarith [h.K_ge_one]) h.b_pos.le
  have hxI : x ∈ Icc 0 T := ⟨hKb.trans hx.1, hx.2⟩
  have hyI : y ∈ Icc 0 T := ⟨hKb.trans hy.1, hy.2⟩
  have hgxy := h.monotone_g hxI hyI hxy
  have hg0 := axis_label_nonneg h hxI hx.1
  have hseg := h.in_subset (t := h.g y) hxI.1 hy.2 hover le_rfl
  have hi := h.equations.radius_s (h.g y) x y hxy hseg
  have hb : -(y - x) ≤ ∫ z in x..y, S.nu z (h.g y) := by
    have hh := intervalIntegral.integral_mono_on hxy
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (-1 : ℝ)) volume x y)
      hi.1 (fun z hz => by
        have hmem := hseg (show (z, h.g y) ∈ inSeg (h.g y) x y from ⟨hz, by simp⟩)
        linarith [neg_nu_le_one_closed h hmem])
    simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_neg, mul_one] using hh
  have hq : (x, h.g y) ∈ chartCylinder h.g T := ⟨hxI.1, hxI.2, hgxy, hover⟩
  have hr := (radius_label_bounds h hx.1 hq).1
  have hie := hi.2
  dsimp only at hie
  rw [(h.axis_values y hyI).1] at hie
  have hK : 0 < K := by linarith [h.K_ge_one]
  have hh := (div_le_iff₀ hK).mp hr
  have hm := mul_le_mul_of_nonneg_right (show S.r x (h.g y) ≤ y - x by linarith) hK.le
  nlinarith

/-- Every late axis point has a neighborhood with the same Lipschitz
constant `K`. Paper `e1a0fd5`, lines 1694–1698. -/
theorem axis_locally_lipschitz {b T K : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (x : ℝ) (hx : x ∈ Icc (K * b) T) :
    ∃ U ∈ 𝓝[Icc (K * b) T] x,
      LipschitzOnWith ⟨K, by linarith [h.K_ge_one]⟩ h.g U := by
  have hKb : 0 ≤ K * b := mul_nonneg (by linarith [h.K_ge_one]) h.b_pos.le
  have hxI : x ∈ Icc 0 T := ⟨hKb.trans hx.1, hx.2⟩
  let c := (h.g x + x) / 2
  have hgc : h.g x < c := by dsimp [c]; linarith [h.axis_before_boundary x hxI]
  have hcx : c < x := by dsimp [c]; linarith [h.axis_before_boundary x hxI]
  let U := Icc (K * b) T ∩ (h.g ⁻¹' Iio c ∩ Ioi c)
  have hU : U ∈ 𝓝[Icc (K * b) T] x := by
    apply inter_mem self_mem_nhdsWithin
    exact mem_nhdsWithin_of_mem_nhds
      (inter_mem (h.continuous_g.continuousAt.preimage_mem_nhds (Iio_mem_nhds hgc))
        (Ioi_mem_nhds hcx))
  refine ⟨U, hU, LipschitzOnWith.of_dist_le_mul ?_⟩
  intro y hy z hz
  change dist (h.g y) (h.g z) ≤ K * dist y z
  have hb {y z : ℝ} (hy : y ∈ U) (hz : z ∈ U) (hyz : y ≤ z) :
      dist (h.g y) (h.g z) ≤ K * dist y z := by
    have hmono := h.monotone_g ⟨hKb.trans hy.1.1, hy.1.2⟩
      ⟨hKb.trans hz.1.1, hz.1.2⟩ hyz
    have he := axis_increment_le_of_overlap h hy.1 hz.1 hyz (hz.2.1.le.trans hy.2.2.le)
    simpa only [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hmono),
      abs_of_nonpos (sub_nonpos.mpr hyz), neg_sub] using he
  rcases le_total y z with hyz | hzy
  · exact hb hy hz hyz
  · simpa only [dist_comm] using hb hz hy hzy

/-- The late axis label is absolutely continuous, with no added
regularity premise. Paper `e1a0fd5`, lines 1694–1707. -/
theorem axis_ac {b T K : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hT : K * b ≤ T) :
    AbsolutelyContinuousOnInterval h.g (K * b) T := by
  obtain ⟨L, hL⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact isCompact_Icc
    (show LocallyLipschitzOn (Icc (K * b) T) h.g from fun x hx =>
      ⟨⟨K, by linarith [h.K_ge_one]⟩, axis_locally_lipschitz h x hx⟩)
  apply LipschitzOnWith.absolutelyContinuousOnInterval
  simpa only [uIcc_of_le hT] using hL

/-- The axis derivative has magnitude at most `K` at every interior
late time, even when written using the total `deriv` function.
Paper `e1a0fd5`, lines 1694–1698. -/
theorem axis_deriv_abs_le {b T K x : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hx : x ∈ Ioo (K * b) T) :
    |deriv h.g x| ≤ K := by
  obtain ⟨U, hU, hL⟩ := axis_locally_lipschitz h x ⟨hx.1.le, hx.2.le⟩
  rw [nhdsWithin_eq_nhds.mpr (Icc_mem_nhds hx.1 hx.2)] at hU
  have hh := norm_deriv_le_of_lipschitzOn hU hL
  change ‖deriv h.g x‖ ≤ K at hh
  exact hh

/-- Integrating the local derivative bound gives the exact global
Lipschitz constant for the late axis graph. Paper `e1a0fd5`,
`eq:observability-axis-label-bounds`, lines 1694–1698. -/
theorem axis_lipschitz {b T K : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hT : K * b ≤ T) :
    LipschitzOnWith ⟨K, by linarith [h.K_ge_one]⟩ h.g (Icc (K * b) T) := by
  have hac := axis_ac h hT
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hsub : uIcc x y ⊆ uIcc (K * b) T := by
    rw [uIcc_of_le hT]
    exact uIcc_subset_Icc hx hy
  have he := (hac.mono hsub).integral_deriv_eq_sub
  have hb : ∀ᵐ z : ℝ, z ∈ uIoc x y → ‖deriv h.g z‖ ≤ K := by
    filter_upwards [show ∀ᵐ z : ℝ, z ≠ K * b by simp [ae_iff],
      show ∀ᵐ z : ℝ, z ≠ T by simp [ae_iff]] with z hz₀ hzT hz
    have hzI := hsub (uIoc_subset_uIcc hz)
    rw [uIcc_of_le hT] at hzI
    simpa only [Real.norm_eq_abs] using axis_deriv_abs_le h
      ⟨lt_of_le_of_ne hzI.1 hz₀.symm, lt_of_le_of_ne hzI.2 hzT⟩
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const_ae hb
  rw [he] at hh
  change dist (h.g x) (h.g y) ≤ K * dist x y
  simpa only [Real.norm_eq_abs, Real.dist_eq, abs_sub_comm, NNReal.coe_mk] using hh

end PropA4
end AcExtensionPrinciple

end
