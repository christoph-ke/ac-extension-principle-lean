module

public import AcExtensionPrinciple.Weighted.ClassAmplitude

/-!
# The actual radial operator in radius coordinates

Paper `e1a0fd5`, `lem:weighted-radial-estimates`,
`equations.tex` lines 1204–1215. The radius-coordinate datum includes
the actual incoming scalar amplitude and the Jacobian 1/λ.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory
open scoped ENNReal

/-- Data for applying the already-proved radial Hardy estimates to an actual
solution cone. Paper `e1a0fd5`, lines 1204–1215. -/
structure WeightedConeData (S : SSFields) (W : ℝ × ℝ → ℝ) (u δ : ℝ) where
  g : ℝ → ℝ
  w : ℝ → ℝ
  f : ℝ → ℝ
  measurable_f : Measurable f
  inverse : ∀ v ∈ Icc u 0, g (S.r u v) = v
  weight_eq : ∀ v ∈ Ioc u 0, w (S.r u v) = -S.nu u v
  datum_eq : ∀ v ∈ Ioc u 0,
    f (S.r u v) = weightedIncomingAmplitude S u v * W (u, v) / S.lam u v
  operator_eq : ∀ v ∈ Ioc u 0,
    radialOperator f (S.r u v) = weightedRadialOperator S W (u, v)
  weight_pos : ∀ x ∈ Ioc 0 (S.r u 0), 0 < w x
  weight_mono : MonotoneOn w (Ioc 0 (S.r u 0))
  weight_growth : RadialWeightGrowth w (S.r u 0) δ

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Construct the radius-coordinate data using only standing assumptions,
the late mass-ratio bound, and measurable input. Paper `e1a0fd5`,
`eq:remainder-radial-estimate`, lines 1204–1215. -/
theorem weighted_exists_cone_data {u δ : ℝ} {W : ℝ × ℝ → ℝ}
    (hu : ui ≤ u) (hu0 : u < 0) (hW : Measurable W)
    (hsmall : ∀ v ∈ Ioc u 0, S.mu u v / (1 - S.mu u v) ≤ δ) :
    Nonempty (WeightedConeData S W u δ) := by
  obtain ⟨g, hgm, hgr, hgi, hgmono⟩ := h.weighted_exists_radial_inverse hu hu0
  obtain ⟨A, hA, heA⟩ := h.weighted_exists_measurable_amplitude hu hu0
  obtain ⟨L, hL, heL⟩ := exists_measurable_Ioc_extension
    ((continuous_out h.regularCenter.continuous_lam
      (outSeg_subset_triangle hu hu0 le_rfl le_rfl)).mono Ioo_subset_Icc_self)
  let f := fun x => A (g x) * W (u, g x) / L (g x)
  let w := fun x => -S.nu u (g x)
  have hgpos (x : ℝ) (hx : x ∈ Ioc 0 (S.r u 0)) : g x ∈ Ioc u 0 := by
    have hc := (hgr x ⟨hx.1.le, hx.2⟩).1
    refine ⟨lt_of_le_of_ne hc.1 ?_, hc.2⟩
    intro he
    have hrx := (hgr x ⟨hx.1.le, hx.2⟩).2
    rw [← he, (h.regularCenter.localBV.axis_values u
      ⟨hu, hu0, le_rfl, hu0.le⟩).1] at hrx
    exact hx.1.ne' hrx.symm
  have hfe (v : ℝ) (hv : v ∈ Ioc u 0) :
      f (S.r u v) = weightedIncomingAmplitude S u v * W (u, v) / S.lam u v := by
    dsimp only [f]
    rw [hgi v (Ioc_subset_Icc_self hv), ← heA hv, ← heL hv]
  refine ⟨{
    g := g
    w := w
    f := f
    measurable_f := ((hA.comp hgm).mul (hW.comp (measurable_const.prodMk hgm))).div
      (hL.comp hgm)
    inverse := hgi
    weight_eq := ?_
    datum_eq := hfe
    operator_eq := ?_
    weight_pos := ?_
    weight_mono := ?_
    weight_growth := ?_
  }⟩
  · intro v hv
    dsimp only [w]
    rw [hgi v (Ioc_subset_Icc_self hv)]
  · intro v hv
    have he := h.weighted_integral_change_radius hu hu0 (Ioc_subset_Icc_self hv) hgi
      (fun s => S.r u s * (weightedIncomingAmplitude S u s * W (u, s)))
    have hi : (∫ x in Ioo 0 (S.r u v), x * f x) =
        ∫ s in u..v, S.r u s * (weightedIncomingAmplitude S u s * W (u, s)) := by
      rw [he]
      apply setIntegral_congr_fun measurableSet_Ioo
      intro x hx
      have hxR : x ∈ Ioc 0 (S.r u 0) :=
        ⟨hx.1, hx.2.le.trans ((h.weighted_radius_strictMonoOn hu hu0).monotoneOn
          (Ioc_subset_Icc_self hv) ⟨hu0.le, le_rfl⟩ hv.2)⟩
      have hrx := (hgr x ⟨hxR.1.le, hxR.2⟩).2
      have hfx := hfe (g x) (hgpos x hxR)
      rw [hrx] at hfx
      dsimp only
      rw [hfx, hrx]
      ring
    simp only [radialOperator, weightedRadialOperator, hi]
  · intro x hx
    exact neg_pos.mpr (h.nu_neg (p := (u, g x))
      ⟨hu, hu0, (hgpos x hx).1.le, (hgpos x hx).2⟩)
  · intro x hx y hy hxy
    exact neg_le_neg (h.nu_le_of_le hu hu0 (hgpos x hx).1
      (hgmono (Ioc_subset_Icc_self hx) (Ioc_subset_Icc_self hy) hxy) (hgpos y hy).2)
  · intro y x hy hyx hxR
    have hys : y ∈ Ioc 0 (S.r u 0) := ⟨hy, hyx.trans hxR⟩
    have hxs : x ∈ Ioc 0 (S.r u 0) := ⟨hy.trans_le hyx, hxR⟩
    have hab := hgmono (Ioc_subset_Icc_self hys) (Ioc_subset_Icc_self hxs) hyx
    have he := (h.late_radial_expansion_comparison_of_smallness hu hu0 (hgpos y hys).1
      hab (hgpos x hxs).2 (fun s hs => hsmall s
        ⟨(hgpos y hys).1.trans_le hs.1, hs.2.trans (hgpos x hxs).2⟩)).2
    rw [(hgr x (Ioc_subset_Icc_self hxs)).2,
      (hgr y (Ioc_subset_Icc_self hys)).2] at he
    dsimp only [w]
    have hn := neg_pos.mpr (h.nu_neg (p := (u, g y))
      ⟨hu, hu0, (hgpos y hys).1.le, (hgpos y hys).2⟩)
    simpa [mul_comm] using (div_le_iff₀ hn).mp he

end StandingFull

end AcExtensionPrinciple

end
