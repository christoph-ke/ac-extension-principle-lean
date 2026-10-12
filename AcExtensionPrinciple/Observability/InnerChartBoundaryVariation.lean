module

public import AcExtensionPrinciple.Observability.InnerChartTraceBounds

/-!
# Boundary expansion BV derived from the outer normalized chart

Paper `e1a0fd5`, `equations.tex` line 1522 and lines 1460–1473, 1901.
This discharges both Jacobian regularity premises of the coordinate constructor.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology NNReal

/-- A positive continuous function whose logarithm is Lipschitz has BV.
Only the compact logarithmic image is used to bound the exponential.
Paper `e1a0fd5`, coordinate calculus at lines 1460–1473, 1901. -/
theorem inner_bv_of_log_lipschitz {f : ℝ → ℝ} {x y : ℝ} {L : ℝ≥0}
    (hxy : x ≤ y) (hf : ContinuousOn f (Icc x y))
    (hp : ∀ s ∈ Icc x y, 0 < f s)
    (hl : LipschitzOnWith L (fun s => Real.log (f s)) (Icc x y)) :
    BoundedVariationOn f (Icc x y) := by
  have hlog : ContinuousOn (fun s => Real.log (f s)) (Icc x y) :=
    hf.log (fun s hs => (hp s hs).ne')
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hlog
  have hmap : MapsTo (fun s => Real.log (f s)) (Icc x y) (Icc (-|B|) |B|) := by
    intro s hs
    have hh : |Real.log (f s)| ≤ |B| := by
      simpa only [Real.norm_eq_abs] using (hB s hs).trans (le_abs_self B)
    exact abs_le.mp hh
  have hExpD : ContDiffOn ℝ 1 Real.exp (Icc (-|B|) |B|) := Real.contDiff_exp.contDiffOn
  obtain ⟨E, hE⟩ := hExpD.exists_lipschitzOnWith (by decide) (convex_Icc _ _) isCompact_Icc
  have hlBV : BoundedVariationOn (fun s => Real.log (f s)) (Icc x y) := by
    have hac := (show LipschitzOnWith L (fun s => Real.log (f s)) (uIcc x y) by
      simpa only [uIcc_of_le hxy] using hl).absolutelyContinuousOnInterval
    simpa only [uIcc_of_le hxy] using hac.boundedVariationOn
  have hb := hE.comp_boundedVariationOn hmap hlBV
  change eVariationOn f (Icc x y) ≠ ⊤
  rw [← eVariationOn.congr (show EqOn (fun s => Real.exp (Real.log (f s))) f (Icc x y)
    from fun s hs => Real.exp_log (hp s hs))]
  exact hb

namespace InnerCylinder

variable {b T K a s₀ s₁ : ℝ} {S : SSFields} {h : NormalizedChartData b T K S}
variable (c : InnerCylinder h a s₀ s₁)

/-- Uniform increment control on overlapping inner slices gives a global
compact-interval Lipschitz trace. Paper `e1a0fd5`, line 1522 and 1901. -/
theorem trace_lipschitz_of_overlap {F : ℝ → ℝ} {D : ℝ≥0}
    (hinc : ∀ x ∈ Icc s₀ s₁, ∀ y ∈ Icc s₀ s₁, x ≤ y → c.v y ≤ x →
      |F x - F y| ≤ (D : ℝ) * (y - x)) :
    ∃ L : ℝ≥0, LipschitzOnWith L F (Icc s₀ s₁) := by
  apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact isCompact_Icc
  intro z hz
  let d := (c.v z + z) / 2
  have hvd : c.v z < d := by dsimp [d]; linarith [(c.points z hz).2.1]
  have hdz : d < z := by dsimp [d]; linarith [(c.points z hz).2.1]
  let U := Icc s₀ s₁ ∩ ({x | c.v x < d} ∩ Ioi d)
  have hvnear : {x | c.v x < d} ∈ 𝓝[Icc s₀ s₁] z :=
    (c.continuous_v z hz) (Iio_mem_nhds hvd)
  have hU : U ∈ 𝓝[Icc s₀ s₁] z := inter_mem self_mem_nhdsWithin
    (inter_mem hvnear (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hdz)))
  refine ⟨D, U, hU, LipschitzOnWith.of_dist_le_mul ?_⟩
  intro x hx y hy
  have hi {x y : ℝ} (hx : x ∈ U) (hy : y ∈ U) (hxy : x ≤ y) :
      dist (F x) (F y) ≤ (D : ℝ) * dist x y := by
    have hh := hinc x hx.1 y hy.1 hxy (hy.2.1.le.trans hx.2.2.le)
    simpa only [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxy), neg_sub] using hh
  rcases le_total x y with hxy | hyx
  · exact hi hx hy hxy
  · simpa only [dist_comm] using hi hy hx hyx

/-- Both inner boundary expansion logarithms are Lipschitz, proved from
the outer characteristic identities and compact uniform BV bounds alone.
Paper `e1a0fd5`, line 1522 and lines 1460–1473, 1901. -/
theorem boundary_log_lipschitz :
    (∃ L : ℝ≥0, LipschitzOnWith L (fun s => Real.log (-S.nu s (c.v s))) (Icc s₀ s₁)) ∧
      ∃ L : ℝ≥0, LipschitzOnWith L (fun s => Real.log (S.lam s (c.v s))) (Icc s₀ s₁) := by
  obtain ⟨C, L, hb, hnu, hlam⟩ := h.inner_coefficient_controls c.a_pos
  obtain ⟨V, hv⟩ := c.v_lipschitz
  let duration : ℝ≥0 := ⟨T, h.T_nonneg⟩
  constructor
  · apply c.trace_lipschitz_of_overlap (D := C * V + L * duration + C)
    intro x hx y hy hxy hover
    exact c.nu_log_increment hv (fun p hp => (hb p hp).1) hnu hx hy hxy hover
  · apply c.trace_lipschitz_of_overlap (D := C * V + L * V * duration + C)
    intro x hx y hy hxy hover
    exact c.lam_log_increment hv (fun p hp => (hb p hp).2) hlam hx hy hxy hover

/-- Both actual boundary expansions have finite variation. This is the
missing internal premise of exists_coordinates_of_boundary_variation;
it is discharged from NormalizedChartData without strengthening the
solution class or the paper statement. Paper `e1a0fd5`, line 1522 and
lines 1460–1473, 1901. -/
theorem boundary_variation :
    BoundedVariationOn (fun s => -S.nu s (c.v s)) (Icc s₀ s₁) ∧
      BoundedVariationOn (fun s => S.lam s (c.v s)) (Icc s₀ s₁) := by
  obtain ⟨hnu, hlam⟩ := c.boundary_log_lipschitz
  obtain ⟨N, hn⟩ := hnu
  obtain ⟨L, hl⟩ := hlam
  constructor
  · exact inner_bv_of_log_lipschitz c.ordered c.density_continuous_positive.1
      c.density_continuous_positive.2 hn
  · exact inner_bv_of_log_lipschitz c.ordered
      (h.continuous_lam.comp (continuousOn_id.prodMk c.continuous_v)
        (fun _ hs => (c.source_mem hs).1))
      (fun _ hs => (h.signs _ _ (c.source_mem hs).1).1) hl

/-- The inner chart coordinates now exist with all Jacobian BV premises
discharged. Paper `e1a0fd5`, lines 1460–1473 and 1877–1907. -/
theorem exists_coordinates
    (hhalf : ∀ s ∈ Icc s₀ s₁, 1 / 2 ≤ -S.nu s (c.v s)) :
    Nonempty (InnerBoundaryCoordinates c (c.clock s₁)) :=
  c.exists_coordinates_of_boundary_variation hhalf c.boundary_variation.1 c.boundary_variation.2

end InnerCylinder

end AcExtensionPrinciple

end
