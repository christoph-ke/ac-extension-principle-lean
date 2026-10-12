module

public import AcExtensionPrinciple.Continuation.OriginalClass

/-!
# Bounds for the carried scalar derivative fields

Paper `e1a0fd5`, `equations.tex` lines 220–275 and 1411. These bounds supply the product estimates
for the Jacobian-weighted fields for original class membership. No continuity of dvψ or duψ is added
to the standing hypotheses.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- An endpoint limit and a TV bound bound all off-axis values.
Paper `e1a0fd5`, lines 220–275 and 1411, component estimate. -/
theorem abs_bound_of_variation_limit {f : ℝ → ℝ} {a b L C : ℝ} (_hab : a < b)
    (hv : eVariationOn f (Icc a b) ≤ ENNReal.ofReal C)
    (hl : Tendsto f (𝓝[>] a) (𝓝 L)) :
    ∀ x ∈ Ioc a b, |f x| ≤ (ENNReal.ofReal C).toReal + |L| := by
  have hBV : BoundedVariationOn f (Icc a b) := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hv
  intro x hx
  have hdist : |f x - L| ≤ (ENNReal.ofReal C).toReal := by
    apply le_of_tendsto (tendsto_const_nhds.sub hl).abs
    filter_upwards [Ioo_mem_nhdsGT hx.1] with y hy
    have hxy : |f x - f y| ≤ (eVariationOn f (Icc a b)).toReal := by
      simpa only [Real.dist_eq] using
        (hBV.dist_le ⟨hx.1.le, hx.2⟩ ⟨hy.1.le, hy.2.le.trans hx.2⟩)
    exact hxy.trans (ENNReal.toReal_mono ENNReal.ofReal_ne_top hv)
  calc
    |f x| = |(f x - L) + L| := by congr 1; ring
    _ ≤ |f x - L| + |L| := abs_add_le _ _
    _ ≤ _ := add_le_add hdist le_rfl

/-- A continuous field on a punctured compact interval with a finite right
endpoint trace is bounded there. Paper `e1a0fd5`, lines 220–275 and 1411. -/
theorem bounded_punctured_interval {f : ℝ → ℝ} {a b L : ℝ} (hab : a < b)
    (hc : ContinuousOn f (Ioc a b)) (hl : Tendsto f (𝓝[>] a) (𝓝 L)) :
    ∃ C : ℝ, ∀ x ∈ Ioc a b, |f x| ≤ C := by
  have hnear : ∀ᶠ x in 𝓝[>] a, |f x| < |L| + 1 := by
    exact hl.abs.eventually_lt_const (by linarith)
  obtain ⟨d, hd, hsub⟩ := (mem_nhdsGT_iff_exists_mem_Ioc_Ioo_subset hab).mp hnear
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hc.mono (show Icc d b ⊆ Ioc a b from fun _ hx => ⟨hd.1.trans_le hx.1, hx.2⟩))
  refine ⟨max (|L| + 1) C, ?_⟩
  intro x hx
  rcases lt_or_ge x d with hxd | hdx
  · exact (hsub ⟨hx.1, hxd⟩).le.trans (le_max_left _ _)
  · have hCx : |f x| ≤ C := by simpa only [Real.norm_eq_abs] using hC x ⟨hdx, hx.2⟩
    exact hCx.trans (le_max_right _ _)

/-- Normalized axis traces and a continuous nonzero denominator give the
unnormalized outgoing derivative trace. Paper `e1a0fd5`,
`eq:regular-axis-scalar-traces`, lines 220–275 and 1411. -/
theorem outgoing_unnormalized_trace {ui a : ℝ} {f d : ℝ → ℝ → ℝ} {L : ℝ}
    (ha : (a, a) ∈ axis ui)
    (ht : Tendsto (fun p : ℝ × ℝ => f p.1 p.2 / d p.1 p.2)
      (𝓝[pastTriangle ui \ axis ui] (a, a)) (𝓝 L))
    (hd : ContinuousOn (fun p => d p.1 p.2) (pastTriangle ui))
    (hne : ∀ v ∈ Ioc a 0, d a v ≠ 0) :
    Tendsto (f a) (𝓝[>] a) (𝓝 (L * d a a)) := by
  have hmem : ∀ᶠ v in 𝓝[>] a, (a, v) ∈ pastTriangle ui \ axis ui := by
    filter_upwards [Ioo_mem_nhdsGT ha.2.1] with v hv
    refine ⟨⟨ha.1, ha.2.1, hv.1.le, hv.2.le⟩, ?_⟩
    exact fun haxis => (ne_of_gt hv.1) haxis.2.2
  have hp : Tendsto (fun v : ℝ => (a, v)) (𝓝[>] a)
      (𝓝[pastTriangle ui \ axis ui] (a, a)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨tendsto_const_nhds.prodMk_nhds (tendsto_id.mono_left nhdsWithin_le_nhds), hmem⟩
  have hden := (hd (a, a) (axis_subset_pastTriangle ui ha)).tendsto.comp
    (hp.mono_right (nhdsWithin_mono _ sdiff_subset))
  apply ((ht.comp hp).mul hden).congr'
  filter_upwards [Ioo_mem_nhdsGT ha.2.1] with v hv
  exact div_mul_cancel₀ _ (hne v ⟨hv.1, hv.2.le⟩)

/-- duψ is continuous on the off-axis selected cone, including v = 0,
by its transverse integral equation. Paper `e1a0fd5`, lines 220–275 and 1411. -/
theorem StandingFull.continuous_dupsi_cone {ui ū : ℝ} {S : SSFields}
    (h : StandingFull ui S) (hū : ū ∈ Ico ui 0) :
    ContinuousOn (S.dupsi ū) (Ioc ū 0) := by
  apply continuousOn_of_locally_continuousOn
  intro x hx
  let y := (ū + x) / 2
  have hy : ū < y := by dsimp [y]; linarith [hx.1]
  have hyx : y < x := by dsimp [y]; linarith [hx.1]
  have hs := outSeg_subset_offAxis hū.1 hū.2 hy (le_refl (0 : ℝ))
  have hac : AbsolutelyContinuousOnInterval (S.dupsi ū) y 0 :=
    intervalPrimitive_ac (hyx.le.trans hx.2) (fun z hz =>
      h.regularCenter.localBV.dupsi_out ū y z hz.1
        ((prod_mono_right (Icc_subset_Icc le_rfl hz.2)).trans hs))
  have hacon : ContinuousOn (S.dupsi ū) (Icc y 0) := by
    simpa only [uIcc_of_le (hyx.le.trans hx.2)] using hac.continuousOn
  exact ⟨Ioi y, isOpen_Ioi, hyx, hacon.mono
    (fun _ hv => ⟨hv.2.le, hv.1.2⟩)⟩

/-- Uniform absolute values of all carried fields on a proper original triangle off Γ. Paper
`e1a0fd5`, lines 220–275 and 1411. The selected cone provides the anchor for incoming duψ variation.
-/
theorem StandingFull.proper_triangle_raw_bounds {ui ū c : ℝ} {S : SSFields}
    (h : StandingFull ui S) (hū : ū ∈ Ico ui 0) (hc : c < 0) :
    ∃ M : ℝ, ∀ p ∈ offAxis (properOriginalTriangle ū c),
      |S.lam p.1 p.2| ≤ M ∧ |S.nu p.1 p.2| ≤ M ∧ |S.phi p.1 p.2| ≤ M ∧
        |S.dvpsi p.1 p.2| ≤ M ∧ |S.dupsi p.1 p.2| ≤ M := by
  let K := properOriginalTriangle ū c
  have hK := isCompact_properOriginalTriangle ū c
  have hKD := properOriginalTriangle_subset hū.1 hc
  rcases hK.exists_bound_of_continuousOn (h.regularCenter.continuous_lam.mono hKD) with ⟨L, hL⟩
  rcases hK.exists_bound_of_continuousOn (h.regularCenter.continuous_nu.mono hKD) with ⟨N, hN⟩
  rcases hK.exists_bound_of_continuousOn (h.regularCenter.continuous_phi.mono hKD) with ⟨P, hP⟩
  rcases h.regularCenter.localBV.psi_variation K hK hKD with ⟨C, hout, hin⟩
  have hDV (u : ℝ) (hu : u ∈ Icc ū c) :
      Tendsto (S.dvpsi u) (𝓝[>] u) (𝓝 (S.phi u u * S.lam u u)) :=
    outgoing_unnormalized_trace ⟨hū.1.trans hu.1, hu.2.trans_lt hc, rfl⟩
      (h.regularCenter.axis_dvpsi_trace _ ⟨hū.1.trans hu.1, hu.2.trans_lt hc, rfl⟩)
      h.regularCenter.continuous_lam (fun v hv => ne_of_gt
        (h.lam_pos (p := (u, v)) ⟨hū.1.trans hu.1, hu.2.trans_lt hc, hv.1.le, hv.2⟩))
  have hDU : Tendsto (S.dupsi ū) (𝓝[>] ū) (𝓝 (S.phi ū ū * S.nu ū ū)) :=
    outgoing_unnormalized_trace ⟨hū.1, hū.2, rfl⟩
      (h.regularCenter.axis_dupsi_trace _ ⟨hū.1, hū.2, rfl⟩)
      h.regularCenter.continuous_nu (fun v hv => ne_of_lt
        (h.nu_neg (p := (ū, v)) ⟨hū.1, hū.2, hv.1.le, hv.2⟩))
  rcases bounded_punctured_interval hū.2 (h.continuous_dupsi_cone hū) hDU with ⟨Q, hQ⟩
  let R := (ENNReal.ofReal C).toReal
  refine ⟨max (max L N) (max P (max (R + |P| * |L|) (R + Q))), ?_⟩
  intro p hp
  have hpa : (p.1, p.1) ∈ K := ⟨hp.1.1, le_rfl, (hp.1.1.2.trans_lt hc).le⟩
  have hgeom : |S.lam p.1 p.2| ≤ L ∧ |S.nu p.1 p.2| ≤ N ∧ |S.phi p.1 p.2| ≤ P := by
    simpa only [Real.norm_eq_abs] using ⟨hL p hp.1, hN p hp.1, hP p hp.1⟩
  have huv : p.1 < p.2 := lt_of_le_of_ne hp.1.2.1 hp.2
  have hs : outSeg p.1 p.1 0 ⊆ K := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    simp only [mem_singleton_iff] at hx
    subst x
    exact ⟨hp.1.1, hy⟩
  have hvbound := abs_bound_of_variation_limit (hp.1.1.2.trans_lt hc)
    (hout p.1 p.1 0 (hp.1.1.2.trans_lt hc).le hs) (hDV p.1 hp.1.1) p.2 ⟨huv, hp.1.2.2⟩
  have hprod : |S.phi p.1 p.1 * S.lam p.1 p.1| ≤ |P| * |L| := by
    rw [abs_mul]
    have hpaP : |S.phi p.1 p.1| ≤ P := by
      simpa only [Real.norm_eq_abs] using hP _ hpa
    have hpaL : |S.lam p.1 p.1| ≤ L := by
      simpa only [Real.norm_eq_abs] using hL _ hpa
    exact mul_le_mul (hpaP.trans (le_abs_self P)) (hpaL.trans (le_abs_self L))
      (abs_nonneg _) (abs_nonneg _)
  have hi : inSeg p.2 ū p.1 ⊆ K := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    simp only [mem_singleton_iff] at hy
    subst y
    exact ⟨⟨hx.1, hx.2.trans hp.1.1.2⟩, hx.2.trans hp.1.2.1, hp.1.2.2⟩
  have hTV := hin p.2 ū p.1 hp.1.1.1 hi
  have hBV : BoundedVariationOn (fun u => S.dupsi u p.2) (Icc ū p.1) :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hTV
  have hibound := boundedVariation_abs_bound hBV (right_mem_Icc.mpr hp.1.1.1)
    (left_mem_Icc.mpr hp.1.1.1)
  have hiabs : |S.dupsi p.1 p.2| ≤ R + Q := hibound.trans (add_le_add
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top hTV)
    (hQ p.2 ⟨hp.1.1.1.trans_lt huv, hp.1.2.2⟩))
  refine ⟨hgeom.1.trans ((le_max_left L N).trans (le_max_left _ _)),
    hgeom.2.1.trans ((le_max_right L N).trans (le_max_left _ _)),
    hgeom.2.2.trans ((le_max_left _ _).trans (le_max_right _ _)),
    (hvbound.trans (add_le_add le_rfl hprod)).trans ?_, hiabs.trans ?_⟩
  · exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  · exact (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))

end AcExtensionPrinciple

end
