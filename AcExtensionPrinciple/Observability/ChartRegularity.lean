module

public import AcExtensionPrinciple.Observability.ChartTriangle
public import AcExtensionPrinciple.Observability.ChartEquations
public import Mathlib.Topology.Algebra.MetricSpace.Lipschitz

/-!
# Characteristic BV regularity and boundary traces

Paper `e1a0fd5`, `equations.tex` line 1522. On a positive-radius triangle,
the mixed equation expresses each first scalar derivative as a BV function
of one label plus a continuous correction. This gives bounded derivatives
and their joint continuity at almost every boundary point.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- A separated BV part and a continuous correction give boundedness and
almost everywhere joint continuity on the diagonal. Paper `e1a0fd5`, line 1522. -/
theorem chart_separated_regularity {U V : ℝ → ℝ → ℝ} {α β : ℝ → ℝ}
    {F G : ℝ × ℝ → ℝ} {a c : ℝ} (hac : a ≤ c)
    (hα : BoundedVariationOn α (Icc a c)) (hβ : BoundedVariationOn β (Icc a c))
    (hF : Continuous F) (hG : Continuous G)
    (hU : ∀ q ∈ chartTriangle a c, U q.1 q.2 = α q.1 + F q)
    (hV : ∀ q ∈ chartTriangle a c, V q.1 q.2 = β q.2 + G q) :
    (∃ M, 0 ≤ M ∧ ∀ s t, (s, t) ∈ chartTriangle a c → |U s t| ≤ M ∧ |V s t| ≤ M) ∧
    (∀ᵐ x ∂volume, x ∈ Icc a c →
      ContinuousWithinAt (fun q : ℝ × ℝ => U q.1 q.2) (chartTriangle a c) (x, x) ∧
      ContinuousWithinAt (fun q : ℝ × ℝ => V q.1 q.2) (chartTriangle a c) (x, x)) := by
  obtain ⟨B, hB⟩ := (isCompact_chartTriangle a c).exists_bound_of_continuousOn hF.continuousOn
  obtain ⟨D, hD⟩ := (isCompact_chartTriangle a c).exists_bound_of_continuousOn hG.continuousOn
  constructor
  · let M := |α a| + (eVariationOn α (Icc a c)).toReal + |B| +
      |β a| + (eVariationOn β (Icc a c)).toReal + |D|
    refine ⟨M, by dsimp [M]; positivity, ?_⟩
    intro s t hq
    have hsa : |α s| ≤ |α a| + (eVariationOn α (Icc a c)).toReal := by
      have hh := hα.dist_le ⟨hq.1.trans hq.2.1, hq.2.2⟩ ⟨le_rfl, hac⟩
      rw [Real.dist_eq] at hh
      have ha : α s = α a + (α s - α a) := by ring
      rw [ha]
      exact (abs_add_le _ _).trans (by linarith)
    have hta : |β t| ≤ |β a| + (eVariationOn β (Icc a c)).toReal := by
      have hh := hβ.dist_le ⟨hq.1, hq.2.1.trans hq.2.2⟩ ⟨le_rfl, hac⟩
      rw [Real.dist_eq] at hh
      have ha : β t = β a + (β t - β a) := by ring
      rw [ha]
      exact (abs_add_le _ _).trans (by linarith)
    have hfq : |F (s, t)| ≤ |B| := (hB (s, t) hq).trans (le_abs_self _)
    have hgq : |G (s, t)| ≤ |D| := (hD (s, t) hq).trans (le_abs_self _)
    rw [hU (s, t) hq, hV (s, t) hq]
    constructor
    · exact (abs_add_le _ _).trans (by
        dsimp [M]
        linarith [abs_nonneg (β a), abs_nonneg D,
          ENNReal.toReal_nonneg (a := eVariationOn β (Icc a c))])
    · exact (abs_add_le _ _).trans (by
        dsimp [M]
        linarith [abs_nonneg (α a), abs_nonneg B,
          ENNReal.toReal_nonneg (a := eVariationOn α (Icc a c))])
  · have hα' : BoundedVariationOn α (uIcc a c) := by simpa [uIcc_of_le hac] using hα
    have hβ' : BoundedVariationOn β (uIcc a c) := by simpa [uIcc_of_le hac] using hβ
    filter_upwards [hα'.ae_differentiableAt_of_mem_uIcc,
      hβ'.ae_differentiableAt_of_mem_uIcc] with x hxα hxβ
    intro hx
    have hx' : x ∈ uIcc a c := by simpa [uIcc_of_le hac] using hx
    have hca : ContinuousAt (fun q : ℝ × ℝ => α q.1) (x, x) :=
      (hxα hx').continuousAt.comp continuous_fst.continuousAt
    have hcb : ContinuousAt (fun q : ℝ × ℝ => β q.2) (x, x) :=
      (hxβ hx').continuousAt.comp continuous_snd.continuousAt
    exact ⟨(hca.add hF.continuousAt).continuousWithinAt.congr_of_mem hU ⟨hx.1, le_rfl, hx.2⟩,
      (hcb.add hG.continuousAt).continuousWithinAt.congr_of_mem hV ⟨hx.1, le_rfl, hx.2⟩⟩

namespace NormalizedChartData

variable {b T K : ℝ} {S : SSFields} (h : NormalizedChartData b T K S)

include h

/-- The wave coefficient is continuous on every positive-radius subdomain.
Paper `e1a0fd5`, `eq:observability-chart-equations`, lines 1490–1492, 1522. -/
theorem continuous_wave_on {C : Set (ℝ × ℝ)}
    (hC : C ⊆ chartInterior (chartCylinder h.g T) S) :
    ContinuousOn (fun q => S.radiusCoeff q.1 q.2 * S.phi q.1 q.2) C := by
  have hr := h.continuous_r.mono (fun q hq => (hC hq).1)
  have hm := h.continuous_m.mono (fun q hq => (hC hq).1)
  have hl := h.continuous_lam.mono (fun q hq => (hC hq).1)
  have hn := h.continuous_nu.mono (fun q hq => (hC hq).1)
  have hp := h.continuous_phi.mono (fun q hq => (hC hq).1)
  have hμ : ContinuousOn (fun q => S.mu q.1 q.2) C :=
    (continuousOn_const.mul hm).div hr (fun q hq => (hC hq).2.ne')
  exact (((hμ.mul hl).mul hn).div ((continuousOn_const.sub hμ).mul hr)
    (fun q hq => mul_ne_zero (h.gap_pos (hC hq).1).ne' (hC hq).2.ne')).mul hp

/-- The mixed equation supplies the separated first-derivative representation.
Paper `e1a0fd5`, `equations.tex` line 1522. The BV premises are obtained directly
from the inherited compact characteristic BV bounds, not assumed on the boundary. -/
theorem scalar_separated {a c : ℝ} (ha : 0 ≤ a) (hac : a ≤ c) (hc : c ≤ T)
    (hg : h.g c < a) :
    ∃ F G : ℝ × ℝ → ℝ, Continuous F ∧ Continuous G ∧
      BoundedVariationOn (fun s => S.dupsi s a) (Icc a c) ∧
      BoundedVariationOn (S.dvpsi c) (Icc a c) ∧
      (∀ q ∈ chartTriangle a c, S.dupsi q.1 q.2 = S.dupsi q.1 a + F q) ∧
      (∀ q ∈ chartTriangle a c, S.dvpsi q.1 q.2 = S.dvpsi c q.2 + G q) := by
  have htri := h.triangle_subset ha hac hc hg
  obtain ⟨Q, hQ, hQeq⟩ := chartTriangle_continuous_extension (h.continuous_wave_on htri)
  let F : ℝ × ℝ → ℝ := fun q => ∫ z in a..q.2, Q (q.1, z)
  let G : ℝ × ℝ → ℝ := fun q => -(∫ σ in q.1..c, Q (σ, q.2))
  have hF : Continuous F := by
    apply continuous_moving_interval_integral _ continuous_const continuous_snd
    exact hQ.comp (continuous_fst.fst.prodMk continuous_snd)
  have hG : Continuous G := by
    apply Continuous.neg
    apply continuous_moving_interval_integral _ continuous_fst continuous_const
    exact hQ.comp (continuous_snd.prodMk continuous_fst.snd)
  have hcompact := isCompact_chartTriangle a c
  have hdom : chartTriangle a c ⊆ chartCylinder h.g T := fun q hq => (htri hq).1
  obtain ⟨A, hA⟩ := h.psi_s_variation _ hcompact hdom
  obtain ⟨B, hB⟩ := h.psi_t_variation _ hcompact hdom
  have hα : BoundedVariationOn (fun s => S.dupsi s a) (Icc a c) :=
    lt_top_iff_ne_top.mp ((hA a a c hac (chartTriangle_in_subset le_rfl le_rfl le_rfl)).trans_lt
      ENNReal.ofReal_lt_top)
  have hβ : BoundedVariationOn (S.dvpsi c) (Icc a c) :=
    lt_top_iff_ne_top.mp ((hB c a c hac (chartTriangle_out_subset le_rfl le_rfl le_rfl)).trans_lt
      ENNReal.ofReal_lt_top)
  refine ⟨F, G, hF, hG, hα, hβ, ?_, ?_⟩
  · intro q hq
    have hi := (h.equations.dupsi_t q.1 a q.2 hq.1
      ((chartTriangle_out_subset le_rfl hq.2.1 hq.2.2).trans htri)).2
    have he : (∫ z in a..q.2, S.radiusCoeff q.1 z * S.phi q.1 z) = F q := by
      apply intervalIntegral.integral_congr
      intro z hz
      rw [uIcc_of_le hq.1] at hz
      exact (hQeq (q.1, z) ⟨hz.1, hz.2.trans hq.2.1, hq.2.2⟩).symm
    rw [he] at hi
    linarith
  · intro q hq
    have hi := (h.equations.dvpsi_s q.2 q.1 c hq.2.2
      ((chartTriangle_in_subset hq.1 hq.2.1 le_rfl).trans htri)).2
    have he : (∫ σ in q.1..c, S.radiusCoeff σ q.2 * S.phi σ q.2) = -G q := by
      simp only [G, neg_neg]
      apply intervalIntegral.integral_congr
      intro σ hσ
      rw [uIcc_of_le hq.2.2] at hσ
      exact (hQeq (σ, q.2) ⟨hq.1, hq.2.1.trans hσ.1, hσ.2⟩).symm
    rw [he] at hi
    linarith

/-- First scalar derivatives are bounded on each positive-radius triangle and
jointly continuous at almost every diagonal point. Paper `e1a0fd5`, line 1522. -/
theorem scalar_triangle_regularity {a c : ℝ} (ha : 0 ≤ a) (hac : a ≤ c)
    (hc : c ≤ T) (hg : h.g c < a) :
    (∃ M, 0 ≤ M ∧ ∀ s t, (s, t) ∈ chartTriangle a c →
      |S.dupsi s t| ≤ M ∧ |S.dvpsi s t| ≤ M) ∧
    (∀ᵐ x ∂volume, x ∈ Icc a c →
      ContinuousWithinAt (fun q => S.dupsi q.1 q.2) (chartTriangle a c) (x, x) ∧
      ContinuousWithinAt (fun q => S.dvpsi q.1 q.2) (chartTriangle a c) (x, x)) := by
  obtain ⟨F, G, hF, hG, hα, hβ, hU, hV⟩ := h.scalar_separated ha hac hc hg
  exact chart_separated_regularity hac hα hβ hF hG hU hV

/-- The scalar boundary trace is AC, derived from the characteristic equations and BV bounds. Paper
`e1a0fd5`, line 1522 (the scalar trace regularity). -/
theorem boundary_psi_lipschitz : ∃ L, LipschitzOnWith L (fun s => chartPsi S s s) (Icc 0 T) := by
  apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact isCompact_Icc
  intro x hx
  obtain ⟨a, c, ha, hac, hc, hg, hnhds⟩ := h.exists_boundary_triangle hx
  obtain ⟨M, hM, hbound⟩ := (h.scalar_triangle_regularity ha hac hc hg).1
  have htri := h.triangle_subset ha hac hc hg
  refine ⟨⟨2 * M, by positivity⟩, Icc a c, hnhds, ?_⟩
  apply chart_diagonal_lipschitz hM
  · intro l r hl hlr hr
    exact h.equations.psi_s l l r hlr
      (fun q hq => (htri (chartTriangle_in_subset hl le_rfl hr hq)).1)
  · intro l r hl hlr hr
    exact h.equations.psi_t r l r hlr
      (fun q hq => (htri (chartTriangle_out_subset hl le_rfl hr hq)).1)
  · exact hbound

/-- The scalar boundary chain rule holds almost everywhere. Paper `e1a0fd5`,
`eq:observability-shifted-balance`, lines 1518, 1522. -/
theorem boundary_psi_ae_hasDerivAt :
    ∀ᵐ s ∂volume, s ∈ Icc 0 T →
      HasDerivAt (fun s => chartPsi S s s) (S.dupsi s s + S.dvpsi s s) s := by
  apply chart_ae_of_local isCompact_Icc
  intro x hx
  obtain ⟨a, c, ha, hac, hc, hg, hnhds⟩ := h.exists_boundary_triangle hx
  have htri := h.triangle_subset ha hac hc hg
  refine ⟨Icc a c, hnhds, ?_⟩
  filter_upwards [(h.scalar_triangle_regularity ha hac hc hg).2,
    show ∀ᵐ y : ℝ ∂volume, y ≠ a by simp [ae_iff],
    show ∀ᵐ y : ℝ ∂volume, y ≠ c by simp [ae_iff]] with y hy hya hyc
  intro hyI
  apply chart_diagonal_hasDerivAt ⟨lt_of_le_of_ne hyI.1 hya.symm, lt_of_le_of_ne hyI.2 hyc⟩
  · intro l r hl hlr hr
    exact h.equations.psi_s l l r hlr
      (fun q hq => (htri (chartTriangle_in_subset hl le_rfl hr hq)).1)
  · intro l r hl hlr hr
    exact h.equations.psi_t r l r hlr
      (fun q hq => (htri (chartTriangle_out_subset hl le_rfl hr hq)).1)
  · exact (hy hyI).1
  · exact (hy hyI).2

end NormalizedChartData

end AcExtensionPrinciple

end
