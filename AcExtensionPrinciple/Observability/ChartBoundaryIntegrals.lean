module

public import AcExtensionPrinciple.Observability.ChartMassRegularity
public import AcExtensionPrinciple.Observability.Energy

/-!
# Finite boundary scalar energy in a regular normalized chart

Paper `e1a0fd5`, `equations.tex` line 1522 and lines 1524–1528.
Compact BV bounds give square integrability of the boundary derivatives;
no finite-energy assumption is added to Lemma A.2.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- The square of a BV function plus a continuous function is integrable.
Paper `e1a0fd5`, local `L²` justification at line 1522. -/
theorem chart_separated_square_integrable {α F : ℝ → ℝ} {a c : ℝ}
    (hα : BoundedVariationOn α (uIcc a c)) (hF : Continuous F) :
    IntervalIntegrable (fun s => (α s + F s) ^ 2) volume a c := by
  have hα2 := (hα.mul hα).intervalIntegrable (μ := volume) (by rfl)
  have hαF := (hα.intervalIntegrable (μ := volume) (by rfl)).mul_continuousOn hF.continuousOn
  have hF2 := (hF.mul hF).intervalIntegrable (μ := volume) a c
  convert (hα2.add (hαF.const_mul 2)).add hF2 using 1
  funext s
  simp only [Pi.mul_apply]
  ring

namespace NormalizedChartData

variable {b T K : ℝ} {S : SSFields} (h : NormalizedChartData b T K S)

include h

/-- The two first scalar derivatives restricted to the boundary have integrable
squares. Paper `e1a0fd5`, `equations.tex` line 1522. -/
theorem boundary_scalar_square_integrable :
    IntervalIntegrable (fun s => S.dupsi s s ^ 2) volume 0 T ∧
      IntervalIntegrable (fun s => S.dvpsi s s ^ 2) volume 0 T := by
  have hlocal : ∀ x ∈ Icc 0 T, ∃ a c, Icc a c ∈ 𝓝[Icc 0 T] x ∧
      IntegrableOn (fun s => S.dupsi s s ^ 2) (Icc a c) volume ∧
      IntegrableOn (fun s => S.dvpsi s s ^ 2) (Icc a c) volume := by
    intro x hx
    obtain ⟨a, c, ha, hac, hc, hg, hnhds⟩ := h.exists_boundary_triangle hx
    obtain ⟨F, G, hF, hG, hα, hβ, hU, hV⟩ := h.scalar_separated ha hac hc hg
    have hα' : BoundedVariationOn (fun s => S.dupsi s a) (uIcc a c) := by
      simpa [uIcc_of_le hac] using hα
    have hβ' : BoundedVariationOn (S.dvpsi c) (uIcc a c) := by
      simpa [uIcc_of_le hac] using hβ
    have hFi := chart_separated_square_integrable hα'
      (hF.comp (continuous_id.prodMk continuous_id))
    have hGi := chart_separated_square_integrable hβ'
      (hG.comp (continuous_id.prodMk continuous_id))
    have hiU : IntervalIntegrable (fun s => S.dupsi s s ^ 2) volume a c := by
      apply hFi.congr
      intro s hs
      rw [uIoc_of_le hac] at hs
      change (S.dupsi s a + F (s, s)) ^ 2 = S.dupsi s s ^ 2
      rw [hU (s, s) ⟨hs.1.le, le_rfl, hs.2⟩]
    have hiV : IntervalIntegrable (fun s => S.dvpsi s s ^ 2) volume a c := by
      apply hGi.congr
      intro s hs
      rw [uIoc_of_le hac] at hs
      change (S.dvpsi c s + G (s, s)) ^ 2 = S.dvpsi s s ^ 2
      rw [hV (s, s) ⟨hs.1.le, le_rfl, hs.2⟩]
    exact ⟨a, c, hnhds, (intervalIntegrable_iff_integrableOn_Icc_of_le hac).mp hiU,
      (intervalIntegrable_iff_integrableOn_Icc_of_le hac).mp hiV⟩
  have hu : LocallyIntegrableOn (fun s => S.dupsi s s ^ 2) (Icc 0 T) volume := by
    intro x hx
    obtain ⟨a, c, hnhds, hU, _⟩ := hlocal x hx
    exact ⟨Icc a c, hnhds, hU⟩
  have hv : LocallyIntegrableOn (fun s => S.dvpsi s s ^ 2) (Icc 0 T) volume := by
    intro x hx
    obtain ⟨a, c, hnhds, _, hV⟩ := hlocal x hx
    exact ⟨Icc a c, hnhds, hV⟩
  exact ⟨(intervalIntegrable_iff_integrableOn_Icc_of_le h.T_nonneg).mpr
    (hu.integrableOn_isCompact isCompact_Icc),
    (intervalIntegrable_iff_integrableOn_Icc_of_le h.T_nonneg).mpr
      (hv.integrableOn_isCompact isCompact_Icc)⟩

/-- The actual scalar boundary derivative has an integrable square. Paper
`e1a0fd5`, `eq:observability-energy-integral`, lines 1477–1480, 1522. -/
theorem boundary_psi_deriv_square_integrable :
    IntervalIntegrable (fun s => deriv (fun s => chartPsi S s s) s ^ 2) volume 0 T := by
  obtain ⟨hu, hv⟩ := h.boundary_scalar_square_integrable
  have hm := h.boundary_traces_ac.1.intervalIntegrable_deriv.def'.aestronglyMeasurable
  apply ((hu.add hv).const_mul 2).mono_fun' (hm.mul hm |>.congr (by
    filter_upwards with s
    simp only [pow_two, Pi.mul_apply]))
  rw [Filter.EventuallyLE, uIoc_of_le h.T_nonneg, ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [h.boundary_psi_ae_hasDerivAt] with s hs
  intro hsI
  rw [(hs ⟨hsI.1.le, hsI.2⟩).deriv, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith [sq_nonneg (S.dupsi s s - S.dvpsi s s)]

/-- The boundary radial amplitude itself is integrable. Paper `e1a0fd5`,
`eq:observability-volterra`, lines 1506–1510, 1524–1528. -/
theorem boundary_dvpsi_integrable : IntervalIntegrable (fun s => S.dvpsi s s) volume 0 T := by
  have hlocal : LocallyIntegrableOn (fun s => S.dvpsi s s) (Icc 0 T) volume := by
    intro x hx
    obtain ⟨a, c, ha, hac, hc, hg, hnhds⟩ := h.exists_boundary_triangle hx
    obtain ⟨F, G, hF, hG, hα, hβ, hU, hV⟩ := h.scalar_separated ha hac hc hg
    have hβ' : BoundedVariationOn (S.dvpsi c) (uIcc a c) := by
      simpa [uIcc_of_le hac] using hβ
    have hi := (hβ'.intervalIntegrable (μ := volume) (by rfl)).add
      ((hG.comp (continuous_id.prodMk continuous_id)).intervalIntegrable a c)
    have hie : IntervalIntegrable (fun s => S.dvpsi s s) volume a c := by
      apply hi.congr
      intro s hs
      rw [uIoc_of_le hac] at hs
      exact (hV (s, s) ⟨hs.1.le, le_rfl, hs.2⟩).symm
    exact ⟨Icc a c, hnhds, (intervalIntegrable_iff_integrableOn_Icc_of_le hac).mp hie⟩
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le h.T_nonneg).mpr
    (hlocal.integrableOn_isCompact isCompact_Icc)

end NormalizedChartData

end AcExtensionPrinciple

end
