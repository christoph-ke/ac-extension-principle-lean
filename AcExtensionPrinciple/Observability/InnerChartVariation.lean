module

public import AcExtensionPrinciple.Observability.InnerChartEquations

/-!
# The inner chart inherits uniform scalar BV bounds

Paper `e1a0fd5`, `equations.tex` line 1522 and lines 1460–1473, 1901.
Uniform scalar bounds come from the outer chart's characteristic BV fields.
-/

public section

namespace AcExtensionPrinciple.InnerBoundaryCoordinates

open Set MeasureTheory
open scoped ENNReal

variable {b T K a s₀ s₁ T' : ℝ} {S : SSFields} {h : NormalizedChartData b T K S}
variable {c : InnerCylinder h a s₀ s₁} (q : InnerBoundaryCoordinates c T')

/-- Uniform outgoing scalar-derivative variation is inherited under the
regular incoming extension. Paper `e1a0fd5`, lines 1441–1443 and 1460–1473. -/
theorem psi_t_variation (C : Set (ℝ × ℝ)) (hC : IsCompact C)
    (hsub : C ⊆ chartCylinder q.axisGraph T') :
    ∃ A : ℝ, ∀ s x y, x ≤ y → outSeg s x y ⊆ C →
      eVariationOn (q.fields.dvpsi s) (Icc x y) ≤ ENNReal.ofReal A := by
  let f := fun p : ℝ × ℝ => (q.U p.1, q.V p.2)
  have hf : Continuous f := (q.U.continuous.comp continuous_fst).prodMk
    (q.V.continuous.comp continuous_snd)
  have hK := hC.image hf
  have hKD : f '' C ⊆ chartCylinder h.g T := by
    rintro _ ⟨p, hp, rfl⟩
    exact q.source_mem (hsub hp)
  obtain ⟨A, hA⟩ := h.psi_t_variation (f '' C) hK hKD
  obtain ⟨M, _, hbound⟩ := h.inner_source_scalar_bound
  have hM : ∀ p ∈ f '' C, |S.dvpsi p.1 p.2| ≤ M := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hbound _ _ (q.source_mem (hsub hz)) (q.source_label_nonneg (hsub hz))).2
  obtain ⟨L, hL⟩ := hC.exists_bound_of_continuousOn
    (continuous_snd.continuousOn : ContinuousOn Prod.snd C)
  let R := |L|
  have hlabel : ∀ p ∈ C, p.2 ∈ Icc (-R) R := by
    intro p hp
    have hb : |p.2| ≤ L := by simpa only [Real.norm_eq_abs] using hL p hp
    have he : |p.2| ≤ R := hb.trans (le_abs_self L)
    exact abs_le.mp he
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (q.dV_continuous.continuousOn : ContinuousOn q.dV (Icc (-R) R))
  let B := ENNReal.ofReal M * eVariationOn q.dV (Icc (-R) R) +
    ENNReal.ofReal D * ENNReal.ofReal A
  have hJ := q.dV_variation (-R) R
  have hB : B ≠ ⊤ := by dsimp [B]; finiteness
  refine ⟨B.toReal, ?_⟩
  intro s x y hxy hseg
  have hsegJ : Icc x y ⊆ Icc (-R) R := fun z hz => hlabel (s, z)
    (hseg (show (s, z) ∈ outSeg s x y from ⟨by simp, hz⟩))
  have hvar : eVariationOn (fun z => S.dvpsi (q.U s) (q.V z)) (Icc x y) ≤
      ENNReal.ofReal A := by
    rw [variation_comp_Icc (S.dvpsi (q.U s)) q.V hxy
      (q.V.monotone.monotoneOn _) q.V.continuous.continuousOn]
    exact hA (q.U s) (q.V x) (q.V y) (q.V.monotone hxy) (q.source_outSeg_image hseg)
  have he := variation_mul_le (fun z => S.dvpsi (q.U s) (q.V z)) q.dV (Icc x y)
    (fun z hz => by
      have hm : f (s, z) ∈ f '' C :=
        ⟨(s, z), hseg (show (s, z) ∈ outSeg s x y from ⟨by simp, hz⟩), rfl⟩
      simpa only [Real.norm_eq_abs] using hM (f (s, z)) hm)
    (fun z hz => by simpa only [Real.norm_eq_abs] using hD z (hsegJ hz))
  rw [ENNReal.ofReal_toReal hB]
  simp only [fields, PropA4.separatePullback]
  change eVariationOn (fun z => S.dvpsi (q.U s) (q.V z) * q.dV z) (Icc x y) ≤ B
  apply he.trans
  dsimp only [B]
  gcongr
  exact eVariationOn.mono _ hsegJ

/-- Uniform incoming scalar-derivative variation is inherited under the
regular inverse boundary clock. Paper `e1a0fd5`, lines 1441–1443 and 1460–1473. -/
theorem psi_s_variation (C : Set (ℝ × ℝ)) (hC : IsCompact C)
    (hsub : C ⊆ chartCylinder q.axisGraph T') :
    ∃ A : ℝ, ∀ t x y, x ≤ y → inSeg t x y ⊆ C →
      eVariationOn (fun s => q.fields.dupsi s t) (Icc x y) ≤ ENNReal.ofReal A := by
  let f := fun p : ℝ × ℝ => (q.U p.1, q.V p.2)
  have hf : Continuous f := (q.U.continuous.comp continuous_fst).prodMk
    (q.V.continuous.comp continuous_snd)
  have hK := hC.image hf
  have hKD : f '' C ⊆ chartCylinder h.g T := by
    rintro _ ⟨p, hp, rfl⟩
    exact q.source_mem (hsub hp)
  obtain ⟨A, hA⟩ := h.psi_s_variation (f '' C) hK hKD
  obtain ⟨M, _, hbound⟩ := h.inner_source_scalar_bound
  have hM : ∀ p ∈ f '' C, |S.dupsi p.1 p.2| ≤ M := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hbound _ _ (q.source_mem (hsub hz)) (q.source_label_nonneg (hsub hz))).1
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (q.dU_continuous.continuousOn : ContinuousOn q.dU (Icc 0 T'))
  let B := ENNReal.ofReal M * eVariationOn q.dU (Icc 0 T') +
    ENNReal.ofReal D * ENNReal.ofReal A
  have hJ := q.dU_variation
  have hB : B ≠ ⊤ := by dsimp [B]; finiteness
  refine ⟨B.toReal, ?_⟩
  intro t x y hxy hseg
  have hsegJ : Icc x y ⊆ Icc 0 T' := by
    intro z hz
    have hp := hsub (hseg (show (z, t) ∈ inSeg t x y from ⟨hz, by simp⟩))
    exact ⟨hp.1, hp.2.1⟩
  have hvar : eVariationOn (fun z => S.dupsi (q.U z) (q.V t)) (Icc x y) ≤
      ENNReal.ofReal A := by
    rw [variation_comp_Icc (fun u => S.dupsi u (q.V t)) q.U hxy
      (q.U.monotone.monotoneOn _) q.U.continuous.continuousOn]
    exact hA (q.V t) (q.U x) (q.U y) (q.U.monotone hxy) (q.source_inSeg_image hseg)
  have he := variation_mul_le (fun z => S.dupsi (q.U z) (q.V t)) q.dU (Icc x y)
    (fun z hz => by
      have hm : f (z, t) ∈ f '' C :=
        ⟨(z, t), hseg (show (z, t) ∈ inSeg t x y from ⟨hz, by simp⟩), rfl⟩
      simpa only [Real.norm_eq_abs] using hM (f (z, t)) hm)
    (fun z hz => by simpa only [Real.norm_eq_abs] using hD z (hsegJ hz))
  rw [ENNReal.ofReal_toReal hB]
  simp only [fields, PropA4.separatePullback]
  change eVariationOn (fun z => S.dupsi (q.U z) (q.V t) * q.dU z) (Icc x y) ≤ B
  apply he.trans
  dsimp only [B]
  gcongr
  exact eVariationOn.mono _ hsegJ


end AcExtensionPrinciple.InnerBoundaryCoordinates

end
