module

public import AcExtensionPrinciple.Observability.PropA4VolterraDomination

/-!
# The invariant exterior domain for the weighted operator

Paper `e1a0fd5`, lines 1730–1747. The domain is understood as a subset
of the normalized chart, and every characteristic integration triangle
stays inside it.
-/

public section

namespace AcExtensionPrinciple
namespace PropA4

open Set

/-- The paper's late exterior domain within the normalized chart.
Paper `e1a0fd5`, lines 1730–1733. -/
@[expose] def exteriorDomain {b T K : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (P : ℝ) : Set (ℝ × ℝ) :=
  {p | p ∈ chartCylinder h.g T ∧ K * b ≤ p.2 ∧ 32 * P ≤ S.r p.1 p.2}

/-- A positive exterior cutoff excludes the axis.
Paper `e1a0fd5`, lines 1730–1738. -/
theorem exteriorDomain_interior {b T K P : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P) {p : ℝ × ℝ}
    (hp : p ∈ exteriorDomain h P) : p ∈ chartInterior (chartCylinder h.g T) S :=
  ⟨hp.1, by linarith [hp.2.2]⟩

/-- Every integration point belongs to the same exterior domain.
Paper `e1a0fd5`, lines 1734–1738. -/
theorem exteriorDomain_triangle {b T K P : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P) {p : ℝ × ℝ}
    (hp : p ∈ exteriorDomain h P) : chartTriangle p.2 p.1 ⊆ exteriorDomain h P := by
  have hKb : 0 ≤ K * b := mul_nonneg (by linarith [h.K_ge_one]) h.b_pos.le
  have ht := hKb.trans hp.2.1
  have hpoint := exteriorDomain_interior h hP hp
  have htri := h.volterra_triangle_subset ht hpoint
  intro q hq
  have hr := h.volterra_radius_order ht hpoint ⟨hq.1.trans hq.2.1, hq.2.2⟩
    ⟨hq.1, hq.2.1⟩
  exact ⟨(htri hq).1, hp.2.1.trans hq.1, hp.2.2.trans (hr.1.trans hr.2)⟩

/-- The exterior domain is closed, using continuity of radius only
within the chart. Paper `e1a0fd5`, lines 1730–1747. -/
theorem isClosed_exteriorDomain {b T K P : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) : IsClosed (exteriorDomain h P) := by
  have hC : IsClosed (chartCylinder h.g T) := by
    exact (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_fst continuous_const).inter
        ((isClosed_le (h.continuous_g.comp continuous_fst) continuous_snd).inter
          (isClosed_le continuous_snd continuous_fst)))
  have hR : IsClosed {p : ℝ × ℝ | p ∈ chartCylinder h.g T ∧ 32 * P ≤ S.r p.1 p.2} :=
    hC.isClosed_le continuousOn_const h.continuous_r
  have ht : IsClosed {p : ℝ × ℝ | K * b ≤ p.2} :=
    isClosed_le continuous_const continuous_snd
  convert hR.inter ht using 1
  ext p
  simp only [exteriorDomain, mem_ofPred_eq, mem_inter_iff]
  tauto

/-- The late exterior domain is compact, including when it is empty.
Paper `e1a0fd5`, lines 1730–1747. -/
theorem isCompact_exteriorDomain {b T K P : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) : IsCompact (exteriorDomain h P) := by
  apply ((isCompact_Icc : IsCompact (Icc (K * b) T)).prod
    (isCompact_Icc : IsCompact (Icc (K * b) T))).of_isClosed_subset (isClosed_exteriorDomain h)
  intro p hp
  exact ⟨⟨hp.2.1.trans hp.1.2.2.2, hp.1.2.1⟩,
    ⟨hp.2.1, hp.1.2.2.2.trans hp.1.2.1⟩⟩

/-- Continuous exterior inputs admit a continuous extension to the
coordinate plane. The operator only uses their original exterior
values. Paper `e1a0fd5`, lines 1730–1747. -/
theorem exteriorDomain_continuous_extension {b T K P : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) {F : ℝ × ℝ → ℝ}
    (hF : ContinuousOn F (exteriorDomain h P)) :
    ∃ G : ℝ × ℝ → ℝ, Continuous G ∧ ∀ p ∈ exteriorDomain h P, G p = F p := by
  obtain ⟨G, hG⟩ := (⟨_, hF.domRestrict⟩ : C(exteriorDomain h P, ℝ)).exists_restrict_eq
    (isClosed_exteriorDomain h)
  refine ⟨G, G.continuous, fun p hp => ?_⟩
  exact congrArg (fun A : C(exteriorDomain h P, ℝ) => A ⟨p, hp⟩) hG

/-- The concrete Volterra operator preserves exterior continuity.
Paper `e1a0fd5`, lines 1742–1755. -/
theorem exterior_volterra_continuous {b T K P : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P) {F : ℝ × ℝ → ℝ}
    (hF : ContinuousOn F (exteriorDomain h P)) :
    ContinuousOn (fun p => triangleVolterra (fun p => chartPotential S p.1 p.2) F p.1 p.2)
      (exteriorDomain h P) := by
  have hPc := continuous_potential_on (C := exteriorDomain h P) h
    (fun p hp => exteriorDomain_interior h hP hp)
  obtain ⟨Q, hQ, hQeq⟩ := exteriorDomain_continuous_extension h hPc
  obtain ⟨G, hG, hGeq⟩ := exteriorDomain_continuous_extension h hF
  apply (continuous_triangleVolterra hQ hG).continuousOn.congr
  intro p hp
  have htri := exteriorDomain_triangle h hP hp
  unfold triangleVolterra
  apply intervalIntegral.integral_congr
  intro σ hσ
  rw [uIcc_of_le hp.1.2.2.2] at hσ
  apply intervalIntegral.integral_congr
  intro z hz
  rw [uIcc_of_le hσ.1] at hz
  have hmem := htri (show (σ, z) ∈ chartTriangle p.2 p.1 from ⟨hz.1, hz.2, hσ.2⟩)
  dsimp only
  rw [hQeq _ hmem, hGeq _ hmem]

/-- The weighted bound is uniform on the entire invariant exterior
domain. Input continuity and boundedness are the premises defining
the weighted operator space. Paper `e1a0fd5`, lines 1742–1747. -/
theorem exterior_volterra_weighted_bound {b T K P q B : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P)
    (hq : q < 1) (hB : 0 ≤ B) {F : ℝ × ℝ → ℝ}
    (hF : ContinuousOn F (exteriorDomain h P))
    (hbound : ∀ p ∈ exteriorDomain h P, |F p| ≤ B * S.r p.1 p.2 ^ q)
    {p : ℝ × ℝ} (hp : p ∈ exteriorDomain h P) :
    |triangleVolterra (fun p => chartPotential S p.1 p.2) F p.1 p.2| ≤
      B * (1 / (4 * (2 - q) * (1 - q))) * S.r p.1 p.2 ^ q := by
  have hKb : 0 ≤ K * b := mul_nonneg (by linarith [h.K_ge_one]) h.b_pos.le
  have htri := exteriorDomain_triangle h hP hp
  exact volterra_weighted_bound h hP (hKb.trans hp.2.1)
    (exteriorDomain_interior h hP hp) hp.2.2 hmass hq hB (hF.mono htri)
    (fun z hz => hbound z (htri hz))

/-- The actual operator contracts the weighted supremum bound by
`1/[4(2-q)(1-q)]`. Paper `e1a0fd5`, lines 1742–1747. -/
theorem exterior_volterra_weighted_norm_bound {b T K P q B : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P)
    (hq : q < 1) (hB : 0 ≤ B) {F : ℝ × ℝ → ℝ}
    (hF : ContinuousOn F (exteriorDomain h P))
    (hbound : ∀ p ∈ exteriorDomain h P, |F p| ≤ B * S.r p.1 p.2 ^ q)
    {p : ℝ × ℝ} (hp : p ∈ exteriorDomain h P) :
    |triangleVolterra (fun p => chartPotential S p.1 p.2) F p.1 p.2| /
        S.r p.1 p.2 ^ q ≤ B * (1 / (4 * (2 - q) * (1 - q))) := by
  have hr := (exteriorDomain_interior h hP hp).2
  exact (div_le_iff₀ (Real.rpow_pos_of_pos hr q)).mpr
    (exterior_volterra_weighted_bound h hP hmass hq hB hF hbound hp)

end PropA4
end AcExtensionPrinciple

end
