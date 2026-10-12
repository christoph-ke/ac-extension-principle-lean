module

public import AcExtensionPrinciple.Observability.FromSolutionChartAlgebra

/-!
# Characteristic segments under the two normalized coordinates

Paper `e1a0fd5`, `equations.tex` lines 1460–1473.
Increasing inverse coordinates preserve each closed characteristic segment,
including its endpoints. Positive radius identifies the off-axis region.
-/

public section

namespace AcExtensionPrinciple.NormalizedBoundaryCoordinates

open Set MeasureTheory

variable {ui b a₀ a₁ a d T : ℝ} {S : SSFields} {c : DecayCylinder ui S b a₀ a₁}
variable (q : NormalizedBoundaryCoordinates c a d T)

/-- The coordinate image of the normalized outgoing segment contains
exactly its corresponding source segment. Paper `e1a0fd5`, lines 1460–1473. -/
theorem source_outSeg_image {C : Set (ℝ × ℝ)} {s x y : ℝ} (hseg : outSeg s x y ⊆ C) :
    outSeg (q.U s) (q.V x) (q.V y) ⊆ (fun p : ℝ × ℝ => (q.U p.1, q.V p.2)) '' C := by
  rintro ⟨u, v⟩ ⟨hu, hv⟩
  simp only [mem_singleton_iff] at hu
  subst u
  refine ⟨(s, q.V.symm v), hseg ⟨by simp, ?_, ?_⟩, ?_⟩
  · simpa only [q.V.symm_apply_apply] using q.V.symm.monotone hv.1
  · simpa only [q.V.symm_apply_apply] using q.V.symm.monotone hv.2
  · simp only [q.V.apply_symm_apply]

/-- The coordinate image of the normalized incoming segment contains
exactly its corresponding source segment. Paper `e1a0fd5`, lines 1460–1473. -/
theorem source_inSeg_image {C : Set (ℝ × ℝ)} {t x y : ℝ} (hseg : inSeg t x y ⊆ C) :
    inSeg (q.V t) (q.U x) (q.U y) ⊆ (fun p : ℝ × ℝ => (q.U p.1, q.V p.2)) '' C := by
  rintro ⟨u, v⟩ ⟨hu, hv⟩
  simp only [mem_singleton_iff] at hv
  subst v
  refine ⟨(q.U.symm u, t), hseg ⟨⟨?_, ?_⟩, by simp⟩, ?_⟩
  · simpa only [q.U.symm_apply_apply] using q.U.symm.monotone hu.1
  · simpa only [q.U.symm_apply_apply] using q.U.symm.monotone hu.2
  · simp only [q.U.apply_symm_apply]

/-- Positive normalized radius maps to a source point strictly off the
axis. Paper `e1a0fd5`, lines 1460–1473 and 1484–1492. -/
theorem source_interior_mem (h : StandingFull ui S) (ha : a₀ ≤ a) (hd : d ≤ a₁)
    {s t : ℝ} (hp : (s, t) ∈ chartInterior (chartCylinder q.axisGraph T) q.fields) :
    (q.U s, q.V t) ∈ offAxis (pastTriangle ui) := by
  have hm := q.source_mem ha hd hp.1
  refine ⟨hm, ?_⟩
  change q.U s ≠ q.V t
  intro he
  have hr := (h.regularCenter.localBV.axis_values (q.U s)
    ⟨hm.1, hm.2.1, le_rfl, hm.2.1.le⟩).1
  have hpos : 0 < S.r (q.U s) (q.V t) := hp.2
  rw [← he, hr] at hpos
  exact lt_irrefl 0 hpos

/-- Source outgoing primitives can be used on the whole mapped segment.
Paper `e1a0fd5`, lines 1460–1473. -/
theorem source_outSeg_subset (ha : a₀ ≤ a) (hd : d ≤ a₁) {s x y : ℝ}
    (hseg : outSeg s x y ⊆ chartCylinder q.axisGraph T) :
    outSeg (q.U s) (q.V x) (q.V y) ⊆ pastTriangle ui := by
  intro p hp
  obtain ⟨z, hz, rfl⟩ := q.source_outSeg_image hseg hp
  exact q.source_mem ha hd hz

/-- Source incoming primitives can be used on the whole mapped segment.
Paper `e1a0fd5`, lines 1460–1473. -/
theorem source_inSeg_subset (ha : a₀ ≤ a) (hd : d ≤ a₁) {t x y : ℝ}
    (hseg : inSeg t x y ⊆ chartCylinder q.axisGraph T) :
    inSeg (q.V t) (q.U x) (q.U y) ⊆ pastTriangle ui := by
  intro p hp
  obtain ⟨z, hz, rfl⟩ := q.source_inSeg_image hseg hp
  exact q.source_mem ha hd hz

/-- The outgoing off-axis primitive domain is preserved. Paper
`e1a0fd5`, lines 1460–1473 and 1484–1492. -/
theorem source_outSeg_interior (h : StandingFull ui S) (ha : a₀ ≤ a) (hd : d ≤ a₁)
    {s x y : ℝ} (hseg : outSeg s x y ⊆ chartInterior (chartCylinder q.axisGraph T) q.fields) :
    outSeg (q.U s) (q.V x) (q.V y) ⊆ offAxis (pastTriangle ui) := by
  intro p hp
  obtain ⟨z, hz, rfl⟩ := q.source_outSeg_image hseg hp
  exact q.source_interior_mem h ha hd hz

/-- The incoming off-axis primitive domain is preserved. Paper
`e1a0fd5`, lines 1460–1473 and 1484–1492. -/
theorem source_inSeg_interior (h : StandingFull ui S) (ha : a₀ ≤ a) (hd : d ≤ a₁)
    {t x y : ℝ} (hseg : inSeg t x y ⊆ chartInterior (chartCylinder q.axisGraph T) q.fields) :
    inSeg (q.V t) (q.U x) (q.U y) ⊆ offAxis (pastTriangle ui) := by
  intro p hp
  obtain ⟨z, hz, rfl⟩ := q.source_inSeg_image hseg hp
  exact q.source_interior_mem h ha hd hz

/-- Outgoing inverse coordinates satisfy every substitution premise.
Paper `e1a0fd5`, lines 1460–1473. -/
theorem gaugeU (x y : ℝ) : GaugeSegment q.U q.dU x y :=
  GaugeSegment.of_hasDerivAt (fun s _ => q.U_derivative s) (fun s _ => (q.dU_positive s).le)

/-- Incoming inverse coordinates satisfy every substitution premise.
Paper `e1a0fd5`, lines 1460–1473. -/
theorem gaugeV (x y : ℝ) : GaugeSegment q.V q.dV x y :=
  GaugeSegment.of_hasDerivAt (fun t _ => q.V_derivative t) (fun t _ => (q.dV_positive t).le)

end AcExtensionPrinciple.NormalizedBoundaryCoordinates

end
