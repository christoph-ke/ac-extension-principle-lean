module

public import AcExtensionPrinciple.Observability.InnerChartCoordinates
public import AcExtensionPrinciple.Observability.InnerChartBounds

/-!
# Geometry and characteristic segments under the inner coordinates

Paper `e1a0fd5`, `equations.tex` lines 1877–1907 and 1460–1473.
The axis graph is transported through the two distinct inverse maps.
-/

public section

namespace AcExtensionPrinciple.InnerBoundaryCoordinates

open Set MeasureTheory

variable {b T K a s₀ s₁ T' : ℝ} {S : SSFields} {h : NormalizedChartData b T K S}
variable {c : InnerCylinder h a s₀ s₁} (q : InnerBoundaryCoordinates c T')

/-- The inner chart axis, including its earlier incoming labels. Paper
`e1a0fd5`, lines 1460–1473 and 1901. -/
@[expose] noncomputable def axisGraph (x : ℝ) : ℝ := q.V.symm (h.g (q.U x))

/-- The actual fields pulled back by the separate inverse coordinates.
Paper `e1a0fd5`, lines 1460–1473 and 1877–1907. -/
@[expose] noncomputable def fields : SSFields :=
  PropA4.separatePullback S q.U q.V q.dU q.dV

/-- The inverse inner clock stays on its old-time interval. Paper
`e1a0fd5`, lines 1877–1907. -/
theorem U_mem {x : ℝ} (hx : x ∈ Icc 0 T') : q.U x ∈ Icc s₀ s₁ := by
  constructor
  · simpa only [q.U_initial] using q.U.monotone hx.1
  · simpa only [q.U_terminal] using q.U.monotone hx.2

/-- The inner clock recovers the new boundary time exactly. Paper
`e1a0fd5`, `eq:observability-inner-boundary-measure`, lines 1877–1887. -/
theorem clock_inverse_apply {x : ℝ} (hx : x ∈ Icc 0 T') : c.clock (q.U x) = x := by
  simpa only [q.U.symm_apply_apply] using (q.clock (q.U x) (q.U_mem hx)).symm

/-- Every inner chart point is a point of the outer chart. Paper
`e1a0fd5`, lines 1877–1907. -/
theorem source_mem {x y : ℝ} (hp : (x, y) ∈ chartCylinder q.axisGraph T') :
    (q.U x, q.V y) ∈ chartCylinder h.g T := by
  have hm := (c.source_mem (q.U_mem ⟨hp.1, hp.2.1⟩)).1
  have hlo : h.g (q.U x) ≤ q.V y := by
    simpa only [axisGraph, q.V.apply_symm_apply] using q.V.monotone hp.2.2.1
  have hhi : q.V y ≤ c.v (q.U x) :=
    (q.V.monotone hp.2.2.2).trans_eq (q.boundary x ⟨hp.1, hp.2.1⟩)
  exact ⟨hm.1, hm.2.1, hlo, hhi.trans hm.2.2.2⟩

/-- All mapped incoming labels are nonnegative, including those using
the affine earlier-label extension. Paper `e1a0fd5`, lines 1692–1698
and 1877–1907. -/
theorem source_label_nonneg {x y : ℝ} (hp : (x, y) ∈ chartCylinder q.axisGraph T') :
    0 ≤ q.V y := by
  have hs := q.U_mem ⟨hp.1, hp.2.1⟩
  have hm := q.source_mem hp
  exact (PropA4.axis_label_nonneg h ⟨hm.1, hm.2.1⟩
    (c.late.trans hs.1)).trans hm.2.2.1

/-- The axis remains continuous and monotone on the inner time interval.
Paper `e1a0fd5`, lines 1460–1473 and 1901. -/
theorem axisGraph_regular : Continuous q.axisGraph ∧ MonotoneOn q.axisGraph (Icc 0 T') := by
  refine ⟨q.V.symm.continuous.comp (h.continuous_g.comp q.U.continuous), ?_⟩
  intro x hx y hy hxy
  have hs := (c.source_mem (q.U_mem hx)).1
  have ht := (c.source_mem (q.U_mem hy)).1
  exact q.V.symm.monotone (h.monotone_g ⟨hs.1, hs.2.1⟩ ⟨ht.1, ht.2.1⟩
    (q.U.monotone hxy))

/-- The transported axis is strictly inside the new boundary diagonal.
Paper `e1a0fd5`, lines 1460–1473 and 1901. -/
theorem axis_before_boundary {x : ℝ} (hx : x ∈ Icc 0 T') : q.axisGraph x < x := by
  have he := (c.points (q.U x) (q.U_mem hx)).1
  rw [← q.boundary x hx] at he
  simpa only [axisGraph, q.V.symm_apply_apply] using q.V.symm.strictMono he

/-- Both expansions and the radius have the required inner boundary
normalization. Paper `e1a0fd5`, lines 1877–1887 and 1901. -/
theorem boundary_gauge {x : ℝ} (hx : x ∈ Icc 0 T') :
    q.fields.r x x = a ∧ q.fields.nu x x = -1 ∧ q.fields.lam x x = 1 := by
  apply PropA4.separatePullback_boundary_gauge
  · simpa only [q.boundary x hx] using (c.points (q.U x) (q.U_mem hx)).2.2
  · simpa only [q.boundary x hx] using (h.signs _ _ (c.source_mem (q.U_mem hx)).1).2.1
  · simpa only [q.boundary x hx] using (h.signs _ _ (c.source_mem (q.U_mem hx)).1).1
  · simpa only [q.boundary x hx] using q.U_jacobian x hx
  · simpa only [q.boundary x hx] using q.V_jacobian x hx

/-- Incoming Jacobians cancel and the entry comparison keeps exactly K.
Paper `e1a0fd5`, line 1901 and `eq:observability-boundary-gauge`. -/
theorem incoming_ratio {x y : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x) (hxT : x ≤ T')
    (hp : (x, y) ∈ chartCylinder q.axisGraph T') :
    q.fields.lam y y / q.fields.lam x y ≤ K := by
  rw [fields, PropA4.separatePullback_incoming_ratio S q.U q.V q.dU q.dV x y
    (q.dV_positive y).ne']
  have hyI : y ∈ Icc 0 T' := ⟨hy, hyx.trans hxT⟩
  have hm := c.source_mem (q.U_mem hyI)
  have hp' : (y, y) ∈ chartCylinder q.axisGraph T' :=
    ⟨hy, hyx.trans hxT, (q.axis_before_boundary hyI).le, le_rfl⟩
  apply h.inner_entry_ratio (q.source_label_nonneg hp')
  · simpa only [q.boundary y hyI] using hm
  · exact q.source_mem hp

/-- The inner arrival time is at most Ka in its own clock, with the
same K as the outer chart. Paper `e1a0fd5`, line 1901. -/
theorem axis_reached {y : ℝ} (hy : y ∈ Icc 0 T') (hwait : y + K * a ≤ T') :
    ∃ x ∈ Icc y (y + K * a), q.axisGraph x = y := by
  have hKa : 0 ≤ K * a := mul_nonneg (zero_lt_one.trans_le h.K_ge_one).le c.a_pos.le
  have hzI : y + K * a ∈ Icc 0 T' := ⟨by linarith [hy.1], hwait⟩
  obtain ⟨z, hz, he⟩ := c.axis_reached_of_clock (q.U_mem hy) (q.U_mem hzI)
    (q.U.monotone (by linarith)) (by
      rw [q.clock_inverse_apply hzI, q.clock_inverse_apply hy]
      linarith)
  refine ⟨q.U.symm z, ⟨?_, ?_⟩, ?_⟩
  · simpa only [q.U.symm_apply_apply] using q.U.symm.monotone hz.1
  · simpa only [q.U.symm_apply_apply] using q.U.symm.monotone hz.2
  · simp only [axisGraph, q.U.apply_symm_apply, he, ← q.boundary y hy,
      q.V.symm_apply_apply]

/-- The mass ratio is unchanged by both independent coordinate maps.
Paper `e1a0fd5`, lines 1877–1879 and 1901. -/
@[simp] theorem fields_mu (x y : ℝ) : q.fields.mu x y = S.mu (q.U x) (q.V y) := rfl

/-- The mixed radius coefficient acquires both Jacobians. Paper
`e1a0fd5`, `eq:observability-chart-equations`, lines 1484–1492 and 1901. -/
theorem fields_radiusCoeff (x y : ℝ) :
    q.fields.radiusCoeff x y = S.radiusCoeff (q.U x) (q.V y) * (q.dU x * q.dV y) := by
  simp only [SSFields.radiusCoeff, q.fields_mu]
  simp only [fields, PropA4.separatePullback]
  ring

/-- Outgoing scalar amplitude scales by the incoming Jacobian. Paper
`e1a0fd5`, lines 1484–1492 and 1901. -/
theorem fields_theta (x y : ℝ) :
    q.fields.theta x y = S.theta (q.U x) (q.V y) * q.dV y := by
  simp only [SSFields.theta, fields, PropA4.separatePullback]
  ring

/-- Incoming scalar amplitude scales by the clock Jacobian. Paper
`e1a0fd5`, lines 1484–1492 and 1901. -/
theorem fields_zeta (x y : ℝ) :
    q.fields.zeta x y = S.zeta (q.U x) (q.V y) * q.dU x := by
  simp only [SSFields.zeta, fields, PropA4.separatePullback]
  ring

/-- An outgoing characteristic segment has exactly its old-coordinate
image. Paper `e1a0fd5`, lines 1460–1473 and 1901. -/
theorem source_outSeg_image {C : Set (ℝ × ℝ)} {x l r : ℝ} (hseg : outSeg x l r ⊆ C) :
    outSeg (q.U x) (q.V l) (q.V r) ⊆ (fun p : ℝ × ℝ => (q.U p.1, q.V p.2)) '' C := by
  rintro ⟨u, v⟩ ⟨hu, hv⟩
  simp only [mem_singleton_iff] at hu
  subst u
  refine ⟨(x, q.V.symm v), hseg ⟨by simp, ?_, ?_⟩, ?_⟩
  · simpa only [q.V.symm_apply_apply] using q.V.symm.monotone hv.1
  · simpa only [q.V.symm_apply_apply] using q.V.symm.monotone hv.2
  · simp only [q.V.apply_symm_apply]

/-- An incoming characteristic segment has exactly its old-coordinate
image. Paper `e1a0fd5`, lines 1460–1473 and 1901. -/
theorem source_inSeg_image {C : Set (ℝ × ℝ)} {y l r : ℝ} (hseg : inSeg y l r ⊆ C) :
    inSeg (q.V y) (q.U l) (q.U r) ⊆ (fun p : ℝ × ℝ => (q.U p.1, q.V p.2)) '' C := by
  rintro ⟨u, v⟩ ⟨hu, hv⟩
  simp only [mem_singleton_iff] at hv
  subst v
  refine ⟨(q.U.symm u, y), hseg ⟨⟨?_, ?_⟩, by simp⟩, ?_⟩
  · simpa only [q.U.symm_apply_apply] using q.U.symm.monotone hu.1
  · simpa only [q.U.symm_apply_apply] using q.U.symm.monotone hu.2
  · simp only [q.U.apply_symm_apply]

/-- Old outgoing segments stay in the old chart domain. Paper `e1a0fd5`,
lines 1460–1473 and 1901. -/
theorem source_outSeg_subset {x l r : ℝ} (hseg : outSeg x l r ⊆ chartCylinder q.axisGraph T') :
    outSeg (q.U x) (q.V l) (q.V r) ⊆ chartCylinder h.g T := by
  intro p hp
  obtain ⟨z, hz, rfl⟩ := q.source_outSeg_image hseg hp
  exact q.source_mem hz

/-- Old incoming segments stay in the old chart domain. Paper `e1a0fd5`,
lines 1460–1473 and 1901. -/
theorem source_inSeg_subset {y l r : ℝ} (hseg : inSeg y l r ⊆ chartCylinder q.axisGraph T') :
    inSeg (q.V y) (q.U l) (q.U r) ⊆ chartCylinder h.g T := by
  intro p hp
  obtain ⟨z, hz, rfl⟩ := q.source_inSeg_image hseg hp
  exact q.source_mem hz

/-- Old outgoing segments preserve positive radius. Paper `e1a0fd5`,
`eq:observability-chart-equations`, lines 1484–1492 and 1901. -/
theorem source_outSeg_interior {x l r : ℝ}
    (hseg : outSeg x l r ⊆ chartInterior (chartCylinder q.axisGraph T') q.fields) :
    outSeg (q.U x) (q.V l) (q.V r) ⊆ chartInterior (chartCylinder h.g T) S := by
  intro p hp
  obtain ⟨z, hz, rfl⟩ := q.source_outSeg_image hseg hp
  exact ⟨q.source_mem hz.1, hz.2⟩

/-- Old incoming segments preserve positive radius. Paper `e1a0fd5`,
`eq:observability-chart-equations`, lines 1484–1492 and 1901. -/
theorem source_inSeg_interior {y l r : ℝ}
    (hseg : inSeg y l r ⊆ chartInterior (chartCylinder q.axisGraph T') q.fields) :
    inSeg (q.V y) (q.U l) (q.U r) ⊆ chartInterior (chartCylinder h.g T) S := by
  intro p hp
  obtain ⟨z, hz, rfl⟩ := q.source_inSeg_image hseg hp
  exact ⟨q.source_mem hz.1, hz.2⟩

/-- The clock inverse supplies all primitive substitution hypotheses.
Paper `e1a0fd5`, lines 1460–1473 and 1877–1887. -/
theorem gaugeU (x y : ℝ) : GaugeSegment q.U q.dU x y :=
  GaugeSegment.of_hasDerivAt (fun z _ => q.U_derivative z) (fun z _ => (q.dU_positive z).le)

/-- The incoming inverse, including its affine extension, supplies all
primitive substitution hypotheses. Paper `e1a0fd5`, lines 1460–1473 and 1901. -/
theorem gaugeV (x y : ℝ) : GaugeSegment q.V q.dV x y :=
  GaugeSegment.of_hasDerivAt (fun z _ => q.V_derivative z) (fun z _ => (q.dV_positive z).le)

end AcExtensionPrinciple.InnerBoundaryCoordinates

end
