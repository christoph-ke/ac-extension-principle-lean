module

public import AcExtensionPrinciple.Observability.FromSolutionCoordinates

/-!
# Source geometry in the constructed normalized chart

Paper `e1a0fd5`, `equations.tex` lines 742–749 and 1460–1473.
The axis is the image of u=v under the two different coordinate maps.
The gap, incoming ratio and arrival-time bounds retain the same K.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory

namespace NormalizedBoundaryCoordinates

variable {ui b a₀ a₁ a d T : ℝ} {S : SSFields} {c : DecayCylinder ui S b a₀ a₁}
variable (q : NormalizedBoundaryCoordinates c a d T)

/-- The regular axis graph in the normalized chart. Paper `e1a0fd5`,
lines 1460–1473. -/
@[expose] noncomputable def axisGraph (s : ℝ) : ℝ := q.V.symm (q.U s)

/-- The actual source fields in the normalized chart. Scalar translation
is handled uniformly by Prop A.1. Paper `e1a0fd5`, lines 1460–1475. -/
@[expose] noncomputable def fields : SSFields :=
  S.normalizedPullback q.U q.V q.dU q.dV 0

/-- The inverse outgoing coordinate stays on the physical interval.
Paper `e1a0fd5`, lines 1460–1473. -/
theorem U_mem {s : ℝ} (hs : s ∈ Icc 0 T) : q.U s ∈ Icc a d := by
  constructor
  · simpa only [q.U_initial] using q.U.monotone hs.1
  · simpa only [q.U_terminal] using q.U.monotone hs.2

/-- Undoing the inverse clock recovers normalized boundary time exactly.
Paper `e1a0fd5`, lines 1460 and 1926–1927. -/
theorem clock_inverse_apply {s : ℝ} (hs : s ∈ Icc 0 T) :
    c.tau (q.U s) - c.tau a = s := by
  have he := q.clock (q.U s) (q.U_mem hs)
  simpa only [q.U.symm_apply_apply, normalizedCylinderClock] using he.symm

/-- Every normalized cylinder point maps into the original source
triangle. Paper `e1a0fd5`, lines 1460–1473. -/
theorem source_mem (ha : a₀ ≤ a) (hd : d ≤ a₁) {s t : ℝ}
    (hp : (s, t) ∈ chartCylinder q.axisGraph T) :
    (q.U s, q.V t) ∈ pastTriangle ui := by
  have hs := Icc_subset_Icc ha hd (q.U_mem ⟨hp.1, hp.2.1⟩)
  have hlow : q.U s ≤ q.V t := by
    simpa only [axisGraph, q.V.apply_symm_apply] using q.V.monotone hp.2.2.1
  have hhigh : q.V t ≤ c.v (q.U s) :=
    (q.V.monotone hp.2.2.2).trans_eq (q.boundary s ⟨hp.1, hp.2.1⟩)
  exact ⟨c.initial_le.trans hs.1, hs.2.trans_lt c.terminal_negative,
    hlow, hhigh.trans (c.points _ hs).2.1⟩

/-- The normalized axis is continuous and increasing globally.
Paper `e1a0fd5`, lines 1460–1473. -/
theorem axisGraph_continuous_monotone : Continuous q.axisGraph ∧ Monotone q.axisGraph :=
  ⟨q.V.symm.continuous.comp q.U.continuous, q.V.symm.monotone.comp q.U.monotone⟩

/-- The regular axis lies strictly inside the radius-b boundary. Paper
`e1a0fd5`, lines 1460–1465. -/
theorem axis_before_boundary (ha : a₀ ≤ a) (hd : d ≤ a₁) {s : ℝ}
    (hs : s ∈ Icc 0 T) : q.axisGraph s < s := by
  have hm := Icc_subset_Icc ha hd (q.U_mem hs)
  have hv := (c.points (q.U s) hm).1
  rw [← q.boundary s hs] at hv
  simpa only [axisGraph, q.V.symm_apply_apply] using q.V.symm.strictMono hv

/-- The pulled-back radius and expansions have the exact boundary
normalization. Paper `e1a0fd5`, `eq:observability-boundary-gauge`. -/
theorem boundary_gauge (h : StandingFull ui S) (ha : a₀ ≤ a) (hd : d ≤ a₁)
    {s : ℝ} (hs : s ∈ Icc 0 T) :
    q.fields.r s s = b ∧ q.fields.nu s s = -1 ∧ q.fields.lam s s = 1 := by
  have hm := Icc_subset_Icc ha hd (q.U_mem hs)
  have hp := c.source_mem hm
  apply SSFields.normalizedPullback_boundary_gauge
  · simpa only [q.boundary s hs] using (c.points (q.U s) hm).2.2
  · simpa only [q.boundary s hs] using (h.nu_neg hp).ne
  · simpa only [q.boundary s hs] using (h.lam_pos hp).ne'
  · simpa only [q.boundary s hs] using q.U_jacobian s hs
  · simpa only [q.boundary s hs] using q.V_jacobian s hs

/-- Incoming-coordinate factors cancel, preserving the source K ratio.
Paper `e1a0fd5`, lines 742–749 and 1473. -/
theorem incoming_ratio (h : StandingFull ui S) {K : ℝ}
    (hK : CylinderKBounds ui S K) (ha : a₀ ≤ a) (hd : d ≤ a₁)
    {s t : ℝ} (ht : 0 ≤ t) (hts : t ≤ s) (hsT : s ≤ T)
    (hp : (s, t) ∈ chartCylinder q.axisGraph T) :
    q.fields.lam t t / q.fields.lam s t ≤ K := by
  change (S.normalizedPullback q.U q.V q.dU q.dV 0).lam t t /
    (S.normalizedPullback q.U q.V q.dU q.dV 0).lam s t ≤ K
  rw [SSFields.normalizedPullback_incoming_ratio S q.U q.V q.dU q.dV 0 s t
    (q.dV_positive t).ne']
  apply h.cylinder_incoming_lam_ratio hK
  · exact q.source_mem ha hd
      ⟨ht, hts.trans hsT, (q.axis_before_boundary ha hd ⟨ht, hts.trans hsT⟩).le, le_rfl⟩
  · exact q.source_mem ha hd hp

/-- The geometric boundary travel-time bound gives the exact normalized
axis-arrival field, with the same K. Paper `e1a0fd5`,
`eq:boundary-travel-time`, lines 745–749 and 1473. -/
theorem axis_reached (h : StandingFull ui S) {K : ℝ}
    (hK : CylinderKBounds ui S K) (ha : a₀ ≤ a) (hd : d ≤ a₁)
    {t : ℝ} (ht : t ∈ Icc 0 T) (htK : t + K * b ≤ T) :
    ∃ s ∈ Icc t (t + K * b), q.axisGraph s = t := by
  have hKpos := zero_lt_one.trans_le hK.1
  have hwait : 0 ≤ K * b := (mul_pos hKpos c.radius_pos).le
  have hlate : t + K * b ∈ Icc 0 T := ⟨by linarith [ht.1], htK⟩
  have hx := Icc_subset_Icc ha hd (q.U_mem ht)
  have hy := Icc_subset_Icc ha hd (q.U_mem hlate)
  have hxy : q.U t ≤ q.U (t + K * b) := q.U.monotone (by linarith)
  have hsub : Icc (q.U t) (q.U (t + K * b)) ⊆ Icc a₀ a₁ := Icc_subset_Icc hx.1 hy.2
  have htime : cylinderTime S c.v (q.U t) (q.U (t + K * b)) = K * b := by
    have he := (c.clock (q.U t) (q.U (t + K * b)) hx.1 hxy hy.2).2
    have he0 := q.clock_inverse_apply ht
    have he1 := q.clock_inverse_apply hlate
    dsimp only [cylinderTime]
    linarith
  have hreach : c.v (q.U t) ≤ q.U (t + K * b) :=
    h.cylinder_axis_parameter_le_of_time hK hxy
      (c.smooth_v.continuousOn.mono hsub)
      (fun u hu => c.source_mem (hsub hu))
      (fun u hu => c.tangent u ⟨hx.1.trans_lt hu.1, hu.2.trans_le hy.2⟩)
      (c.points _ hy).2.2 htime.ge
  refine ⟨q.U.symm (q.V t), ⟨?_, ?_⟩, ?_⟩
  · have he := q.U.symm.monotone (c.points _ hx).1.le
    simpa only [q.boundary t ht, q.U.symm_apply_apply] using he
  · have he := q.U.symm.monotone hreach
    simpa only [q.boundary t ht, q.U.symm_apply_apply] using he
  · simp only [axisGraph, q.U.apply_symm_apply, q.V.symm_apply_apply]

end NormalizedBoundaryCoordinates

end AcExtensionPrinciple

end
