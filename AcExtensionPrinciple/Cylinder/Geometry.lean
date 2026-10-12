module

public import AcExtensionPrinciple.Cylinder.Smooth
public import AcExtensionPrinciple.GeometricBounds.Kappa

/-!
# Uniform cylinder geometry and boundary travel time

Paper `e1a0fd5`, `equations.tex` lines 742–749,
`eq:boundary-travel-time`. The uniform mass gap from Lemma 1.1 is an explicit
helper premise, supplied by `StandingFull.mass_gap_lower` in
`GeometricBounds/Kappa.lean`.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- The common geometric constant used on all regular cylinders.
Paper `e1a0fd5`, lines 742–749, `eq:boundary-travel-time`. -/
@[expose] def CylinderKBounds (ui : ℝ) (S : SSFields) (K : ℝ) : Prop :=
  1 ≤ K ∧ ∀ p ∈ pastTriangle ui,
    K⁻¹ ≤ S.lam p.1 p.2 ∧ S.lam p.1 p.2 ≤ 1 ∧
      K⁻¹ ≤ 1 - S.mu p.1 p.2 ∧ K⁻¹ ≤ -S.nu p.1 p.2

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Choose K from Lemma 1.1. Its gap premise is precisely G2 with ci>0;
The positive subtype `initialGap` discharges this premise.
Paper `e1a0fd5`, lines 742–749, `eq:mass-gap-and-nu-bound`. -/
theorem exists_cylinder_K_of_geometric {ci : ℝ} (hci : 0 < ci)
    (hgap : ∀ p ∈ pastTriangle ui, ci * Real.exp (-Bstar ui S) ≤ 1 - S.mu p.1 p.2) :
    ∃ K : ℝ, CylinderKBounds ui S K := by
  let l := Real.exp (-Bstar ui S)
  let g := ci * l
  have hl : 0 < l := Real.exp_pos _
  have hg : 0 < g := mul_pos hci hl
  let K := 1 + l⁻¹ + g⁻¹
  have hK1 : 1 ≤ K := by dsimp [K]; linarith [inv_nonneg.mpr hl.le, inv_nonneg.mpr hg.le]
  have hK : 0 < K := zero_lt_one.trans_le hK1
  have hKl : l⁻¹ ≤ K := by dsimp [K]; linarith [inv_nonneg.mpr hl.le, inv_nonneg.mpr hg.le]
  have hKg : g⁻¹ ≤ K := by dsimp [K]; linarith [inv_nonneg.mpr hl.le, inv_nonneg.mpr hg.le]
  have hli : K⁻¹ ≤ l := by
    simpa only [inv_inv] using (inv_le_inv₀ hK (inv_pos.mpr hl)).mpr hKl
  have hgi : K⁻¹ ≤ g := by
    simpa only [inv_inv] using (inv_le_inv₀ hK (inv_pos.mpr hg)).mpr hKg
  refine ⟨K, hK1, ?_⟩
  intro p hp
  exact ⟨hli.trans (h.lam_bounds hp).1, (h.lam_bounds hp).2,
    hgi.trans (hgap p hp), hli.trans (h.neg_nu_lower hp)⟩

/-- A single uniform K now follows from the completed Lemma 1.1 without helper premises.
Paper `e1a0fd5`, lines 742–749, `eq:boundary-travel-time`. -/
theorem exists_cylinder_K : ∃ K : ℝ, CylinderKBounds ui S K :=
  h.exists_cylinder_K_of_geometric h.initialGap_pos
    (fun _ hp => h.mass_gap_lower hp)

/-- Uniform incoming λ ratio, including the ray's axis endpoint.
Paper `e1a0fd5`, lines 742–749. -/
theorem cylinder_incoming_lam_ratio {K u0 u v0 : ℝ}
    (hK : CylinderKBounds ui S K) (hp0 : (u0, v0) ∈ pastTriangle ui)
    (hp : (u, v0) ∈ pastTriangle ui) : S.lam u0 v0 / S.lam u v0 ≤ K := by
  have hK0 : 0 < K := zero_lt_one.trans_le hK.1
  apply (div_le_iff₀ (h.lam_pos hp)).mpr
  have hl := mul_le_mul_of_nonneg_left (hK.2 (u, v0) hp).1 hK0.le
  simp only [mul_inv_cancel₀ hK0.ne'] at hl
  exact (hK.2 (u0, v0) hp0).2.1.trans hl

/-- The coordinate width of a radius-b cylinder is at most Kb.
Paper `e1a0fd5`, `eq:boundary-travel-time`, lines 745–749. -/
theorem cylinder_coordinate_width {K b u v : ℝ} (hK : CylinderKBounds ui S K)
    (hp : (u, v) ∈ pastTriangle ui) (hr : S.r u v = b) : v - u ≤ K * b := by
  have hs := outSeg_subset_triangle hp.1 hp.2.1 le_rfl hp.2.2.2
  have hi := (h.regularCenter.localBV.radius_out u u v hp.2.2.1 hs).1
  have hb : K⁻¹ * (v - u) ≤ b := by
    rw [← hr, h.radius_from_axis hp]
    calc
      _ = ∫ s in u..v, K⁻¹ := by simp [mul_comm]
      _ ≤ _ := intervalIntegral.integral_mono_on hp.2.2.1 intervalIntegrable_const hi
        (fun s hs' => (hK.2 (u, s) (hs ⟨by simp, hs'⟩)).1)
  have hK0 : 0 < K := zero_lt_one.trans_le hK.1
  have hm := mul_le_mul_of_nonneg_left hb hK0.le
  simpa [← mul_assoc, mul_inv_cancel₀ hK0.ne'] using hm

end StandingFull

/-- Boundary time anchored at a0 on an arbitrary cylinder graph.
Paper `e1a0fd5`, `eq:cylinder-time`, lines 671–673. -/
@[expose] noncomputable def cylinderTime (S : SSFields) (v : ℝ → ℝ) (a0 u : ℝ) : ℝ :=
  ∫ s in a0..u, -S.nu s (v s)

/-- A continuous derivative on the interval's interior gives an AC primitive.
Paper `e1a0fd5`, calculus input to `eq:cylinder-time`, lines 671–673. -/
theorem cylinder_ac_of_continuous_derivative {f g : ℝ → ℝ} {a0 a1 : ℝ}
    (ha : a0 ≤ a1) (hf : ContinuousOn f (Icc a0 a1))
    (hg : ContinuousOn g (Icc a0 a1))
    (hd : ∀ u ∈ Ioo a0 a1, HasDerivAt f (g u) u) :
    AbsolutelyContinuousOnInterval f a0 a1 := by
  apply intervalPrimitive_ac (g := g) ha
  intro x hx
  have hc : Icc a0 x ⊆ Icc a0 a1 := Icc_subset_Icc le_rfl hx.2
  have hi := (hg.mono hc).intervalIntegrable_of_Icc (μ := volume) hx.1
  exact ⟨hi, (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.1 (hf.mono hc)
    (fun y hy => hd y ⟨hy.1, hy.2.trans_le hx.2⟩) hi).symm⟩

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Boundary time increment equals ∫λ_b v_b'; the comparison uses λ≤1.
Paper `e1a0fd5`, `eq:boundary-travel-time`, lines 745–748. -/
theorem cylinder_time_le_coordinate_increment {v : ℝ → ℝ} {a0 a1 : ℝ}
    (ha : a0 ≤ a1) (hv : ContinuousOn v (Icc a0 a1))
    (hp : ∀ u ∈ Icc a0 a1, (u, v u) ∈ pastTriangle ui)
    (hd : ∀ u ∈ Ioo a0 a1, HasDerivAt v (-S.nu u (v u) / S.lam u (v u)) u) :
    cylinderTime S v a0 a1 ≤ v a1 - v a0 := by
  have hc := continuousOn_id.prodMk hv
  have hn := h.regularCenter.continuous_nu.comp hc hp
  have hl := h.regularCenter.continuous_lam.comp hc hp
  have hq := hn.neg.div hl (fun u hu => ne_of_gt (h.lam_pos (hp u hu)))
  have hi := hq.intervalIntegrable_of_Icc (μ := volume) ha
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ha hv hd hi
  unfold cylinderTime
  calc
    _ ≤ ∫ u in a0..a1, -S.nu u (v u) / S.lam u (v u) := by
      apply intervalIntegral.integral_mono_on ha
        (hn.neg.intervalIntegrable_of_Icc (μ := volume) ha) hi
      intro u hu
      have hn0 := neg_nonneg.mpr (h.nu_neg (hp u hu)).le
      apply (le_div_iff₀ (h.lam_pos (hp u hu))).mpr
      exact mul_le_of_le_one_right hn0 (h.lam_bounds (hp u hu)).2
    _ = _ := he

/-- An incoming ray still short of the axis has elapsed boundary time strictly below Kb.
Paper `e1a0fd5`, `eq:boundary-travel-time`, lines 745–749. -/
theorem cylinder_travel_time_lt {v : ℝ → ℝ} {K b a0 u : ℝ}
    (hK : CylinderKBounds ui S K) (ha : a0 ≤ u)
    (hv : ContinuousOn v (Icc a0 u))
    (hp : ∀ s ∈ Icc a0 u, (s, v s) ∈ pastTriangle ui)
    (hd : ∀ s ∈ Ioo a0 u, HasDerivAt v (-S.nu s (v s) / S.lam s (v s)) s)
    (hr : S.r u (v u) = b) (huv0 : u < v a0) :
    cylinderTime S v a0 u < K * b := by
  calc
    _ ≤ v u - v a0 := h.cylinder_time_le_coordinate_increment ha hv hp hd
    _ < v u - u := by linarith
    _ ≤ K * b := h.cylinder_coordinate_width hK (hp u ⟨ha, le_rfl⟩) hr

/-- If elapsed time is at least Kb, the incoming ray's axis parameter is reached.
Paper `e1a0fd5`, lines 748–749, `eq:boundary-travel-time`. -/
theorem cylinder_axis_parameter_le_of_time {v : ℝ → ℝ} {K b a0 a1 : ℝ}
    (hK : CylinderKBounds ui S K) (ha : a0 ≤ a1)
    (hv : ContinuousOn v (Icc a0 a1))
    (hp : ∀ u ∈ Icc a0 a1, (u, v u) ∈ pastTriangle ui)
    (hd : ∀ u ∈ Ioo a0 a1, HasDerivAt v (-S.nu u (v u) / S.lam u (v u)) u)
    (hr : S.r a1 (v a1) = b) (ht : K * b ≤ cylinderTime S v a0 a1) : v a0 ≤ a1 := by
  by_contra hn
  exact (not_lt_of_ge ht) (h.cylinder_travel_time_lt hK ha hv hp hd hr (lt_of_not_ge hn))

/-- Once the ray's axis parameter belongs to the continued cylinder interval, its boundary
arrival time is ≤Kb. This also proves the paper's limiting conclusion directly.
Paper `e1a0fd5`, lines 748–749, `eq:boundary-travel-time`. -/
theorem cylinder_axis_arrival_time_le {v : ℝ → ℝ} {K b a0 a1 : ℝ}
    (hK : CylinderKBounds ui S K) (ha : a0 ≤ a1)
    (hv : ContinuousOn v (Icc a0 a1))
    (hp : ∀ u ∈ Icc a0 a1, (u, v u) ∈ pastTriangle ui)
    (hd : ∀ u ∈ Ioo a0 a1, HasDerivAt v (-S.nu u (v u) / S.lam u (v u)) u)
    (hr : ∀ u ∈ Icc a0 a1, S.r u (v u) = b)
    (hv0 : a0 ≤ v a0) (ht : K * b ≤ cylinderTime S v a0 a1) :
    v a0 ≤ a1 ∧ cylinderTime S v a0 (v a0) ≤ K * b := by
  have hva := h.cylinder_axis_parameter_le_of_time hK ha hv hp hd
    (hr a1 ⟨ha, le_rfl⟩) ht
  refine ⟨hva, ?_⟩
  have hsub : Icc a0 (v a0) ⊆ Icc a0 a1 := Icc_subset_Icc le_rfl hva
  calc
    _ ≤ v (v a0) - v a0 := h.cylinder_time_le_coordinate_increment hv0 (hv.mono hsub)
      (fun u hu => hp u (hsub hu)) (fun u hu => hd u ⟨hu.1, hu.2.trans_le hva⟩)
    _ ≤ K * b := h.cylinder_coordinate_width hK
      (hp (v a0) ⟨hv0, hva⟩) (hr (v a0) ⟨hv0, hva⟩)

/-- Boundary time is an AC primitive with derivative -ν_b.
Paper `e1a0fd5`, `eq:cylinder-time`, lines 671–673. -/
theorem cylinder_time_ac {v : ℝ → ℝ} {a0 a1 : ℝ} (ha : a0 ≤ a1)
    (hv : ContinuousOn v (Icc a0 a1))
    (hp : ∀ u ∈ Icc a0 a1, (u, v u) ∈ pastTriangle ui) :
    AbsolutelyContinuousOnInterval (cylinderTime S v a0) a0 a1 := by
  have hc := (h.regularCenter.continuous_nu.comp (continuousOn_id.prodMk hv) hp).neg
  have hi := hc.intervalIntegrable_of_Icc (μ := volume) ha
  exact hi.absolutelyContinuousOnInterval_intervalIntegral (c := a0) (by simp)

/-- Its ordinary derivative agrees with the boundary-time differential at interior points.
Paper `e1a0fd5`, `eq:cylinder-time`, lines 671–673. -/
theorem cylinder_time_hasDerivAt {v : ℝ → ℝ} {a0 a1 u : ℝ}
    (hv : ContinuousOn v (Icc a0 a1))
    (hp : ∀ s ∈ Icc a0 a1, (s, v s) ∈ pastTriangle ui) (hu : u ∈ Ioo a0 a1) :
    HasDerivAt (cylinderTime S v a0) (-S.nu u (v u)) u := by
  have hc := (h.regularCenter.continuous_nu.comp (continuousOn_id.prodMk hv) hp).neg
  have hi := (hc.mono (Icc_subset_Icc le_rfl hu.2.le)).intervalIntegrable_of_Icc
    (μ := volume) hu.1.le
  exact intervalIntegral.integral_hasDerivAt_right hi
    ⟨Icc a0 a1, Icc_mem_nhds hu.1 hu.2, hc.aestronglyMeasurable measurableSet_Icc⟩
    (hc.continuousAt (Icc_mem_nhds hu.1 hu.2))

/-- The same K bounds waiting time uniformly on all regular cylinders.
Paper `e1a0fd5`, lines 748–749, `eq:cylinder-time`. -/
theorem cylinder_time_lower_of_K {v : ℝ → ℝ} {K a0 a1 : ℝ}
    (hK : CylinderKBounds ui S K) (ha : a0 ≤ a1)
    (hv : ContinuousOn v (Icc a0 a1))
    (hp : ∀ u ∈ Icc a0 a1, (u, v u) ∈ pastTriangle ui) :
    K⁻¹ * (a1 - a0) ≤ cylinderTime S v a0 a1 := by
  have hc := (h.regularCenter.continuous_nu.comp (continuousOn_id.prodMk hv) hp).neg
  unfold cylinderTime
  calc
    _ = ∫ u in a0..a1, K⁻¹ := by simp [mul_comm]
    _ ≤ _ := intervalIntegral.integral_mono_on ha intervalIntegrable_const
      (hc.intervalIntegrable_of_Icc (μ := volume) ha)
      (fun u hu => (hK.2 (u, v u) (hp u hu)).2.2.2)

end StandingFull

end AcExtensionPrinciple

end
