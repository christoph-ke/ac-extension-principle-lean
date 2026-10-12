module

public import AcExtensionPrinciple.Solution.PrimitiveCalculus

/-!
# Elementary consequences of the solution class

Paper `e1a0fd5`, `eq:past-triangle`,
`eq:regular-axis`, `eq:radius-from-axis` and lines 220–275.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- Axis points belong to the past triangle. Paper `e1a0fd5`, `eq:past-triangle`. -/
theorem axis_subset_pastTriangle (ui : ℝ) : axis ui ⊆ pastTriangle ui := by
  rintro ⟨u, v⟩ ⟨hu, hu0, he⟩
  change v = u at he
  subst v
  exact ⟨hu, hu0, le_rfl, hu0.le⟩

/-- Outgoing subsegments stay in the triangle. Paper `e1a0fd5`, `eq:past-triangle`. -/
theorem outSeg_subset_triangle {ui u a b : ℝ} (hu : ui ≤ u) (hu0 : u < 0)
    (hua : u ≤ a) (hb : b ≤ 0) : outSeg u a b ⊆ pastTriangle ui := by
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  simp only [mem_singleton_iff] at hx
  subst x
  exact ⟨hu, hu0, hua.trans hy.1, hy.2.trans hb⟩

/-- Incoming subsegments stay in the triangle. Paper `e1a0fd5`, `eq:past-triangle`. -/
theorem inSeg_subset_triangle {ui v a b : ℝ} (ha : ui ≤ a) (hb0 : b < 0)
    (hbv : b ≤ v) (hv0 : v ≤ 0) : inSeg v a b ⊆ pastTriangle ui := by
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  simp only [mem_singleton_iff] at hy
  subst y
  exact ⟨ha.trans hx.1, hx.2.trans_lt hb0, hx.2.trans hbv, hv0⟩

/-- Outgoing segments strictly above the axis stay off it.
Paper `e1a0fd5`, `eq:past-triangle`, line 66. -/
theorem outSeg_subset_offAxis {ui u a b : ℝ} (hu : ui ≤ u) (hu0 : u < 0)
    (hua : u < a) (hb : b ≤ 0) : outSeg u a b ⊆ offAxis (pastTriangle ui) := by
  intro p hp
  refine ⟨outSeg_subset_triangle hu hu0 hua.le hb hp, ?_⟩
  have hp' : p.1 = u ∧ a ≤ p.2 ∧ p.2 ≤ b := by simpa [outSeg] using hp
  change ¬p.1 = p.2
  linarith [hp'.1, hp'.2.1]

/-- Incoming segments strictly below their axis endpoint stay off it.
Paper `e1a0fd5`, `eq:past-triangle`, line 66. -/
theorem inSeg_subset_offAxis {ui v a b : ℝ} (ha : ui ≤ a) (hb0 : b < 0)
    (hbv : b < v) (hv0 : v ≤ 0) : inSeg v a b ⊆ offAxis (pastTriangle ui) := by
  intro p hp
  refine ⟨inSeg_subset_triangle ha hb0 hbv.le hv0 hp, ?_⟩
  have hp' : (a ≤ p.1 ∧ p.1 ≤ b) ∧ p.2 = v := by simpa [inSeg] using hp
  change ¬p.1 = p.2
  linarith [hp'.1.2, hp'.2]

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)

include h

/-- The lower expansion bound in D1 also applies on the axis.
Paper `e1a0fd5`, line 222, Luk–Oh Definition 2.1(1). -/
theorem lam_pos {p : ℝ × ℝ} (hp : p ∈ pastTriangle ui) : 0 < S.lam p.1 p.2 := by
  obtain ⟨c, hc, hb⟩ := h.regularCenter.localBV.expansion_bounds {p}
    (isCompact_singleton) (singleton_subset_iff.mpr hp)
  exact hc.trans_le (hb p (mem_singleton p)).1

/-- Negative incoming expansion, including axis values.
Paper `e1a0fd5`, line 120 and `eq:regular-axis`. -/
theorem nu_neg {p : ℝ × ℝ} (hp : p ∈ pastTriangle ui) : S.nu p.1 p.2 < 0 := by
  rcases hp.2.2.1.eq_or_lt with he | he
  · have ha : (p.1, p.1) ∈ axis ui := ⟨hp.1, hp.2.1, rfl⟩
    rw [← he, h.regularCenter.axis_expansions _ ha]
    exact neg_neg_of_pos (h.lam_pos (axis_subset_pastTriangle ui ha))
  · exact (h.signs p hp he).2.1

omit h in
/-- Restrict continuous fields to outgoing segments.
Paper `e1a0fd5`, lines 220–275. -/
theorem continuous_out {f : ℝ → ℝ → ℝ}
    (hf : ContinuousOn (fun p => f p.1 p.2) (pastTriangle ui))
    {u a b : ℝ} (hs : outSeg u a b ⊆ pastTriangle ui) : ContinuousOn (f u) (Icc a b) := by
  exact hf.comp (continuous_const.prodMk continuous_id).continuousOn
    (fun v hv => hs ⟨by simp, hv⟩)

omit h in
/-- Restrict continuous fields to incoming segments.
Paper `e1a0fd5`, lines 220–275. -/
theorem continuous_in {f : ℝ → ℝ → ℝ}
    (hf : ContinuousOn (fun p => f p.1 p.2) (pastTriangle ui))
    {v a b : ℝ} (hs : inSeg v a b ⊆ pastTriangle ui) :
    ContinuousOn (fun u => f u v) (Icc a b) := by
  exact hf.comp (continuous_id.prodMk continuous_const).continuousOn
    (fun u hu => hs ⟨hu, by simp⟩)

/-- Radius is the integral of λ from the axis.
Paper `e1a0fd5`, `eq:radius-from-axis`. -/
theorem radius_from_axis {u v : ℝ} (hp : (u, v) ∈ pastTriangle ui) :
    S.r u v = ∫ s in u..v, S.lam u s := by
  have he := (h.regularCenter.localBV.radius_out u u v hp.2.2.1
    (outSeg_subset_triangle hp.1 hp.2.1 le_rfl hp.2.2.2)).2
  rw [(h.regularCenter.localBV.axis_values u ⟨hp.1, hp.2.1, le_rfl, hp.2.1.le⟩).1,
    sub_zero] at he
  exact he

/-- Radius is strictly positive off the axis, derived from D1 and its primitive.
Paper `e1a0fd5`, `eq:radius-from-axis`, line 66. -/
theorem r_pos {u v : ℝ} (hp : (u, v) ∈ pastTriangle ui) (huv : u < v) : 0 < S.r u v := by
  have hs := outSeg_subset_triangle hp.1 hp.2.1 le_rfl hp.2.2.2
  obtain ⟨c, hc, hb⟩ := h.regularCenter.localBV.expansion_bounds (outSeg u u v)
    (isCompact_singleton.prod isCompact_Icc) hs
  have hi := (h.regularCenter.localBV.radius_out u u v huv.le hs).1
  have hbound : c * (v - u) ≤ S.r u v := by
    rw [h.radius_from_axis hp]
    calc
      c * (v - u) = ∫ s in u..v, c := by simp [mul_comm]
      _ ≤ _ := intervalIntegral.integral_mono_on huv.le (intervalIntegrable_const) hi
        (fun s hs' => (hb (u, s) ⟨by simp, hs'⟩).1)
  exact (mul_pos hc (sub_pos.mpr huv)).trans_le hbound

/-- The zero-division convention gives μ = 0 on the axis.
Paper `e1a0fd5`, line 275. -/
theorem mu_axis {a : ℝ} (ha : (a, a) ∈ axis ui) : S.mu a a = 0 := by
  have hr := (h.regularCenter.localBV.axis_values a (axis_subset_pastTriangle ui ha)).1
  simp [SSFields.mu, massRatio, hr]

/-- Untrapped mass ratio including its axis value. Paper `e1a0fd5`, line 120, 275. -/
theorem mu_bounds {p : ℝ × ℝ} (hp : p ∈ pastTriangle ui) : 0 ≤ S.mu p.1 p.2 ∧ S.mu p.1 p.2 < 1 := by
  rcases hp.2.2.1.eq_or_lt with he | he
  · rw [← he, h.mu_axis ⟨hp.1, hp.2.1, rfl⟩]
    exact ⟨le_rfl, zero_lt_one⟩
  · exact (h.signs p hp he).2.2

end StandingFull

end AcExtensionPrinciple

end
