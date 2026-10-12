module

public import AcExtensionPrinciple.Gauge.Primitive
public import AcExtensionPrinciple.Gauge.Variation
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Topology.Piecewise

/-!
# The continuation coordinate map and its linear extension

Components for paper `e1a0fd5`, `equations.tex`
`eq:continuation-null-gauge` (1294), the linear extension (1319), and
`eq:terminal-expansion-gauge` (1327). The radius vanishes at the cone vertex.
Continuity of the supplied radius derivative is explicit in the C¹ theorem.
-/

public section

namespace AcExtensionPrinciple

open Set Filter
open scoped Topology

/-- Twice the cone radius, extended linearly beyond zero. Paper `e1a0fd5`,
`eq:continuation-null-gauge`, line 1393, and the extension in line 1422. -/
@[expose] noncomputable def continuationMap (g d : ℝ → ℝ) (t : ℝ) : ℝ :=
  if t ≤ 0 then 2 * g t else 2 * g 0 + 2 * d 0 * t

/-- The derivative is held constant after zero. Paper `e1a0fd5`,
`equations.tex` line 1422. -/
@[expose] noncomputable def continuationDerivative (d : ℝ → ℝ) (t : ℝ) : ℝ :=
  2 * d (min t 0)

/-- Formula on the old chart. Paper `e1a0fd5`,
`eq:continuation-null-gauge`, lines 1391–1394. -/
theorem continuationMap_of_nonpos (g d : ℝ → ℝ) {t : ℝ} (ht : t ≤ 0) :
    continuationMap g d t = 2 * g t := by simp [continuationMap, ht]

/-- Formula on the extended chart, including the join. Paper `e1a0fd5`,
`equations.tex` line 1422. -/
theorem continuationMap_of_nonneg (g d : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    continuationMap g d t = 2 * g 0 + 2 * d 0 * t := by
  rcases ht.eq_or_lt with h | h
  · subst t
    simp [continuationMap]
  · simp [continuationMap, not_le.mpr h]

/-- Old-chart derivative formula. Paper `e1a0fd5`,
`eq:continuation-null-gauge`, lines 1391–1395. -/
theorem continuationDerivative_of_nonpos (d : ℝ → ℝ) {t : ℝ} (ht : t ≤ 0) :
    continuationDerivative d t = 2 * d t := by simp [continuationDerivative, min_eq_left ht]

/-- Constant derivative on the extension. Paper `e1a0fd5`,
`equations.tex` line 1422. -/
theorem continuationDerivative_of_nonneg (d : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    continuationDerivative d t = 2 * d 0 := by simp [continuationDerivative, min_eq_right ht]

/-- Differentiability of the extension, including the matching point. Paper
`e1a0fd5`, `eq:continuation-null-gauge`, lines 1393 and 1422. -/
theorem hasDerivAt_continuationMap {g d : ℝ → ℝ} {a : ℝ} (ha : a ≤ 0)
    (hg : ∀ t ∈ Icc a 0, HasDerivAt g (d t) t) :
    ∀ t ∈ Ici a, HasDerivAt (continuationMap g d) (continuationDerivative d t) t := by
  intro t ht
  have haff (x : ℝ) : HasDerivAt (fun t => 2 * g 0 + 2 * d 0 * t) (2 * d 0) x := by
    convert (hasDerivAt_const x (2 * g 0)).add
      ((hasDerivAt_id x).const_mul (2 * d 0)) using 1 <;> (try ext y) <;> simp
  rcases lt_trichotomy t 0 with hneg | rfl | hpos
  · rw [continuationDerivative_of_nonpos d hneg.le]
    apply ((hg t ⟨ht, hneg.le⟩).const_mul 2).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hneg] with x hx
    exact continuationMap_of_nonpos g d hx.le
  · rw [continuationDerivative_of_nonpos d le_rfl]
    have hl : HasDerivWithinAt (continuationMap g d) (2 * d 0) (Iic 0) 0 :=
      ((hg 0 ⟨ha, le_rfl⟩).const_mul 2).hasDerivWithinAt.congr
        (fun x hx => continuationMap_of_nonpos g d hx) (by simp [continuationMap])
    have hr : HasDerivWithinAt (continuationMap g d) (2 * d 0) (Ici 0) 0 :=
      (haff 0).hasDerivWithinAt.congr
        (fun x hx => continuationMap_of_nonneg g d hx) (by simp [continuationMap])
    have h := hl.union hr
    rw [Iic_union_Ici] at h
    exact h.hasDerivAt (by simp)
  · rw [continuationDerivative_of_nonneg d hpos.le]
    apply (haff t).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hpos] with x hx
    exact continuationMap_of_nonneg g d hx.le

/-- Domain-relative differentiability of the extension needs only the cone
radius derivative within its original closed segment, including the vertex.
Paper `e1a0fd5`, `equations.tex` lines 1393 and 1422. -/
theorem hasDerivWithinAt_continuationMap {g d : ℝ → ℝ} {a : ℝ} (ha : a ≤ 0)
    (hg : ∀ t ∈ Icc a 0, HasDerivWithinAt g (d t) (Icc a 0) t) :
    ∀ t ∈ Ici a, HasDerivWithinAt (continuationMap g d)
      (continuationDerivative d t) (Ici a) t := by
  intro t ht
  have haff (x : ℝ) : HasDerivAt (fun t => 2 * g 0 + 2 * d 0 * t) (2 * d 0) x := by
    convert (hasDerivAt_const x (2 * g 0)).add
      ((hasDerivAt_id x).const_mul (2 * d 0)) using 1 <;> (try ext y) <;> simp
  rcases lt_trichotomy t 0 with hneg | rfl | hpos
  · rw [continuationDerivative_of_nonpos d hneg.le]
    have hleft : HasDerivWithinAt (continuationMap g d) (2 * d t) (Icc a 0) t :=
      ((hg t ⟨ht, hneg.le⟩).const_mul 2).congr_of_mem
        (fun x hx => continuationMap_of_nonpos g d hx.2) ⟨ht, hneg.le⟩
    have hset : Ici a ∩ Iic 0 = Icc a 0 := by ext x; simp
    rw [← hset] at hleft
    exact (hasDerivWithinAt_inter (Iic_mem_nhds hneg)).mp hleft
  · rw [continuationDerivative_of_nonpos d le_rfl]
    have hl : HasDerivWithinAt (continuationMap g d) (2 * d 0) (Icc a 0) 0 :=
      ((hg 0 ⟨ha, le_rfl⟩).const_mul 2).congr_of_mem
        (fun x hx => continuationMap_of_nonpos g d hx.2) ⟨ha, le_rfl⟩
    have hr : HasDerivWithinAt (continuationMap g d) (2 * d 0) (Ici 0) 0 :=
      (haff 0).hasDerivWithinAt.congr
        (fun x hx => continuationMap_of_nonneg g d hx) (by simp [continuationMap])
    have hset : Icc a 0 ∪ Ici 0 = Ici a := by
      ext x
      simp only [mem_union, mem_Icc, mem_Ici]
      constructor
      · rintro (h | h)
        · exact h.1
        · exact ha.trans h
      · intro hx
        rcases le_total x 0 with h | h
        · exact Or.inl ⟨hx, h⟩
        · exact Or.inr h
    simpa only [hset] using hl.union hr
  · rw [continuationDerivative_of_nonneg d hpos.le]
    have h : HasDerivAt (continuationMap g d) (2 * d 0) t := by
      apply (haff t).congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds hpos] with x hx
      exact continuationMap_of_nonneg g d hx.le
    exact h.hasDerivWithinAt

/-- The extended derivative is continuous on the whole future interval.
Paper `e1a0fd5`, `equations.tex` line 1422. -/
theorem continuousOn_continuationDerivative {d : ℝ → ℝ} {a : ℝ} (ha : a ≤ 0)
    (hd : ContinuousOn d (Icc a 0)) : ContinuousOn (continuationDerivative d) (Ici a) := by
  apply (hd.comp (continuous_id.min continuous_const).continuousOn _).const_mul 2
  intro t ht
  exact ⟨le_min ht ha, min_le_right _ _⟩

/-- The concrete extension is C¹ under the stated continuous-derivative premise.
Paper `e1a0fd5`, `equations.tex` lines 1393 and 1422. -/
theorem contDiffOn_continuationMap {g d : ℝ → ℝ} {a : ℝ} (ha : a ≤ 0)
    (hg : ∀ t ∈ Icc a 0, HasDerivWithinAt g (d t) (Icc a 0) t)
    (hd : ContinuousOn d (Icc a 0)) :
    ContDiffOn ℝ 1 (continuationMap g d) (Ici a) := by
  have h := hasDerivWithinAt_continuationMap ha hg
  apply (contDiffOn_one_iff_derivWithin (uniqueDiffOn_Ici a)).mpr
  refine ⟨fun x hx => (h x hx).differentiableWithinAt, ?_⟩
  apply (continuousOn_continuationDerivative ha hd).congr
  intro x hx
  exact ((h x hx).derivWithin ((uniqueDiffOn_Ici a) x hx))

/-- The positive derivative bound persists after the linear extension. Paper
`e1a0fd5`, `eq:continuation-null-gauge`, line 1395, and line 1422. -/
theorem continuationDerivative_lower_bound {d : ℝ → ℝ} {a c : ℝ} (ha : a ≤ 0)
    (hd : ∀ t ∈ Icc a 0, c ≤ d t) :
    ∀ t ∈ Ici a, 2 * c ≤ continuationDerivative d t := by
  intro t ht
  unfold continuationDerivative
  exact mul_le_mul_of_nonneg_left (hd _ ⟨le_min ht ha, min_le_right _ _⟩) (by norm_num)

/-- A BV radius derivative remains BV after its constant extension. This
supplies the Jacobian BV premise for the weighted pullback field estimates.
Paper `e1a0fd5`, `equations.tex` lines 1422 and 1441–1443. -/
theorem boundedVariation_continuationDerivative {d : ℝ → ℝ} {a b : ℝ} (ha : a ≤ 0)
    (hd : BoundedVariationOn d (Icc a 0)) :
    BoundedVariationOn (continuationDerivative d) (Icc a b) := by
  have hm : MonotoneOn (fun t : ℝ => min t 0) (Icc a b) :=
    fun _ _ _ _ h => min_le_min_right 0 h
  have hmap : MapsTo (fun t : ℝ => min t 0) (Icc a b) (Icc a 0) :=
    fun _ ht => ⟨le_min ht.1 ha, min_le_right _ _⟩
  have hv : BoundedVariationOn (fun t : ℝ => d (min t 0)) (Icc a b) := by
    exact ne_top_of_le_ne_top hd (eVariationOn.comp_le_of_monotoneOn d _ hm hmap)
  have hc : BoundedVariationOn (fun _ : ℝ => (2 : ℝ)) (Icc a b) := by
    change eVariationOn (fun _ : ℝ => (2 : ℝ)) (Icc a b) ≠ ⊤
    rw [eVariationOn.constant_on (by
      rintro x ⟨_, _, rfl⟩ y ⟨_, _, rfl⟩
      rfl)]
    simp
  exact hc.mul hv

/-- Strict increase of the concrete extension. Paper `e1a0fd5`,
`eq:continuation-null-gauge`, line 1395, and line 1422. -/
theorem strictMonoOn_continuationMap {g d : ℝ → ℝ} {a c : ℝ} (ha : a ≤ 0)
    (hc : 0 < c) (hg : ∀ t ∈ Icc a 0, HasDerivWithinAt g (d t) (Icc a 0) t)
    (hd : ∀ t ∈ Icc a 0, c ≤ d t) : StrictMonoOn (continuationMap g d) (Ici a) := by
  have h := hasDerivWithinAt_continuationMap ha hg
  apply strictMonoOn_of_deriv_pos (convex_Ici a)
  · exact fun x hx => (h x hx).continuousWithinAt
  · intro x hx
    have hxa : a < x := by simpa only [interior_Ici, mem_Ioi] using hx
    rw [((h x (interior_subset hx)).hasDerivAt (Ici_mem_nhds hxa)).deriv]
    exact (by positivity : 0 < 2 * c).trans_le
      (continuationDerivative_lower_bound ha hd x (interior_subset hx))

/-- The selected cone vertex becomes zero by regular-axis normalization.
Paper `e1a0fd5`, `equations.tex` line 1395. -/
theorem continuationMap_vertex {g d : ℝ → ℝ} {a : ℝ} (ha : a ≤ 0) (hg : g a = 0) :
    continuationMap g d a = 0 := by simp [continuationMap, ha, hg]

/-- Preservation and reflection of the axis on the future chart. Paper
`e1a0fd5`, `eq:continuation-null-gauge`, line 1395. -/
theorem continuationMap_axis_iff {g d : ℝ → ℝ} {a c u v : ℝ} (ha : a ≤ 0)
    (hc : 0 < c) (hg : ∀ t ∈ Icc a 0, HasDerivWithinAt g (d t) (Icc a 0) t)
    (hd : ∀ t ∈ Icc a 0, c ≤ d t) (hu : u ∈ Ici a) (hv : v ∈ Ici a) :
    continuationMap g d u = continuationMap g d v ↔ u = v :=
  (strictMonoOn_continuationMap ha hc hg hd).injOn.eq_iff hu hv

/-- The terminal logarithmic expansion law in the original chart. With
`d(u)=λ(ū,u)` this is precisely paper `e1a0fd5`,
`eq:terminal-expansion-gauge`, lines 1435–1438. -/
theorem terminal_expansion_gauge {S : SSFields} {g d : ℝ → ℝ} {u : ℝ}
    (hu : u ≤ 0) (hd : 0 < d u)
    (hnu : S.nu (continuationMap g d u) (continuationMap g d 0) ≠ 0) :
    Real.log (-(S.pullback (continuationMap g d) (continuationDerivative d)).nu u 0) =
      Real.log (2 * d u) +
        Real.log (-S.nu (continuationMap g d u) (continuationMap g d 0)) := by
  rw [SSFields.pullback_log_neg_nu]
  · rw [continuationDerivative_of_nonpos d hu]
  · rw [continuationDerivative_of_nonpos d hu]
    positivity
  · exact hnu

end AcExtensionPrinciple

end
