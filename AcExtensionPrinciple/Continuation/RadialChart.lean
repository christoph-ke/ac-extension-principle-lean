module

public import AcExtensionPrinciple.Continuation.OriginalClass
public import AcExtensionPrinciple.Gauge.ContinuationMap
public import AcExtensionPrinciple.Gauge.AbsoluteContinuity
public import Mathlib.Order.Hom.Set

/-!
# A global extension of the selected radial coordinate

Paper `e1a0fd5`, `eq:continuation-null-gauge`, lines 1390–1422.
The extension to the left is only a convenient way to define a total inverse;
the source chart and its future linear extension are unchanged.
-/

public section

namespace AcExtensionPrinciple

open Set Filter
open scoped Topology

/-- Extend the radial coordinate linearly to the left of the selected vertex.
Paper `e1a0fd5`, `eq:continuation-null-gauge`, lines 1390–1422. -/
@[expose] noncomputable def radialChartMap (g d : ℝ → ℝ) (a t : ℝ) : ℝ :=
  if t ≤ a then 2 * d a * (t - a) else continuationMap g d t

/-- The extended Jacobian, with its argument clamped to the original cone.
Paper `e1a0fd5`, `eq:continuation-null-gauge`, lines 1390–1422. -/
@[expose] noncomputable def radialChartDerivative (d : ℝ → ℝ) (a t : ℝ) : ℝ :=
  2 * d (max a (min t 0))

/-- The auxiliary left extension agrees with the selected coordinate on its
original interval. Paper `e1a0fd5`, lines 1393–1400. -/
theorem radialChartMap_on_interval {g d : ℝ → ℝ} {a : ℝ} (_ha : a ≤ 0) (hg : g a = 0) :
    ∀ t ∈ Icc a 0, radialChartMap g d a t = 2 * g t := by
  intro t ht
  by_cases hta : t ≤ a
  · have he : t = a := le_antisymm hta ht.1
    subst t
    simp [radialChartMap, hg]
  · simp [radialChartMap, hta, continuationMap_of_nonpos g d ht.2]

/-- The Jacobian agrees with twice λ on the selected cone.
Paper `e1a0fd5`, lines 1393–1400. -/
theorem radialChartDerivative_on_interval {d : ℝ → ℝ} {a t : ℝ} (ht : t ∈ Icc a 0) :
    radialChartDerivative d a t = 2 * d t := by
  simp [radialChartDerivative, min_eq_left ht.2, max_eq_right ht.1]

/-- The extended Jacobian is continuous and retains the positive lower bound.
Paper `e1a0fd5`, lines 1395 and 1422. -/
theorem radialChartDerivative_properties {d : ℝ → ℝ} {a c : ℝ} (ha : a ≤ 0)
    (hc : ContinuousOn d (Icc a 0)) (hb : ∀ t ∈ Icc a 0, c ≤ d t) :
    Continuous (radialChartDerivative d a) ∧ ∀ t, 2 * c ≤ radialChartDerivative d a t := by
  have hmem (t : ℝ) : max a (min t 0) ∈ Icc a 0 :=
    ⟨le_max_left _ _, max_le ha (min_le_right _ _)⟩
  constructor
  · have hclamp : Continuous (fun t : ℝ => max a (min t 0)) := by fun_prop
    have hm : MapsTo (fun t : ℝ => max a (min t 0)) univ (Icc a 0) :=
      fun t _ => hmem t
    exact (continuousOn_univ.mp (hc.comp hclamp.continuousOn hm)).const_mul 2
  · exact fun t => mul_le_mul_of_nonneg_left (hb _ (hmem t)) (by norm_num)

/-- The left extension joins the existing C¹ continuation map with its actual
derivative at the selected vertex. Paper `e1a0fd5`, lines 1390–1422. -/
theorem radialChartMap_hasDerivAt {g d : ℝ → ℝ} {a : ℝ} (ha : a ≤ 0) (hg0 : g a = 0)
    (hg : ∀ t ∈ Icc a 0, HasDerivWithinAt g (d t) (Icc a 0) t) :
    ∀ t, HasDerivAt (radialChartMap g d a) (radialChartDerivative d a t) t := by
  have hright := hasDerivWithinAt_continuationMap ha hg
  have he (x : ℝ) (hx : a ≤ x) : radialChartMap g d a x = continuationMap g d x := by
    by_cases hxa : x ≤ a
    · have heq : x = a := le_antisymm hxa hx
      subst x
      simp [radialChartMap, continuationMap, ha, hg0]
    · simp [radialChartMap, hxa]
  have hrD (x : ℝ) (hx : a ≤ x) :
      radialChartDerivative d a x = continuationDerivative d x := by
    simp only [radialChartDerivative, continuationDerivative]
    rw [max_eq_right (le_min hx ha)]
  have hl (x : ℝ) : HasDerivAt (fun t => 2 * d a * (t - a)) (2 * d a) x := by
    convert ((hasDerivAt_id x).sub_const a).const_mul (2 * d a) using 1 <;> simp
  intro t
  rcases lt_trichotomy t a with hta | heq | hat
  · have hd : radialChartDerivative d a t = 2 * d a := by
      simp [radialChartDerivative, max_eq_left ((min_le_left t 0).trans hta.le)]
    rw [hd]
    apply (hl t).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hta] with x hx
    simp [radialChartMap, hx.le]
  · subst t
    have hl' : HasDerivWithinAt (radialChartMap g d a) (2 * d a) (Iic a) a :=
      (hl a).hasDerivWithinAt.congr_of_mem
        (fun x hx => by simp only [radialChartMap, ite_eq_left (show x ≤ a from hx)]) (by simp)
    have hr' := (hright a (by simp)).congr_of_mem (fun x hx => he x hx) (by simp)
    rw [continuationDerivative_of_nonpos d ha] at hr'
    have ht := hl'.union hr'
    rw [Iic_union_Ici, hasDerivWithinAt_univ] at ht
    simpa [radialChartDerivative, min_eq_left ha] using ht
  · rw [hrD t hat.le]
    apply ((hright t hat.le).hasDerivAt (Ici_mem_nhds hat)).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hat] with x hx
    exact he x hx.le

/-- The selected coordinate admits a global increasing C¹ chart, retaining
the exact radial map on the original cone. Paper `e1a0fd5`, lines 1390–1422. -/
theorem radialChartMap_orderIso {g d : ℝ → ℝ} {a c : ℝ} (ha : a < 0) (hc : 0 < c)
    (hg0 : g a = 0)
    (hg : ∀ t ∈ Icc a 0, HasDerivWithinAt g (d t) (Icc a 0) t)
    (hd : ContinuousOn d (Icc a 0)) (hb : ∀ t ∈ Icc a 0, c ≤ d t) :
    ∃ T : ℝ ≃o ℝ, (T : ℝ → ℝ) = radialChartMap g d a := by
  have hD := radialChartDerivative_properties ha.le hd hb
  have hder := radialChartMap_hasDerivAt ha.le hg0 hg
  have hmono : StrictMono (radialChartMap g d a) := by
    intro x y hxy
    have hl := gauge_lower_bound (a := x) (b := y)
      (fun t _ => (hder t).hasDerivWithinAt) (fun t _ => hD.2 t)
      x ⟨le_rfl, hxy.le⟩ y ⟨hxy.le, le_rfl⟩ hxy.le
    have hp : 0 < 2 * c * (y - x) := mul_pos (by positivity) (sub_pos.mpr hxy)
    linarith
  have hcont : Continuous (radialChartMap g d a) := continuous_iff_continuousAt.mpr
    (fun x => (hder x).continuousAt)
  have hvertex : radialChartMap g d a a = 0 := by simp [radialChartMap]
  have hterminal : radialChartMap g d a 0 = 2 * g 0 := by
    simpa using radialChartMap_on_interval ha.le hg0 0 ⟨ha.le, le_rfl⟩
  have hda : 0 < 2 * d a := mul_pos (by norm_num) (hc.trans_le (hb a ⟨le_rfl, ha.le⟩))
  have hd0 : 0 < 2 * d 0 := mul_pos (by norm_num) (hc.trans_le (hb 0 ⟨ha.le, le_rfl⟩))
  have hsurj : Function.Surjective (radialChartMap g d a) := by
    intro y
    by_cases hy : y ≤ 0
    · refine ⟨a + y / (2 * d a), ?_⟩
      have hx : a + y / (2 * d a) ≤ a := by
        have := div_nonpos_of_nonpos_of_nonneg hy hda.le
        linarith
      simp only [radialChartMap, ite_eq_left hx]
      field_simp [ne_of_gt (show 0 < d a by linarith)]
      ring
    · by_cases hyt : 2 * g 0 ≤ y
      · refine ⟨(y - 2 * g 0) / (2 * d 0), ?_⟩
        have hx : 0 ≤ (y - 2 * g 0) / (2 * d 0) := div_nonneg (sub_nonneg.mpr hyt) hd0.le
        have hxa : ¬(y - 2 * g 0) / (2 * d 0) ≤ a := by linarith
        simp only [radialChartMap, ite_eq_right hxa, continuationMap_of_nonneg g d hx]
        field_simp [ne_of_gt (show 0 < d 0 by linarith)]
        ring
      · have hi := hcont.continuousOn.image_Icc_of_monotoneOn ha.le (hmono.monotone.monotoneOn _)
        rw [hvertex, hterminal] at hi
        have hym : y ∈ radialChartMap g d a '' Icc a 0 := by
          rw [hi]
          exact ⟨(lt_of_not_ge hy).le, (lt_of_not_ge hyt).le⟩
        obtain ⟨x, _, hx⟩ := hym
        exact ⟨x, hx⟩
  exact ⟨hmono.orderIsoOfSurjective _ hsurj, by simp⟩

end AcExtensionPrinciple

end
