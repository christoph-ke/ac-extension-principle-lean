module

public import AcExtensionPrinciple.Observability.PropA4Axis
public import AcExtensionPrinciple.Observability.PropA4InnerChart
public import AcExtensionPrinciple.Observability.FromSolutionClock
public import AcExtensionPrinciple.Gauge.Primitive

/-!
# Geometry of a smaller cylinder in a normalized chart

Paper `e1a0fd5`, `equations.tex` lines 1460–1473 and 1877–1907.
The smaller cylinder is a level set of the original radius, rather than
the diagonal. The three geometric K facts are kept separate.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

namespace NormalizedChartData

variable {b T K : ℝ} {S : SSFields} (h : NormalizedChartData b T K S)

/-- Radius is strictly increasing on each full outgoing slice. Paper
`e1a0fd5`, lines 1460–1473, `eq:observability-boundary-gauge`. -/
theorem inner_radius_strictMono {s : ℝ} (hs : s ∈ Icc 0 T) :
    StrictMonoOn (S.r s) (Icc (h.g s) s) := by
  intro x hx y hy hxy
  have hseg := h.out_subset hs hx.1 hy.2
  have hc : ContinuousOn (S.lam s) (Icc x y) :=
    h.continuous_lam.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun z hz => hseg ⟨by simp, hz⟩)
  have hp : 0 < ∫ z in x..y, S.lam s z := by
    apply intervalIntegral.integral_pos hxy hc
      (fun z hz => (h.signs s z (hseg ⟨by simp, hz.1.le, hz.2⟩)).1.le)
    exact ⟨y, ⟨hxy.le, le_rfl⟩, (h.signs s y (hseg ⟨by simp, hxy.le, le_rfl⟩)).1⟩
  have he := (h.equations.radius_t s x y hxy.le hseg).2
  linarith

/-- Every positive radius below b has a unique label on every slice.
Paper `e1a0fd5`, lines 1877–1887 and 1901. -/
theorem exists_unique_inner_label {a s : ℝ} (ha : 0 < a) (hab : a < b)
    (hs : s ∈ Icc 0 T) :
    ∃! t, t ∈ Ioo (h.g s) s ∧ S.r s t = a := by
  have hc : ContinuousOn (S.r s) (Icc (h.g s) s) :=
    h.continuous_r.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun z hz => h.out_subset hs le_rfl le_rfl ⟨by simp, hz⟩)
  obtain ⟨t, ht, hr⟩ := intermediate_value_Icc
    (h.axis_before_boundary s hs).le hc (show a ∈ Icc (S.r s (h.g s)) (S.r s s) by
      rw [(h.axis_values s hs).1, (h.boundary_gauge s hs).1]
      exact ⟨ha.le, hab.le⟩)
  have hgt : h.g s < t := by
    apply lt_of_le_of_ne ht.1
    intro he
    have hz := (h.axis_values s hs).1
    rw [he] at hz
    linarith
  have hts : t < s := by
    apply lt_of_le_of_ne ht.2
    intro he
    rw [he, (h.boundary_gauge s hs).1] at hr
    linarith
  refine ⟨t, ⟨⟨hgt, hts⟩, hr⟩, ?_⟩
  intro z hz
  exact (h.inner_radius_strictMono hs).injOn
    (Ioo_subset_Icc_self hz.1) ht (hz.2.trans hr.symm)

/-- The canonical radius-a label, extended by zero outside the outer
time interval. The extension is never used as a coordinate. Paper
`e1a0fd5`, lines 1877–1887. -/
@[expose] noncomputable def innerLabel (a : ℝ) (ha : 0 < a) (hab : a < b)
    (s : ℝ) : ℝ :=
  if hs : s ∈ Icc 0 T then (h.exists_unique_inner_label ha hab hs).choose else 0

/-- The selected label lies strictly between the axis and outer boundary
and has exactly radius a. Paper `e1a0fd5`, lines 1877–1887. -/
theorem innerLabel_spec {a : ℝ} (ha : 0 < a) (hab : a < b) {s : ℝ}
    (hs : s ∈ Icc 0 T) :
    h.innerLabel a ha hab s ∈ Ioo (h.g s) s ∧
      S.r s (h.innerLabel a ha hab s) = a := by
  simp only [innerLabel, dite_eq_left hs]
  exact (h.exists_unique_inner_label ha hab hs).choose_spec.1

/-- On a late slice, the inner cylinder has label width at most Ka.
This is the width used in the inner arrival-time proof. Paper `e1a0fd5`,
line 1901 and `eq:observability-axis-label-bounds`, lines 1694–1698. -/
theorem inner_label_width {a s t : ℝ} (hlate : K * b ≤ s)
    (hp : (s, t) ∈ chartCylinder h.g T) (hr : S.r s t = a) :
    t - h.g s ≤ K * a := by
  have hK : 0 < K := zero_lt_one.trans_le h.K_ge_one
  have hh := (PropA4.radius_label_bounds h hlate hp).1
  rw [hr] at hh
  simpa only [mul_comm] using (div_le_iff₀ hK).mp hh

/-- Earlier entry at radius a keeps the same incoming expansion bound.
The old incoming label is nonnegative on late slices. Paper `e1a0fd5`,
line 1901, `eq:observability-boundary-gauge`. -/
theorem inner_entry_ratio {x y t : ℝ} (ht : 0 ≤ t)
    (hx : (x, t) ∈ chartInterior (chartCylinder h.g T) S)
    (hy : (y, t) ∈ chartCylinder h.g T) : S.lam x t / S.lam y t ≤ K := by
  apply PropA4.inner_incoming_ratio (h.signs y t hy).1 (h.lam_bounds ht hx).2
  have he := h.incoming_ratio y t ht hy.2.2.2 hy.2.1 hy
  rwa [(h.boundary_gauge t ⟨ht, hy.2.2.2.trans hy.2.1⟩).2.2] at he

end NormalizedChartData

/-- A regular radius-a graph on an old-time subinterval. These are internal
coordinate premises, not an additional solution-class assumption. Paper
`e1a0fd5`, lines 1877–1887 and 1901–1907. -/
structure InnerCylinder {b T K : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (a s₀ s₁ : ℝ) where
  a_pos : 0 < a
  a_lt_b : a < b
  ordered : s₀ ≤ s₁
  late : K * b ≤ s₀
  terminal_le : s₁ ≤ T
  v : ℝ → ℝ
  continuous_v : ContinuousOn v (Icc s₀ s₁)
  points : ∀ s ∈ Icc s₀ s₁, h.g s < v s ∧ v s < s ∧ S.r s (v s) = a
  tangent : ∀ s ∈ Ioo s₀ s₁,
    HasDerivAt v (-S.nu s (v s) / S.lam s (v s)) s

namespace InnerCylinder

variable {b T K a s₀ s₁ : ℝ} {S : SSFields} {h : NormalizedChartData b T K S}
variable (c : InnerCylinder h a s₀ s₁)

/-- An inner boundary point is an off-axis point of the old chart. Paper
`e1a0fd5`, lines 1877–1887. -/
theorem source_mem {s : ℝ} (hs : s ∈ Icc s₀ s₁) :
    (s, c.v s) ∈ chartInterior (chartCylinder h.g T) S := by
  have hK : 0 ≤ K := (zero_lt_one.trans_le h.K_ge_one).le
  refine ⟨⟨(mul_nonneg hK h.b_pos.le).trans (c.late.trans hs.1),
    hs.2.trans c.terminal_le, (c.points s hs).1.le, (c.points s hs).2.1.le⟩, ?_⟩
  rw [(c.points s hs).2.2]
  exact c.a_pos

/-- The boundary clock density is continuous and positive. Paper
`e1a0fd5`, `eq:observability-inner-boundary-measure`, lines 1877–1887. -/
theorem density_continuous_positive :
    ContinuousOn (fun s => -S.nu s (c.v s)) (Icc s₀ s₁) ∧
      ∀ s ∈ Icc s₀ s₁, 0 < -S.nu s (c.v s) :=
  ⟨(h.continuous_nu.comp (continuousOn_id.prodMk c.continuous_v)
    (fun _ hs => (c.source_mem hs).1)).neg,
    fun _ hs => neg_pos.mpr (h.signs _ _ (c.source_mem hs).1).2.1⟩

/-- The old-time clock, anchored at the initial inner slice. Paper
`e1a0fd5`, `eq:observability-inner-boundary-measure`, lines 1877–1887. -/
@[expose] noncomputable def clock (s : ℝ) : ℝ :=
  ∫ x in s₀..s, -S.nu x (c.v x)

/-- Inner boundary time is at most the increase of its old incoming
label. This uses λ≤1, not an incoming-lapse lower bound. Paper
`e1a0fd5`, line 1901 and `eq:boundary-travel-time`, lines 745–749. -/
theorem clock_increment_le_label {x y : ℝ} (hx : x ∈ Icc s₀ s₁)
    (hy : y ∈ Icc s₀ s₁) (hxy : x ≤ y) :
    c.clock y - c.clock x ≤ c.v y - c.v x := by
  have hsub : Icc x y ⊆ Icc s₀ s₁ := Icc_subset_Icc hx.1 hy.2
  have hn := c.density_continuous_positive.1.mono hsub
  have hl := h.continuous_lam.comp (continuousOn_id.prodMk c.continuous_v)
    (fun _ hs => (c.source_mem hs).1)
  have hq := hn.div (hl.mono hsub)
    (fun _ hs => (h.signs _ _ (c.source_mem (hsub hs)).1).1.ne')
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hxy
    (c.continuous_v.mono hsub)
    (fun z hz => c.tangent z ⟨hx.1.trans_lt hz.1, hz.2.trans_le hy.2⟩)
    (hq.intervalIntegrable_of_Icc (μ := volume) hxy)
  have hnx := c.density_continuous_positive.1.mono (Icc_subset_Icc le_rfl hx.2)
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hnx.intervalIntegrable_of_Icc (μ := volume) hx.1)
    (hn.intervalIntegrable_of_Icc (μ := volume) hxy)
  have hmono : (∫ z in x..y, -S.nu z (c.v z)) ≤
      ∫ z in x..y, -S.nu z (c.v z) / S.lam z (c.v z) := by
    apply intervalIntegral.integral_mono_on hxy
      (hn.intervalIntegrable_of_Icc (μ := volume) hxy)
      (hq.intervalIntegrable_of_Icc (μ := volume) hxy)
    intro z hz
    have hp := c.source_mem (hsub hz)
    have ht : 0 ≤ c.v z :=
      (PropA4.axis_label_nonneg h ⟨hp.1.1, hp.1.2.1⟩
        (c.late.trans (hsub hz).1)).trans (c.points z (hsub hz)).1.le
    apply (le_div_iff₀ (h.signs _ _ hp.1).1).mpr
    exact mul_le_of_le_one_right (c.density_continuous_positive.2 z (hsub hz)).le
      (h.lam_bounds ht hp).2
  dsimp only [clock]
  linarith

/-- Before the old incoming ray reaches the axis, its elapsed inner
clock is strictly less than Ka. Paper `e1a0fd5`, line 1901. -/
theorem clock_lt_of_axis_not_reached {x y : ℝ} (hx : x ∈ Icc s₀ s₁)
    (hy : y ∈ Icc s₀ s₁) (hxy : x ≤ y) (hnot : h.g y < c.v x) :
    c.clock y - c.clock x < K * a := by
  have hc := c.clock_increment_le_label hx hy hxy
  have hw := h.inner_label_width (c.late.trans hy.1) (c.source_mem hy).1
    (c.points y hy).2.2
  linarith

/-- Once Ka of the inner clock elapses, that incoming ray has an axis
intersection during the interval. Paper `e1a0fd5`, line 1901. -/
theorem axis_reached_of_clock {x y : ℝ} (hx : x ∈ Icc s₀ s₁)
    (hy : y ∈ Icc s₀ s₁) (hxy : x ≤ y)
    (hwait : K * a ≤ c.clock y - c.clock x) :
    ∃ z ∈ Icc x y, h.g z = c.v x := by
  have hreach : c.v x ≤ h.g y := by
    by_contra hn
    exact (not_lt_of_ge hwait)
      (c.clock_lt_of_axis_not_reached hx hy hxy (lt_of_not_ge hn))
  exact intermediate_value_Icc hxy h.continuous_g.continuousOn
    ⟨(c.points x hx).1.le, hreach⟩

end InnerCylinder

end AcExtensionPrinciple

end
