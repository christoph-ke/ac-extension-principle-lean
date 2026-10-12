module

public import AcExtensionPrinciple.Redundancy.OutgoingScalarConvention

/-!
# The incoming scalar right-continuity convention is redundant
Paper commit `e1a0fd5`, `equations.tex` lines 66–84 and 220–275,
`eq:wave-psi`, `eq:regular-axis-scalar-traces`. A near-axis trace fixes the
integration constant on each outgoing characteristic, including its representative.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- Retained continuous expansions turn a normalized trace and its stored axis value into an
unnormalized joint trace. Paper `e1a0fd5`, lines 247–261, `eq:regular-axis-scalar-traces`. -/
theorem q1_scalar_axis_trace {ui a : ℝ} {S : SSFields} {f g : ℝ → ℝ → ℝ}
    (ha : (a, a) ∈ axis ui)
    (hg : ContinuousOn (fun p => g p.1 p.2) (pastTriangle ui))
    (hne : ∀ p ∈ pastTriangle ui, g p.1 p.2 ≠ 0)
    (ht : Tendsto (fun p : ℝ × ℝ => f p.1 p.2 / g p.1 p.2)
      (𝓝[pastTriangle ui \ axis ui] (a, a)) (𝓝 (S.phi a a)))
    (hv : f a a / g a a = S.phi a a) :
    Tendsto (fun p : ℝ × ℝ => f p.1 p.2)
      (𝓝[pastTriangle ui \ axis ui] (a, a)) (𝓝 (f a a)) := by
  have hgt := (hg (a, a) (axis_subset_pastTriangle ui ha)).tendsto.mono_left
    (nhdsWithin_mono (a, a)
      (show pastTriangle ui \ axis ui ⊆ pastTriangle ui from sdiff_subset))
  have hp := ht.mul hgt
  have he := (div_eq_iff (hne (a, a) (axis_subset_pastTriangle ui ha))).mp hv
  rw [← he] at hp
  apply hp.congr'
  filter_upwards [self_mem_nhdsWithin] with p hq
  exact div_mul_cancel₀ _ (hne p hq.1)

/-- Joint axis traces fix outgoing transport constants continuously from incoming labels on the
right. Premises are exactly the retained scalar trace, transport equation, and continuous off-
axis forcing. Paper `e1a0fd5`, `eq:wave-psi`, `eq:regular-axis-scalar-traces`, lines 66–84 and
247–261. -/
theorem q1_outgoing_transport_right_cont {ui u v : ℝ} {f F : ℝ → ℝ → ℝ}
    (hu : ui ≤ u) (huv : u < v) (hv : v ≤ 0)
    (hF : ContinuousOn (fun p => F p.1 p.2) (cylinderScalarRegion ui))
    (hprim : ∀ q a b, a ≤ b → outSeg q a b ⊆ offAxis (pastTriangle ui) →
      IntervalPrimitive (f q) (F q) a b)
    (ht : Tendsto (fun p : ℝ × ℝ => f p.1 p.2)
      (𝓝[pastTriangle ui \ axis ui] (u, u)) (𝓝 (f u u))) :
    ContinuousWithinAt (fun q => f q v) {q | u ≤ q ∧ (q, v) ∈ pastTriangle ui} u := by
  let A := {q : ℝ | u ≤ q ∧ (q, v) ∈ pastTriangle ui}
  rw [ContinuousWithinAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, htδ⟩ := Metric.tendsto_nhdsWithin_nhds.mp ht (ε / 4) (by positivity)
  let α := min ((v - u) / 2) (δ / 2)
  have hα : 0 < α := lt_min (by linarith) (by positivity)
  let a := u + α
  let b := u + α / 2
  have hua : u < a := by dsimp [a]; linarith
  have hub : u < b := by dsimp [b]; linarith
  have hba : b < a := by dsimp [b, a]; linarith
  have hav : a < v := by dsimp [a, α]; linarith [min_le_left ((v - u) / 2) (δ / 2)]
  have haδ : dist a u < δ := by
    rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hua)]
    dsimp [a, α]
    linarith [min_le_right ((v - u) / 2) (δ / 2)]
  have htua : dist (f u a) (f u u) < ε / 4 := by
    apply htδ (x := (u, a))
    · exact (cylinderScalarRegion_eq_axisComplement ui ▸
        (show (u, a) ∈ cylinderScalarRegion ui from ⟨hu, hua, hav.le.trans hv⟩))
    · simpa using haδ
  have hrect : Icc ui b ×ˢ Icc a v ⊆ cylinderScalarRegion ui :=
    cylinder_rectangle_subset_region hba hv
  obtain ⟨G, hG, hGe⟩ := cylinder_rectangle_extension (hu.trans hub.le) hav.le (hF.mono hrect)
  have hGc : Continuous (fun z : ℝ × ℝ => G z.1 z.2) := hG
  have hIc : Continuous (fun q : ℝ => ∫ t in a..v, G q t) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := volume) hGc a v
  have hI : Tendsto (fun q => ∫ t in a..v, F q t) (𝓝[A] u)
      (𝓝 (∫ t in a..v, F u t)) := by
    have hEq (q : ℝ) (hq : q ∈ Icc ui b) :
        (∫ t in a..v, G q t) = ∫ t in a..v, F q t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hav.le] at ht
      exact hGe q hq t ht
    have hc := hIc.continuousWithinAt.tendsto (s := A) (x := u)
    rw [hEq u ⟨hu, hub.le⟩] at hc
    apply hc.congr'
    filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (show ∀ᶠ q in 𝓝 u, q < b from Iio_mem_nhds hub)]
      with q hq hqb
    exact hEq q ⟨hu.trans hq.1, hqb.le⟩
  have hIε := Metric.tendsto_nhds.mp hI (ε / 2) (by positivity)
  filter_upwards [self_mem_nhdsWithin, hIε,
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (show ∀ᶠ q in 𝓝 u, q < b from Iio_mem_nhds hub),
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (show ∀ᶠ q in 𝓝 u, dist q u < δ from Metric.ball_mem_nhds u hδ)] with q hq hqI hqb hqδ
  have hqa : q < a := hqb.trans hba
  have htqa : dist (f q a) (f u u) < ε / 4 := by
    apply htδ (x := (q, a))
    · rw [← cylinderScalarRegion_eq_axisComplement]
      exact ⟨hu.trans hq.1, hqa, hav.le.trans hv⟩
    · rw [Prod.dist_eq]
      exact max_lt hqδ haδ
  have hpu := (hprim u a v hav.le
    (outSeg_subset_offAxis hu (huv.trans_le hv) hua hv)).2
  have hpq := (hprim q a v hav.le
    (outSeg_subset_offAxis (hu.trans hq.1) (hqa.trans (hav.trans_le hv)) hqa hv)).2
  have heu : f u v = f u a + ∫ t in a..v, F u t := by linarith
  have heq : f q v = f q a + ∫ t in a..v, F q t := by linarith
  calc
    dist (f q v) (f u v) =
        dist (f q a + ∫ t in a..v, F q t) (f u a + ∫ t in a..v, F u t) := by rw [heu, heq]
    _ ≤ dist (f q a) (f u a) + dist (∫ t in a..v, F q t) (∫ t in a..v, F u t) :=
      dist_add_add_le _ _ _ _
    _ ≤ (dist (f q a) (f u u) + dist (f u u) (f u a)) +
        dist (∫ t in a..v, F q t) (∫ t in a..v, F u t) := by
      gcongr
      exact dist_triangle _ _ _
    _ < ε := by rw [dist_comm (f u u) (f u a)]; linarith

/-- The incoming scalar right-continuity field follows from the remaining standing hypotheses.
Incoming right sections at the axis are singletons. Paper `e1a0fd5`, lines 220–275,
`eq:regular-axis-scalar-traces`, `eq:wave-psi`. -/
theorem dupsi_right_cont_of_rest {ui : ℝ} {S : SSFields}
    (h : StandingWithout_dupsi_right_cont ui S) :
    ∀ p ∈ pastTriangle ui, ContinuousWithinAt (fun u => S.dupsi u p.2)
      {u | p.1 ≤ u ∧ (u, p.2) ∈ pastTriangle ui} p.1 := by
  have hf := q1_forcing_continuous h.toQ1StandingCore h.continuous_r h.continuous_m
    h.continuous_lam h.continuous_nu h.continuous_phi
  intro p hp
  rcases hp.2.2.1.eq_or_lt with he | he
  · apply continuousWithinAt_singleton.mono
    intro u hu
    simp only [mem_singleton_iff]
    have hvu := hu.2.2.2.1
    linarith [hu.1]
  · have ha : (p.1, p.1) ∈ axis ui := ⟨hp.1, hp.2.1, rfl⟩
    exact q1_outgoing_transport_right_cont hp.1 he hp.2.2.2 hf
      h.regularCenter.localBV.dupsi_out
      (q1_scalar_axis_trace ha h.continuous_nu
        (fun q hq => (h.toQ1StandingCore.nu_neg hq).ne)
        (h.regularCenter.axis_dupsi_trace p.1 ha)
        (h.regularCenter.axis_dupsi_value p.1 ha))

end AcExtensionPrinciple

end
