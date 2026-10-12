module

public import AcExtensionPrinciple.Observability.Chart
public import AcExtensionPrinciple.Observability.VolterraBounds

/-!
# Compact triangles in a normalized chart

Paper `e1a0fd5`, `equations.tex` lines 1520–1530. Before the incoming ray
hits the axis, every integration point lies in a compact positive-radius
triangle. Continuous extensions below are auxiliary and agree on that triangle.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- A characteristic triangle with its diagonal boundary. Paper `e1a0fd5`,
`eq:observability-volterra`, lines 1520–1530. -/
@[expose] def chartTriangle (a c : ℝ) : Set (ℝ × ℝ) :=
  {q | a ≤ q.2 ∧ q.2 ≤ q.1 ∧ q.1 ≤ c}

/-- The triangle is closed. Paper `e1a0fd5`, lines 1520–1530. -/
theorem isClosed_chartTriangle (a c : ℝ) : IsClosed (chartTriangle a c) :=
  (isClosed_le continuous_const continuous_snd).inter
    ((isClosed_le continuous_snd continuous_fst).inter
      (isClosed_le continuous_fst continuous_const))

/-- The triangle is compact. Paper `e1a0fd5`, lines 1520–1530. -/
theorem isCompact_chartTriangle (a c : ℝ) : IsCompact (chartTriangle a c) := by
  apply ((isCompact_Icc : IsCompact (Icc a c)).prod
    (isCompact_Icc : IsCompact (Icc a c))).of_isClosed_subset
    (isClosed_chartTriangle a c)
  intro q hq
  exact ⟨⟨hq.1.trans hq.2.1, hq.2.2⟩, ⟨hq.1, hq.2.1.trans hq.2.2⟩⟩

/-- A continuous function on the triangle admits a continuous extension.
Paper `e1a0fd5`, bounded-kernel step at lines 1524–1530. -/
theorem chartTriangle_continuous_extension {f : ℝ × ℝ → ℝ} {a c : ℝ}
    (hf : ContinuousOn f (chartTriangle a c)) :
    ∃ F : ℝ × ℝ → ℝ, Continuous F ∧ ∀ q ∈ chartTriangle a c, F q = f q := by
  obtain ⟨F, hF⟩ := (⟨_, hf.domRestrict⟩ : C(chartTriangle a c, ℝ)).exists_restrict_eq
    (isClosed_chartTriangle a c)
  refine ⟨F, F.continuous, fun q hq => ?_⟩
  exact congrArg (fun G : C(chartTriangle a c, ℝ) => G ⟨q, hq⟩) hF

/-- Positive-radius triangle inside the normalized cylinder. Paper `e1a0fd5`,
`equations.tex` lines 1520–1530. -/
theorem NormalizedChartData.triangle_subset {b T K a c : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (ha : 0 ≤ a) (hac : a ≤ c)
    (hc : c ≤ T) (hg : h.g c < a) :
    chartTriangle a c ⊆ chartInterior (chartCylinder h.g T) S := by
  intro q hq
  have hs : q.1 ∈ Icc 0 T := ⟨ha.trans (hq.1.trans hq.2.1), hq.2.2.trans hc⟩
  have hgc := h.monotone_g hs ⟨ha.trans hac, hc⟩ hq.2.2
  have hgt : h.g q.1 < q.2 := hgc.trans_lt (hg.trans_le hq.1)
  have hmem : q ∈ chartCylinder h.g T := ⟨hs.1, hs.2, hgt.le, hq.2.1⟩
  exact ⟨hmem, h.radius_pos hmem hgt⟩

/-- Each boundary point has a positive-radius triangular neighborhood. Paper
`e1a0fd5`, local trace justification at `equations.tex` line 1522. -/
theorem NormalizedChartData.exists_boundary_triangle {b T K x : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hx : x ∈ Icc 0 T) :
    ∃ a c, 0 ≤ a ∧ a ≤ c ∧ c ≤ T ∧ h.g c < a ∧ Icc a c ∈ 𝓝[Icc 0 T] x := by
  have hgap : 0 < x - h.g x := sub_pos.mpr (h.axis_before_boundary x hx)
  obtain ⟨η, hη, hηg⟩ := Metric.continuousAt_iff.mp h.continuous_g.continuousAt
    ((x - h.g x) / 4) (by positivity)
  let δ := min η ((x - h.g x) / 4) / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδη : δ < η := by dsimp [δ]; linarith [min_le_left η ((x - h.g x) / 4)]
  have hδgap : δ < (x - h.g x) / 4 := by
    dsimp [δ]; linarith [min_le_right η ((x - h.g x) / 4)]
  let a := max 0 (x - δ)
  let c := min T (x + δ)
  have hax : a ≤ x := max_le hx.1 (by linarith)
  have hxc : x ≤ c := le_min hx.2 (by linarith)
  have hcnear : dist c x < η := by
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hxc)]
    exact (by dsimp [c]; linarith [min_le_right T (x + δ)] : c - x ≤ δ).trans_lt hδη
  have hgc : h.g c < a := by
    have hh := (abs_lt.mp (show |h.g c - h.g x| < (x - h.g x) / 4 from
      by simpa [Real.dist_eq] using hηg hcnear)).2
    have ha : x - δ ≤ a := le_max_right _ _
    linarith
  refine ⟨a, c, le_max_left _ _, hax.trans hxc, min_le_left _ _, hgc, ?_⟩
  apply Filter.mem_of_superset (inter_mem (mem_nhdsWithin_of_mem_nhds
    (Metric.ball_mem_nhds x hδ)) self_mem_nhdsWithin)
  rintro y ⟨hy, hyI⟩
  have hyδ : |y - x| < δ := hy
  rcases abs_lt.mp hyδ with ⟨hylo, hyhi⟩
  exact ⟨max_le hyI.1 (by linarith), le_min hyI.2 (by linarith)⟩

/-- Local almost everywhere statements on a compact set combine globally.
Paper `e1a0fd5`, local-to-cylinder step at line 1522. -/
theorem chart_ae_of_local {P : ℝ → Prop} {C : Set ℝ} (hC : IsCompact C)
    (hlocal : ∀ x ∈ C, ∃ U ∈ 𝓝[C] x, ∀ᵐ y ∂volume, y ∈ U → P y) :
    ∀ᵐ y ∂volume, y ∈ C → P y := by
  apply IsCompact.induction_on hC (p := fun U => ∀ᵐ y ∂volume, y ∈ U → P y)
  · exact ae_of_all _ (by simp)
  · intro U V hUV hV
    exact hV.mono (fun y hy hU => hy (hUV hU))
  · intro U V hU hV
    filter_upwards [hU, hV] with y hyU hyV
    exact fun hy => hy.elim hyU hyV
  · exact hlocal

/-- Ordered outgoing segments of the triangle. Paper `e1a0fd5`,
`eq:observability-volterra`, lines 1520–1530. -/
theorem chartTriangle_out_subset {a c s t z : ℝ} (ha : a ≤ t) (hz : z ≤ s)
    (hs : s ≤ c) : outSeg s t z ⊆ chartTriangle a c := by
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  simp only [mem_singleton_iff] at hx
  subst x
  exact ⟨ha.trans hy.1, hy.2.trans hz, hs⟩

/-- Ordered incoming segments of the triangle. Paper `e1a0fd5`,
`eq:observability-volterra`, lines 1520–1530. -/
theorem chartTriangle_in_subset {a c t s z : ℝ} (ha : a ≤ t) (ht : t ≤ s)
    (hz : z ≤ c) : inSeg t s z ⊆ chartTriangle a c := by
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  simp only [mem_singleton_iff] at hy
  subst y
  exact ⟨ha, ht.trans hx.1, hx.2.trans hz⟩

/-- Two characteristic primitives give the increment of the diagonal trace.
Paper `e1a0fd5`, AC and chain-rule justification at line 1522. -/
theorem chart_diagonal_increment {f U V : ℝ → ℝ → ℝ} {a c : ℝ}
    (hU : IntervalPrimitive (fun s => f s a) (fun s => U s a) a c)
    (hV : IntervalPrimitive (f c) (V c) a c) :
    f c c - f a a = (∫ s in a..c, U s a) + ∫ t in a..c, V c t := by
  linarith [hU.2, hV.2]

/-- Uniformly bounded characteristic derivatives make the diagonal trace
Lipschitz, and hence AC. Paper `e1a0fd5`, line 1522. -/
theorem chart_diagonal_lipschitz {f U V : ℝ → ℝ → ℝ} {a c M : ℝ}
    (hM : 0 ≤ M)
    (hU : ∀ x y, a ≤ x → x ≤ y → y ≤ c →
      IntervalPrimitive (fun s => f s x) (fun s => U s x) x y)
    (hV : ∀ x y, a ≤ x → x ≤ y → y ≤ c → IntervalPrimitive (f y) (V y) x y)
    (hbound : ∀ s t, (s, t) ∈ chartTriangle a c → |U s t| ≤ M ∧ |V s t| ≤ M) :
    LipschitzOnWith ⟨2 * M, by positivity⟩ (fun s => f s s) (Icc a c) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  wlog hxy : x ≤ y generalizing x y
  · simpa [dist_comm] using this y hy x hx (le_of_not_ge hxy)
  have hi := chart_diagonal_increment (hU x y hx.1 hxy hy.2) (hV x y hx.1 hxy hy.2)
  have hu : |∫ s in x..y, U s x| ≤ M * |y - x| := by
    simpa only [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun s => U s x) (a := x) (b := y) (fun s hs => by
        rw [uIoc_of_le hxy] at hs
        exact (hbound s x ⟨hx.1, hs.1.le, hs.2.trans hy.2⟩).1)
  have hv : |∫ t in x..y, V y t| ≤ M * |y - x| := by
    simpa only [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun t => V y t) (a := x) (b := y) (fun t ht => by
        rw [uIoc_of_le hxy] at ht
        exact (hbound y t ⟨hx.1.trans ht.1.le, ht.2, hy.2⟩).2)
  rw [Real.dist_eq, abs_sub_comm, hi, Real.dist_eq, abs_sub_comm]
  change |(∫ s in x..y, U s x) + ∫ t in x..y, V y t| ≤ 2 * M * |y - x|
  exact (abs_add_le _ _).trans (by linarith)

/-- Continuous characteristic derivative traces give the diagonal chain rule.
Paper `e1a0fd5`, local AC/BV justification at line 1522. -/
theorem chart_diagonal_hasDerivAt {f U V : ℝ → ℝ → ℝ} {a c x : ℝ}
    (hx : x ∈ Ioo a c)
    (hU : ∀ l r, a ≤ l → l ≤ r → r ≤ c →
      IntervalPrimitive (fun s => f s l) (fun s => U s l) l r)
    (hV : ∀ l r, a ≤ l → l ≤ r → r ≤ c → IntervalPrimitive (f r) (V r) l r)
    (hcU : ContinuousWithinAt (fun q : ℝ × ℝ => U q.1 q.2) (chartTriangle a c) (x, x))
    (hcV : ContinuousWithinAt (fun q : ℝ × ℝ => V q.1 q.2) (chartTriangle a c) (x, x)) :
    HasDerivAt (fun s => f s s) (U x x + V x x) x := by
  apply HasDerivAt.of_isLittleO
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δU, hδU, hUb⟩ := Metric.continuousWithinAt_iff.mp hcU (ε / 2) (by positivity)
  obtain ⟨δV, hδV, hVb⟩ := Metric.continuousWithinAt_iff.mp hcV (ε / 2) (by positivity)
  filter_upwards [Ioo_mem_nhds hx.1 hx.2,
    Metric.ball_mem_nhds x (lt_min hδU hδV)] with y hy hdist
  change |y - x| < min δU δV at hdist
  have hdistU : |y - x| < δU := (lt_min_iff.mp hdist).1
  have hdistV : |y - x| < δV := (lt_min_iff.mp hdist).2
  have hnear {s t : ℝ} (hs : s ∈ uIcc x y) (ht : t ∈ uIcc x y) :
      dist (s, t) (x, x) ≤ |y - x| := by
    have hcoord {z : ℝ} (hz : z ∈ uIcc x y) : |z - x| ≤ |y - x| := by
      rcases le_total x y with h | h
      · rw [uIcc_of_le h] at hz
        rw [abs_of_nonneg (sub_nonneg.mpr hz.1), abs_of_nonneg (sub_nonneg.mpr h)]
        linarith [hz.2]
      · rw [uIcc_of_ge h] at hz
        rw [abs_of_nonpos (sub_nonpos.mpr hz.2), abs_of_nonpos (sub_nonpos.mpr h)]
        linarith [hz.1]
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    exact max_le (hcoord hs) (hcoord ht)
  have hu {s t : ℝ} (hq : (s, t) ∈ chartTriangle a c)
      (hs : s ∈ uIcc x y) (ht : t ∈ uIcc x y) : |U s t - U x x| ≤ ε / 2 := by
    have hb := (hUb hq ((hnear hs ht).trans_lt hdistU)).le
    simpa only [Real.dist_eq] using hb
  have hv {s t : ℝ} (hq : (s, t) ∈ chartTriangle a c)
      (hs : s ∈ uIcc x y) (ht : t ∈ uIcc x y) : |V s t - V x x| ≤ ε / 2 := by
    have hb := (hVb hq ((hnear hs ht).trans_lt hdistV)).le
    simpa only [Real.dist_eq] using hb
  have hestimate {l r : ℝ} (hl : l ∈ Icc a c) (hr : r ∈ Icc a c) (hlr : l ≤ r)
      (hlxy : l ∈ uIcc x y) (hrxy : r ∈ uIcc x y) :
      |f r r - f l l - (r - l) * (U x x + V x x)| ≤ ε * |r - l| := by
    have hi := chart_diagonal_increment (hU l r hl.1 hlr hr.2) (hV l r hl.1 hlr hr.2)
    have hu' : |∫ s in l..r, U s l - U x x| ≤ ε / 2 * |r - l| := by
      simpa only [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_of_norm_le_const
        (f := fun s => U s l - U x x) (a := l) (b := r) (fun s hs => by
          rw [uIoc_of_le hlr] at hs
          exact hu ⟨hl.1, hs.1.le, hs.2.trans hr.2⟩
            (uIcc_subset_uIcc hlxy hrxy (by simpa [uIcc_of_le hlr] using ⟨hs.1.le, hs.2⟩)) hlxy)
    have hv' : |∫ t in l..r, V r t - V x x| ≤ ε / 2 * |r - l| := by
      simpa only [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_of_norm_le_const
        (f := fun t => V r t - V x x) (a := l) (b := r) (fun t ht => by
          rw [uIoc_of_le hlr] at ht
          exact hv ⟨hl.1.trans ht.1.le, ht.2, hr.2⟩ hrxy
            (uIcc_subset_uIcc hlxy hrxy (by simpa [uIcc_of_le hlr] using ⟨ht.1.le, ht.2⟩)))
    have he : f r r - f l l - (r - l) * (U x x + V x x) =
        (∫ s in l..r, U s l - U x x) + ∫ t in l..r, V r t - V x x := by
      rw [intervalIntegral.integral_sub (hU l r hl.1 hlr hr.2).1 intervalIntegrable_const,
        intervalIntegral.integral_sub (hV l r hl.1 hlr hr.2).1 intervalIntegrable_const]
      simp only [intervalIntegral.integral_const, smul_eq_mul]
      linarith [hi]
    rw [he]
    exact (abs_add_le _ _).trans (by linarith)
  simp only [Real.norm_eq_abs, smul_eq_mul]
  rcases le_total x y with hxy | hyx
  · exact hestimate ⟨hx.1.le, hx.2.le⟩ ⟨hy.1.le, hy.2.le⟩ hxy
      (left_mem_uIcc) (right_mem_uIcc)
  · have he := hestimate ⟨hy.1.le, hy.2.le⟩ ⟨hx.1.le, hx.2.le⟩ hyx
      (right_mem_uIcc) (left_mem_uIcc)
    have heq : f y y - f x x - (y - x) * (U x x + V x x) =
        -(f x x - f y y - (x - y) * (U x x + V x x)) := by ring
    rw [heq, abs_neg]
    exact he.trans_eq (by rw [abs_sub_comm])

end AcExtensionPrinciple

end
