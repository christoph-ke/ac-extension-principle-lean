module

public import AcExtensionPrinciple.Minimal.OneSidedScalarRays
public import AcExtensionPrinciple.Minimal.ScalarInterior

/-!
# Local scalar bounds and vanishing-variation control

Paper `e1a0fd5`, `equations.tex` lines 220–261,
`eq:axis-vanishing-variation`, `eq:regular-axis-scalar-traces`.
Bounds use a positive-radius anchor, so no joint axis trace enters.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- An extended variation tending to zero is uniformly small on a right interval.
Paper `e1a0fd5`, lines 224–237, `eq:axis-vanishing-variation`. -/
theorem oneSided_variation_small {F : ℝ → ℝ≥0∞} {B : ℝ} (hB : 0 < B)
    (ht : Tendsto F (𝓝[>] 0) (𝓝 0)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε ∈ Ioo 0 δ, F ε ≤ ENNReal.ofReal B := by
  have he := ht.eventually (Iio_mem_nhds (ENNReal.ofReal_pos.mpr hB))
  obtain ⟨δ, hδ, hb⟩ := (mem_nhdsGT_iff_exists_mem_Ioc_Ioo_subset zero_lt_one).mp he
  exact ⟨δ, hδ.1, fun ε hε => (hb hε).le⟩

/-- Variation on an open interval controls its continuous right endpoint.
Paper `e1a0fd5`, lines 224–237, `eq:axis-vanishing-variation`. -/
theorem oneSided_variation_right_endpoint {f : ℝ → ℝ} {u v a B : ℝ}
    (huv : u < v) (hva : v < a) (hB : 0 ≤ B)
    (hv : eVariationOn f (Ioo u a) ≤ ENNReal.ofReal B)
    (ht : Tendsto f (𝓝[<] a) (𝓝 (f a))) : dist (f v) (f a) ≤ B := by
  apply le_of_tendsto (tendsto_const_nhds.dist ht)
  filter_upwards [Ioo_mem_nhdsLT (huv.trans hva)] with w hw
  apply (ENNReal.ofReal_le_ofReal_iff hB).mp
  rw [← edist_dist]
  exact (eVariationOn.edist_le f (s := Ioo u a) ⟨huv, hva⟩ hw).trans hv

/-- Variation on an open interval controls its continuous left endpoint.
Paper `e1a0fd5`, lines 224–237, `eq:axis-vanishing-variation`. -/
theorem oneSided_variation_left_endpoint {f : ℝ → ℝ} {a u v B : ℝ}
    (hau : a < u) (huv : u < v) (hB : 0 ≤ B)
    (hv : eVariationOn f (Ioo a v) ≤ ENNReal.ofReal B)
    (ht : Tendsto f (𝓝[>] a) (𝓝 (f a))) : dist (f u) (f a) ≤ B := by
  apply le_of_tendsto (tendsto_const_nhds.dist ht)
  filter_upwards [Ioo_mem_nhdsGT (hau.trans huv)] with w hw
  apply (ENNReal.ofReal_le_ofReal_iff hB).mp
  rw [← edist_dist]
  exact (eVariationOn.edist_le f (s := Ioo a v) ⟨hau, huv⟩ hw).trans hv

/-- A positive-radius outgoing anchor and uniform scalar variation bound φ
on a compact triangle, including its stored axis values. Paper `e1a0fd5`,
lines 220–222, Luk–Oh Definition 2.1(4). -/
theorem StandingAssumptions.oneSided_phi_local_bound {ui W V : ℝ} {S : SSFields}
    (h : StandingAssumptions ui S) (_hui : ui ≤ W) (hWV : W < V) (hV : V < 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p ∈ pastTriangle ui, p.1 ≤ W → p.2 ≤ V →
      |S.phi p.1 p.2| ≤ B := by
  have hc : ContinuousOn (fun u => S.phi u V) (Icc ui W) :=
    h.continuous_phi_offAxis.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun u hu => ⟨hu.1, hu.2.trans_lt hWV, hV.le⟩)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  let K := (Icc ui V ×ˢ Icc ui V) ∩ {p : ℝ × ℝ | p.1 ≤ p.2}
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc).inter_right
    (isClosed_le continuous_fst continuous_snd)
  have hKQ : K ⊆ pastTriangle ui := fun p hp =>
    ⟨hp.1.1.1, hp.1.1.2.trans_lt hV, hp.2, hp.1.2.2.trans hV.le⟩
  obtain ⟨C, hC, _⟩ := h.regularCenter.localBV.scalar_variation K hK hKQ
  refine ⟨|M| + |C|, by positivity, ?_⟩
  intro p hp hpW hpV
  have hpui : ui ≤ p.2 := hp.1.trans hp.2.2.1
  have hp1V : p.1 ≤ V := hpW.trans hWV.le
  have hs : outSeg p.1 p.1 V ⊆ K := by
    intro q hq
    have hqu : q.1 = p.1 := mem_singleton_iff.mp hq.1
    change (q.1 ∈ Icc ui V ∧ q.2 ∈ Icc ui V) ∧ q.1 ≤ q.2
    rw [hqu]
    exact ⟨⟨⟨hp.1, hp1V⟩, ⟨hp.1.trans hq.2.1, hq.2.2⟩⟩, hq.2.1⟩
  have hd : dist (S.phi p.1 p.2) (S.phi p.1 V) ≤ |C| := by
    apply (ENNReal.ofReal_le_ofReal_iff (abs_nonneg C)).mp
    rw [← edist_dist]
    exact (eVariationOn.edist_le (S.phi p.1) (s := Icc p.1 V)
      ⟨hp.2.2.1, hpV⟩ ⟨hp1V, le_rfl⟩).trans
      ((hC p.1 p.1 V hp1V hs).trans (ENNReal.ofReal_le_ofReal (le_abs_self C)))
  have hb : |S.phi p.1 V| ≤ |M| := by
    simpa only [Real.norm_eq_abs] using (hM p.1 ⟨hp.1, hpW⟩).trans (le_abs_self M)
  calc
    _ ≤ dist (S.phi p.1 p.2) (S.phi p.1 V) + |S.phi p.1 V| := by
      simpa only [Real.norm_eq_abs, dist_eq_norm, add_comm] using
        norm_le_insert' (S.phi p.1 p.2) (S.phi p.1 V)
    _ ≤ |C| + |M| := add_le_add hd hb
    _ = _ := add_comm _ _

/-- Scalar restrictions are continuous on outgoing rays away from their axis endpoint.
Paper `e1a0fd5`, lines 220–261, `eq:wave-psi`. -/
theorem StandingAssumptions.oneSided_phi_out_interior {ui u : ℝ} {S : SSFields}
    (h : StandingAssumptions ui S) (hu : ui ≤ u) :
    ContinuousOn (S.phi u) (Ioc u 0) :=
  h.continuous_phi_offAxis.comp (continuous_const.prodMk continuous_id).continuousOn
    (fun _ hv => ⟨hu, hv.1, hv.2⟩)

/-- Scalar restrictions are continuous on incoming rays away from their axis endpoint.
Paper `e1a0fd5`, lines 220–261, `eq:wave-psi`. -/
theorem StandingAssumptions.oneSided_phi_in_interior {ui v : ℝ} {S : SSFields}
    (h : StandingAssumptions ui S) (hv : v ≤ 0) :
    ContinuousOn (fun u => S.phi u v) (Ico ui v) :=
  h.continuous_phi_offAxis.comp (continuous_id.prodMk continuous_const).continuousOn
    (fun _ hu => ⟨hu.1, hu.2, hv⟩)

/-- Points in the characteristic square between u and v stay as close to (a,a)
as (u,v). Paper `e1a0fd5`, lines 224–261, regular-axis neighborhoods. -/
theorem oneSided_box_near {u v a δ x y : ℝ}
    (hp : dist (u, v) (a, a) < δ) (hx : x ∈ Icc u v) (hy : y ∈ Icc u v) :
    dist (x, y) (a, a) < δ := by
  rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq, abs_lt, abs_lt] at hp ⊢
  constructor <;> constructor <;> dsimp only at * <;> linarith [hx.1, hx.2, hy.1, hy.2]

/-- A compact lower expansion bound gives the corresponding lower radius bound.
Paper `e1a0fd5`, lines 220–222, `eq:radius-from-axis`. -/
theorem StandingAssumptions.oneSided_radius_lower {ui u v c : ℝ} {S : SSFields}
    (h : StandingAssumptions ui S) (hp : (u, v) ∈ pastTriangle ui) (huv : u ≤ v)
    (hc : ∀ t ∈ Icc u v, c ≤ S.lam u t) : c * (v - u) ≤ S.r u v := by
  have hi := h.regularCenter.localBV.radius_out u u v huv
    (outSeg_subset_triangle hp.1 hp.2.1 le_rfl hp.2.2.2)
  have hr0 := (h.regularCenter.localBV.axis_values u
    ⟨hp.1, hp.2.1, le_rfl, hp.2.1.le⟩).1
  have he : (∫ t in u..v, S.lam u t) = S.r u v := by linarith [hi.2]
  rw [← he]
  have hb := intervalIntegral.integral_mono_on huv intervalIntegrable_const hi.1 hc
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using hb

end AcExtensionPrinciple

end
