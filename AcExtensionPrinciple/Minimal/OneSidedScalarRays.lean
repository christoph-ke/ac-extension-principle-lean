module

public import AcExtensionPrinciple.Minimal.OneSidedPaths
public import AcExtensionPrinciple.Minimal.Geometry
public import AcExtensionPrinciple.Solution.EndpointPrimitive

/-!
# Scalar traces along the two characteristics

Paper `e1a0fd5`, `equations.tex` lines 220–261,
`eq:regular-axis-scalar-traces`. The expansion-sum limit and retained ν continuity
give the outgoing λ trace without joint scalar traces. Slopes of the r and ψ
primitives then recover the scalar traces on fixed characteristics.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- A primitive's left slope tends to the left limit of its integrand.
Paper `e1a0fd5`, lines 220–261, integral equations at the regular axis. -/
theorem oneSided_intervalPrimitive_left_slope {f g : ℝ → ℝ} {a b c : ℝ}
    (hab : a < b) (hp : ∀ x ∈ Icc a b, IntervalPrimitive f g x b)
    (hg : Tendsto g (𝓝[<] b) (𝓝 c)) :
    Tendsto (fun x => (f x - f b) / (x - b)) (𝓝[<] b) (𝓝 c) := by
  have hi := (hp a ⟨le_rfl, hab.le⟩).1
  have hev : ∀ᶠ x in 𝓝[≤] b, x ∈ Ioc a b := by
    filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (show ∀ᶠ x in 𝓝 b, a < x from Ioi_mem_nhds hab)] with x hx hxa
    exact ⟨hxa, hx⟩
  have hm : StronglyMeasurableAtFilter g (𝓝[≤] b) volume :=
    ⟨Ioc a b, hev, hi.1.aestronglyMeasurable⟩
  have hid : Tendsto (fun x : ℝ => x) (𝓝[≤] b ⊓ ae volume) (𝓝[<] b) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_id.mono_left (inf_le_left.trans nhdsWithin_le_nhds), ?_⟩
    have hle : ∀ᶠ x : ℝ in 𝓝[≤] b ⊓ ae volume, x ≤ b :=
      Filter.Eventually.filter_mono inf_le_left
        (self_mem_nhdsWithin : ∀ᶠ x : ℝ in 𝓝[≤] b, x ≤ b)
    have hne : ∀ᶠ x : ℝ in 𝓝[≤] b ⊓ ae volume, x ≠ b :=
      Filter.Eventually.filter_mono inf_le_right (volume.ae_ne b)
    filter_upwards [hle, hne] with x hx hxb
    exact lt_of_le_of_ne hx hxb
  have hd : HasDerivWithinAt (fun x => ∫ s in x..b, g s) (-c) (Iic b) b :=
    intervalIntegral.integral_hasDerivWithinAt_of_tendsto_ae_left
      (IntervalIntegrable.refl) hm (hg.comp hid)
  have hd' : HasDerivWithinAt f c (Iic b) b := by
    have hn := hd.neg.add_const (f b)
    simp only [neg_neg] at hn
    apply hn.congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin,
        Filter.Eventually.filter_mono nhdsWithin_le_nhds
          (show ∀ᶠ x in 𝓝 b, a < x from Ioi_mem_nhds hab)] with x hx hxa
      have he := (hp x ⟨hxa.le, hx⟩).2
      dsimp only [Pi.neg_apply] at ⊢
      linarith
    · simp
  simpa only [slope_fun_def_field] using
    (hasDerivWithinAt_iff_tendsto_slope' (by simp)).mp (hd'.mono Iio_subset_Iic_self)

/-- Retained ν continuity fixes the outgoing λ trace from the expansion-sum limit.
Paper `e1a0fd5`, lines 222, 243–245, `eq:regular-axis`. -/
theorem RegularCenterLocalACBV.oneSided_lam_out {ui a : ℝ} {S : SSFields}
    (h : RegularCenterLocalACBV ui S) (ha : (a, a) ∈ axis ui) :
    Tendsto (S.lam a) (𝓝[>] a) (𝓝 (S.lam a a)) := by
  have hp := axis_subset_pastTriangle ui ha
  have hn := (h.continuous_nu (a, a) hp).tendsto.comp
    ((oneSided_outgoing_path ha).mono_right (nhdsWithin_mono _ sdiff_subset))
  have hs := h.localBV.expansion_axis_limit a hp
  have ht : Tendsto (fun ε => S.lam a (a + ε)) (𝓝[>] 0) (𝓝 (S.lam a a)) := by
    simpa only [Function.comp_def, add_sub_cancel_left, zero_sub,
      h.axis_expansions a ha, neg_neg] using hs.sub hn
  exact oneSided_outgoing_reparam ht

/-- An outgoing normalized derivative trace recovers φ on that same outgoing ray.
No joint trace or φ continuity is used. Paper `e1a0fd5`, lines 247–261,
`eq:regular-axis-scalar-traces`, `eq:radius-from-axis`, `eq:wave-psi`. -/
theorem StandingAssumptions.oneSided_phi_out {ui a : ℝ} {S : SSFields}
    (h : StandingAssumptions ui S) (ha : (a, a) ∈ axis ui) :
    Tendsto (S.phi a) (𝓝[>] a) (𝓝 (S.phi a a)) := by
  have hl := h.regularCenter.oneSided_lam_out ha
  have hq := oneSided_outgoing_reparam (f := fun v => S.dvpsi a v / S.lam a v)
    (h.regularCenter.axis_dvpsi_out a ha)
  have hd : Tendsto (S.dvpsi a) (𝓝[>] a) (𝓝 (S.phi a a * S.lam a a)) := by
    apply (hq.mul hl).congr'
    filter_upwards [Ioo_mem_nhdsGT ha.2.1] with v hv
    exact div_mul_cancel₀ _ (h.lam_pos (p := (a, v))
      ⟨ha.1, ha.2.1, hv.1.le, hv.2.le⟩).ne'
  have hr := intervalPrimitive_right_slope ha.2.1 (fun x hx =>
    h.regularCenter.localBV.radius_out a a x hx.1
      (outSeg_subset_triangle ha.1 ha.2.1 le_rfl hx.2)) hl
  have hψ := intervalPrimitive_right_slope ha.2.1 (fun x hx =>
    h.regularCenter.localBV.psi_out a a x hx.1
      (outSeg_subset_triangle ha.1 ha.2.1 le_rfl hx.2)) hd
  have hav := h.regularCenter.localBV.axis_values a (axis_subset_pastTriangle ui ha)
  simp only [hav.1, zero_mul, sub_zero] at hr hψ
  have ht := hψ.div hr (h.lam_pos (axis_subset_pastTriangle ui ha)).ne'
  rw [mul_div_cancel_right₀ _ (h.lam_pos (axis_subset_pastTriangle ui ha)).ne'] at ht
  apply ht.congr'
  filter_upwards [Ioo_mem_nhdsGT ha.2.1] with v hv
  have hp : (a, v) ∈ pastTriangle ui := ⟨ha.1, ha.2.1, hv.1.le, hv.2.le⟩
  change (S.r a v * S.phi a v / (v - a)) / (S.r a v / (v - a)) = S.phi a v
  field_simp [(h.r_pos hp hv.1).ne', (sub_pos.mpr hv.1).ne']

/-- The incoming normalized derivative trace recovers φ on that incoming ray.
The initial vertex is excluded only because its incoming source filter is bottom.
Paper `e1a0fd5`, lines 247–262, `eq:regular-axis-one-sided-traces`, `eq:regular-axis-scalar-traces`, `eq:wave-psi`. -/
theorem StandingAssumptions.oneSided_phi_in {ui a : ℝ} {S : SSFields}
    (h : StandingAssumptions ui S) (ha : (a, a) ∈ axis ui) (hia : ui < a) :
    Tendsto (fun u => S.phi u a) (𝓝[<] a) (𝓝 (S.phi a a)) := by
  have hpair : Tendsto (fun u : ℝ => (u, a)) (𝓝[<] a)
      (𝓝[pastTriangle ui] (a, a)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨(tendsto_id.mono_left nhdsWithin_le_nhds).prodMk_nhds
      tendsto_const_nhds, ?_⟩
    filter_upwards [Ioo_mem_nhdsLT hia] with u hu
    exact ⟨hu.1.le, hu.2.trans ha.2.1, hu.2.le, ha.2.1.le⟩
  have hn := (h.regularCenter.continuous_nu (a, a)
    (axis_subset_pastTriangle ui ha)).tendsto.comp hpair
  have hq := oneSided_incoming_reparam (f := fun u => S.dupsi u a / S.nu u a)
    hia (h.regularCenter.axis_dupsi_in a ha)
  have hd : Tendsto (fun u => S.dupsi u a) (𝓝[<] a)
      (𝓝 (S.phi a a * S.nu a a)) := by
    apply (hq.mul hn).congr'
    filter_upwards [Ioo_mem_nhdsLT hia] with u hu
    exact div_mul_cancel₀ _ (h.nu_neg (p := (u, a))
      ⟨hu.1.le, hu.2.trans ha.2.1, hu.2.le, ha.2.1.le⟩).ne
  have hr := oneSided_intervalPrimitive_left_slope hia (fun x hx =>
    h.regularCenter.localBV.radius_in a x a hx.2
      (inSeg_subset_triangle hx.1 ha.2.1 le_rfl ha.2.1.le)) hn
  have hψ := oneSided_intervalPrimitive_left_slope hia (fun x hx =>
    h.regularCenter.localBV.psi_in a x a hx.2
      (inSeg_subset_triangle hx.1 ha.2.1 le_rfl ha.2.1.le)) hd
  have hav := h.regularCenter.localBV.axis_values a (axis_subset_pastTriangle ui ha)
  simp only [hav.1, zero_mul, sub_zero] at hr hψ
  have ht := hψ.div hr (h.nu_neg (axis_subset_pastTriangle ui ha)).ne
  rw [mul_div_cancel_right₀ _ (h.nu_neg (axis_subset_pastTriangle ui ha)).ne] at ht
  apply ht.congr'
  filter_upwards [Ioo_mem_nhdsLT hia] with u hu
  have hp : (u, a) ∈ pastTriangle ui :=
    ⟨hu.1.le, hu.2.trans ha.2.1, hu.2.le, ha.2.1.le⟩
  change (S.r u a * S.phi u a / (u - a)) / (S.r u a / (u - a)) = S.phi u a
  field_simp [(h.r_pos hp hu.2).ne', (sub_neg.mpr hu.2).ne]

end AcExtensionPrinciple

end
