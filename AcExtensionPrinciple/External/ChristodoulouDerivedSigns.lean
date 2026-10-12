module

public import AcExtensionPrinciple.External.ChristodoulouDerivedMass

/-!
# Sign, lapse, and incoming-axis conclusions from the Christodoulou BV class

Paper `e1a0fd5`, `equations.tex` `eq:hawking-mass`, `eq:regular-axis`,
lines 220–275 and 1411; Christodoulou pp. 1135–1138 and 1146–1148.
`ChristodoulouBV` implies these conditions on domains of development with A = adjacentAxis D.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- The homogeneous coefficient of the outgoing ν equation is integrable
strictly off the axis. Paper `e1a0fd5`, `eq:radius`, lines 220–275;
Christodoulou (1.14b), pp. 1147–1148. The mass-gap premises have been derived. -/
theorem ChristodoulouBV.nu_coefficient_integrable {D : Set (ℝ × ℝ)} {S : SSFields}
    (h : ChristodoulouBV D (adjacentAxis D) S) (hD : domainOfDevelopment D)
    {u a b : ℝ} (hab : a ≤ b) (hs : outSeg u a b ⊆ D) :
    IntervalIntegrable (fun v => S.mu u v * S.lam u v /
      ((1 - S.mu u v) * S.r u v)) volume a b := by
  have hr := (h.1.radius_ac_out hab hs).continuousOn
  have hm := (h.1.mass_ac_out hab hs).continuousOn
  have hpoint (v : ℝ) (hv : v ∈ uIcc a b) : (u, v) ∈ D :=
    hs ⟨by simp, by simpa only [uIcc_of_le hab] using hv⟩
  have hmu : ContinuousOn (S.mu u) (uIcc a b) :=
    (continuousOn_const.mul hm).div hr (fun v hv => (h.r_pos hD (hpoint v hv)).ne')
  have hweight : ContinuousOn (fun v => S.mu u v /
      ((1 - S.mu u v) * S.r u v)) (uIcc a b) := by
    apply hmu.div ((continuousOn_const.sub hmu).mul hr)
    intro v hv
    exact mul_ne_zero (sub_pos.mpr (h.mu_lt_one hD (hpoint v hv))).ne'
      (h.r_pos hD (hpoint v hv)).ne'
  convert (h.1.radius_out u a b hab hs).1.mul_continuousOn hweight using 1
  ext v
  ring

/-- Negative incoming expansion follows from its outgoing axis cancellation
and the homogeneous outgoing equation. Paper `e1a0fd5`, line 66, `eq:radius`,
lines 220–275 and 1411; Christodoulou p. 1148, (1.14b) and definition item 2. -/
theorem ChristodoulouBV.nu_neg {D : Set (ℝ × ℝ)} {S : SSFields}
    (h : ChristodoulouBV D (adjacentAxis D) S) (hD : domainOfDevelopment D)
    {p : ℝ × ℝ} (hp : p ∈ D) : S.nu p.1 p.2 < 0 := by
  rcases p with ⟨u, v⟩
  obtain ⟨c, N, hc, hb⟩ := h.2.expansion_bounds
  have ht := (h.1.expansion_axis_limit u (hD.outgoing_axis hp)).mono_left
    (le_inf le_rfl (hD.outgoing_filter hp))
  obtain ⟨a, hsum, ha⟩ :=
    ((ht.eventually (Iio_mem_nhds hc)).and (Ioo_mem_nhdsGT (hD.1 hp).2)).exists
  have hpa := hD.outgoing hp ⟨ha.1, ha.2.le⟩
  have hna : S.nu u a < 0 := by
    have hl := (hb (u, a) ⟨mem_univ _, hpa⟩).1
    linarith
  have hs := hD.outSeg hp ha.1 le_rfl
  let q (w : ℝ) := S.mu u w * S.lam u w / ((1 - S.mu u w) * S.r u w)
  have hq : IntervalIntegrable q volume a v := h.nu_coefficient_integrable hD ha.2.le hs
  have hd := intervalPrimitive_ae_hasDerivAt (g := S.radiusCoeff u) ha.2.le
    (fun x hx => h.1.nu_out u a x hx.1
      (fun p hp => hs ⟨hp.1, hp.2.1, hp.2.2.trans hx.2⟩))
  have hODE : ∀ᵐ w, w ∈ Ioo a v →
      HasDerivAt (S.nu u) (-(-q w) * S.nu u w + 0) w := by
    filter_upwards [hd] with w hdw
    intro hw
    convert hdw hw using 1
    simp only [SSFields.radiusCoeff, q]
    ring
  have he := (chr_weighted_primitive ha.2.le (h.1.nu_ac_out ha.2.le hs)
    hq.neg hODE).2
  simp only [Pi.neg_apply, intervalIntegral.integral_same, Real.exp_zero, one_mul, mul_zero,
    intervalIntegral.integral_zero] at he
  have hneg : Real.exp (∫ t in a..v, -q t) * S.nu u v < 0 := by linarith
  exact neg_of_mul_neg_right hneg (Real.exp_pos _).le

/-- The reconstructed lapse square is a positive finite real number.
Paper `e1a0fd5`, `eq:hawking-mass`, lines 220–275 and 1411;
Christodoulou (1.5), pp. 1133–1135 and 1147–1148. -/
theorem ChristodoulouBV.lapse_sq_pos {D : Set (ℝ × ℝ)} {S : SSFields}
    (h : ChristodoulouBV D (adjacentAxis D) S) (hD : domainOfDevelopment D)
    {p : ℝ × ℝ} (hp : p ∈ D) :
    0 < -4 * S.lam p.1 p.2 * S.nu p.1 p.2 / (1 - S.mu p.1 p.2) := by
  apply div_pos _ (sub_pos.mpr (h.mu_lt_one hD hp))
  exact mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos (by norm_num) (h.lam_pos hp))
    (h.nu_neg hD hp)

/-- A positive lapse square satisfying the Hawking relation exists at every
point. Paper `e1a0fd5`, `eq:hawking-mass`, line 1411;
Christodoulou pp. 1133–1135 and 1147–1148. -/
theorem ChristodoulouBV.exists_lapse_sq {D : Set (ℝ × ℝ)} {S : SSFields}
    (h : ChristodoulouBV D (adjacentAxis D) S) (hD : domainOfDevelopment D)
    {p : ℝ × ℝ} (hp : p ∈ D) :
    ∃ Ω2 : ℝ, 0 < Ω2 ∧
      1 - S.mu p.1 p.2 = -4 * S.lam p.1 p.2 * S.nu p.1 p.2 / Ω2 := by
  refine ⟨_, h.lapse_sq_pos hD hp, ?_⟩
  have hl := (h.lam_pos hp).ne'
  have hn := (h.nu_neg hD hp).ne
  have hg := (sub_pos.mpr (h.mu_lt_one hD hp)).ne'
  field_simp

/-- The mass also vanishes along incoming rays, by 0 ≤ 2m ≤ r and the radius
comparison. Paper `e1a0fd5`, `eq:regular-axis`, lines 220–275 and 1411;
Christodoulou (1.7b), p. 1147, incoming mass integral. -/
theorem ChristodoulouBV.incoming_mass_axis_limit {D : Set (ℝ × ℝ)} {S : SSFields}
    (h : ChristodoulouBV D (adjacentAxis D) S) (hD : domainOfDevelopment D) (a : ℝ) :
    Tendsto (fun u => S.m u a)
      (𝓝[<] a ⊓ 𝓟 {u | (u, a) ∈ D}) (𝓝 0) := by
  have hev : ∀ᶠ u in 𝓝[<] a ⊓ 𝓟 {u | (u, a) ∈ D}, (u, a) ∈ D :=
    eventually_inf_principal.mpr (Filter.Eventually.of_forall (fun _ hp => hp))
  have hr : Tendsto (fun u => S.r u a / 2)
      (𝓝[<] a ⊓ 𝓟 {u | (u, a) ∈ D}) (𝓝 0) := by
    simpa using (h.incoming_radius_axis_limit hD a).div_const 2
  apply squeeze_zero' (hev.mono (fun u hp => (h.mass_gap_nonneg hD hp).1)) _ hr
  filter_upwards [hev] with u hp
  have hg := (h.mass_gap_nonneg hD hp).2
  linarith

/-- The incoming boundary conditions follow from the existing class, with no added source
hypothesis. Paper `e1a0fd5`, `eq:regular-axis`, line 1411; Christodoulou (1.7a,b), pp. 1147–1148.
The conclusion holds for every a, including vacuous rays and terminal axis parameters. -/
theorem ChristodoulouBV.incoming_axis_limits {D : Set (ℝ × ℝ)} {S : SSFields}
    (h : ChristodoulouBV D (adjacentAxis D) S) (hD : domainOfDevelopment D) (a : ℝ) :
    Tendsto (fun u => S.r u a)
      (𝓝[<] a ⊓ 𝓟 {u | (u, a) ∈ D}) (𝓝 0) ∧
    Tendsto (fun u => S.m u a)
      (𝓝[<] a ⊓ 𝓟 {u | (u, a) ∈ D}) (𝓝 0) :=
  ⟨h.incoming_radius_axis_limit hD a, h.incoming_mass_axis_limit hD a⟩

end AcExtensionPrinciple

end
