module

public import AcExtensionPrinciple.External.ChristodoulouDerivedComparison

/-!
# Mass signs derived within Christodoulou's BV class

Paper `e1a0fd5`, `equations.tex` `eq:mass`, lines 220–275 and 1411;
Christodoulou pp. 1147–1148. Compact outgoing integrating factors applied
to m and r − 2m avoid assuming integrability at the axis, a mass-ratio
limit there, or any of the signs being proved.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- The scalar amplitude is BV on each compact outgoing segment.
Paper `e1a0fd5`, lines 220–275 and 1411; Christodoulou p. 1147, item 5. -/
theorem ChristodoulouBV.theta_bv_out {D : Set (ℝ × ℝ)} {A : Set ℝ} {S : SSFields}
    (h : ChristodoulouBV D A S) {u a b : ℝ} (hs : outSeg u a b ⊆ D) :
    BoundedVariationOn (S.theta u) (Icc a b) := by
  obtain ⟨C, hout, hin⟩ := h.2.variation_bounds
  have hsub : Icc a b ⊆ {v | (u, v) ∈ (univ : Set (ℝ × ℝ)) ∩ D} :=
    fun v hv => ⟨mem_univ _, hs ⟨by simp, hv⟩⟩
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    ((eVariationOn.mono _ hsub).trans (hout u).2.2)

/-- The coefficient θ²/(λr) is integrable on each compact off-axis segment.
Paper `e1a0fd5`, `eq:mass`, lines 220–275; Christodoulou p. 1147.
Its premises follow from BV θ, inf λ > 0, and the radius primitive. -/
theorem ChristodoulouBV.mass_coefficient_integrable {D : Set (ℝ × ℝ)} {S : SSFields}
    (h : ChristodoulouBV D (adjacentAxis D) S) (hD : domainOfDevelopment D)
    {u a b : ℝ} (hab : a ≤ b) (hs : outSeg u a b ⊆ D) :
    IntervalIntegrable (fun v => S.theta u v ^ 2 / (S.lam u v * S.r u v))
      volume a b := by
  obtain ⟨c, N, hc, hb⟩ := h.2.expansion_bounds
  have ht := h.theta_bv_out hs
  have ht2 : BoundedVariationOn (fun v => S.theta u v ^ 2) (Icc a b) := by
    simpa only [pow_two, Pi.mul_def] using ht.mul ht
  have hnum := ht2.intervalIntegrable (μ := volume) (by rw [uIcc_of_le hab])
  have hlam := (h.1.radius_out u a b hab hs).1
  have hquot := chr_intervalIntegrable_div_pos hab hc hnum hlam
    (fun v hv => ⟨sq_nonneg _, (hb (u, v) ⟨mem_univ _, hs ⟨by simp, hv⟩⟩).1⟩)
  have hrinv := positive_ac_inv (h.1.radius_ac_out hab hs)
    (fun v hv => h.r_pos hD (p := (u, v))
      (hs ⟨by simp, by simpa [uIcc_of_le hab] using hv⟩))
  convert hquot.mul_continuousOn hrinv.continuousOn using 1
  ext v
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The mass equation and its radius-gap version hold a.e. without assuming
any mass or incoming-expansion sign. Paper `e1a0fd5`, `eq:mass`, `eq:radius`,
lines 220–275; Christodoulou p. 1147, (1.12), (1.15b). -/
theorem ChristodoulouBV.mass_gap_ae_ode {D : Set (ℝ × ℝ)} {S : SSFields}
    (h : ChristodoulouBV D (adjacentAxis D) S) (hD : domainOfDevelopment D)
    {u a b : ℝ} (hab : a ≤ b) (hs : outSeg u a b ⊆ D) :
    ∀ᵐ v, v ∈ Ioo a b →
      HasDerivAt (S.m u)
        (-(S.theta u v ^ 2 / (S.lam u v * S.r u v)) * S.m u v +
          S.theta u v ^ 2 / (2 * S.lam u v)) v ∧
      HasDerivAt (fun w => S.r u w - 2 * S.m u w)
        (-(S.theta u v ^ 2 / (S.lam u v * S.r u v)) *
          (S.r u v - 2 * S.m u v) + S.lam u v) v := by
  have hm := intervalPrimitive_ae_hasDerivAt (g := S.massV u) hab
    (fun x hx => h.1.mass_out u a x hx.1
      (fun p hp => hs ⟨hp.1, hp.2.1, hp.2.2.trans hx.2⟩))
  have hr := intervalPrimitive_ae_hasDerivAt (g := S.lam u) hab
    (fun x hx => h.1.radius_out u a x hx.1
      (fun p hp => hs ⟨hp.1, hp.2.1, hp.2.2.trans hx.2⟩))
  filter_upwards [hm, hr] with v hmv hrv
  intro hv
  have hp := hs (show (u, v) ∈ outSeg u a b from ⟨by simp, hv.1.le, hv.2.le⟩)
  have hr0 := (h.r_pos hD hp).ne'
  have hl0 := (h.lam_pos hp).ne'
  have he : S.massV u v =
      -(S.theta u v ^ 2 / (S.lam u v * S.r u v)) * S.m u v +
        S.theta u v ^ 2 / (2 * S.lam u v) := by
    simp only [SSFields.massV, SSFields.mu, massRatio]
    field_simp [hr0, hl0]
    ring
  constructor
  · exact (hmv hv).congr_deriv he
  · convert (hrv hv).sub ((hmv hv).const_mul 2) using 1
    rw [he]
    field_simp [hr0, hl0]
    ring

/-- Both m and r − 2m are nonnegative, by compact comparisons and their zero
outgoing boundary limits. Paper `e1a0fd5`, `eq:regular-axis`, `eq:mass`,
lines 220–275; Christodoulou (1.7a,b), p. 1147. -/
theorem ChristodoulouBV.mass_gap_nonneg {D : Set (ℝ × ℝ)} {S : SSFields}
    (h : ChristodoulouBV D (adjacentAxis D) S) (hD : domainOfDevelopment D)
    {p : ℝ × ℝ} (hp : p ∈ D) :
    0 ≤ S.m p.1 p.2 ∧ 0 ≤ S.r p.1 p.2 - 2 * S.m p.1 p.2 := by
  rcases p with ⟨u, v⟩
  have huv := (hD.1 hp).2
  have hfilter := le_inf le_rfl (hD.outgoing_filter hp)
  have hr0 := (h.1.radius_axis_limit u (hD.outgoing_axis hp)).mono_left hfilter
  have hm0 := (h.1.mass_axis_limit u (hD.outgoing_axis hp)).mono_left hfilter
  have hg0 : Tendsto (fun w => S.r u w - 2 * S.m u w) (𝓝[>] u) (𝓝 0) := by
    simpa using hr0.sub (tendsto_const_nhds.mul hm0)
  have hcomp (a : ℝ) (ha : a ∈ Ioo u v) :
      min (S.m u a) 0 ≤ S.m u v ∧
        min (S.r u a - 2 * S.m u a) 0 ≤ S.r u v - 2 * S.m u v := by
    have hs := hD.outSeg hp ha.1 le_rfl
    have hq := h.mass_coefficient_integrable hD ha.2.le hs
    have hd := h.mass_gap_ae_ode hD ha.2.le hs
    have hpos (w : ℝ) (hw : w ∈ Icc a v) :
        0 ≤ S.theta u w ^ 2 / (S.lam u w * S.r u w) ∧ 0 < S.lam u w := by
      have hpw : (u, w) ∈ D := hs ⟨by simp, hw⟩
      exact ⟨div_nonneg (sq_nonneg _) (mul_pos (h.lam_pos hpw) (h.r_pos hD hpw)).le,
        h.lam_pos hpw⟩
    constructor
    · apply chr_linear_lower_bound ha.2.le (h.1.mass_ac_out ha.2.le hs) hq
      · filter_upwards [hd] with w hdw hw using (hdw hw).1
      · intro w hw
        have hl := (hpos w hw).2
        exact ⟨(hpos w hw).1, div_nonneg (sq_nonneg _)
          (mul_nonneg (by norm_num) hl.le)⟩
    · apply chr_linear_lower_bound ha.2.le
        ((h.1.radius_ac_out ha.2.le hs).sub ((h.1.mass_ac_out ha.2.le hs).const_mul 2)) hq
      · filter_upwards [hd] with w hdw hw using (hdw hw).2
      · exact fun w hw => ⟨(hpos w hw).1, (hpos w hw).2.le⟩
  exact ⟨chr_nonneg_of_axis_comparison huv hm0 (fun a ha => (hcomp a ha).1),
    chr_nonneg_of_axis_comparison (f := fun w => S.r u w - 2 * S.m u w)
      huv hg0 (fun a ha => (hcomp a ha).2)⟩

/-- The positive source λ makes the mass gap strictly positive off the axis.
Paper `e1a0fd5`, line 66, `eq:mass`, lines 220–275;
Christodoulou pp. 1147–1148. -/
theorem ChristodoulouBV.mass_gap_pos {D : Set (ℝ × ℝ)} {S : SSFields}
    (h : ChristodoulouBV D (adjacentAxis D) S) (hD : domainOfDevelopment D)
    {p : ℝ × ℝ} (hp : p ∈ D) : 0 < S.r p.1 p.2 - 2 * S.m p.1 p.2 := by
  rcases p with ⟨u, v⟩
  obtain ⟨a, hua, hav⟩ := exists_between (hD.1 hp).2
  have hs := hD.outSeg hp hua le_rfl
  obtain ⟨c, N, hc, hb⟩ := h.2.expansion_bounds
  apply chr_linear_pos hav hc
    ((h.1.radius_ac_out hav.le hs).sub ((h.1.mass_ac_out hav.le hs).const_mul 2))
    (h.mass_coefficient_integrable hD hav.le hs)
  · filter_upwards [h.mass_gap_ae_ode hD hav.le hs] with w hd hw using (hd hw).2
  · exact (h.mass_gap_nonneg hD (hD.outgoing hp ⟨hua, hav.le⟩)).2
  · intro w hw
    have hpw : (u, w) ∈ D := hs ⟨by simp, hw⟩
    exact ⟨div_nonneg (sq_nonneg _) (mul_pos (h.lam_pos hpw) (h.r_pos hD hpw)).le,
      (hb (u, w) ⟨mem_univ _, hpw⟩).1⟩

/-- The Hawking mass ratio is nonnegative on the development.
Paper `e1a0fd5`, line 66, `eq:scalar-and-mass-ratio`, lines 220–275;
Christodoulou pp. 1147–1148. -/
theorem ChristodoulouBV.mu_nonneg {D : Set (ℝ × ℝ)} {S : SSFields}
    (h : ChristodoulouBV D (adjacentAxis D) S) (hD : domainOfDevelopment D)
    {p : ℝ × ℝ} (hp : p ∈ D) : 0 ≤ S.mu p.1 p.2 := by
  exact div_nonneg (mul_nonneg (by norm_num) (h.mass_gap_nonneg hD hp).1)
    (h.r_pos hD hp).le

/-- The Hawking mass ratio is strictly below one on the development.
Paper `e1a0fd5`, line 66, `eq:scalar-and-mass-ratio`, lines 220–275;
Christodoulou pp. 1147–1148. -/
theorem ChristodoulouBV.mu_lt_one {D : Set (ℝ × ℝ)} {S : SSFields}
    (h : ChristodoulouBV D (adjacentAxis D) S) (hD : domainOfDevelopment D)
    {p : ℝ × ℝ} (hp : p ∈ D) : S.mu p.1 p.2 < 1 := by
  apply (div_lt_one (h.r_pos hD hp)).mpr
  linarith [h.mass_gap_pos hD hp]

end AcExtensionPrinciple

end
