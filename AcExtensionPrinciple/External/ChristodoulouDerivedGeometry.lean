module

public import AcExtensionPrinciple.External.ChristodoulouBV
public import AcExtensionPrinciple.Solution.PrimitiveCalculus

/-!
# Geometry supplied by the Christodoulou BV class

Deductions from `ChristodoulouBV`. Paper `e1a0fd5`,
`equations.tex` lines 220–275 and 1411; Christodoulou pp. 1146–1148.
The axis is excluded from the domain. No values of total fields on the axis
are used, and the domain need not contain its terminal outgoing ray.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- A development contains the outgoing segment from its axis to each point.
Paper `e1a0fd5`, line 1411; Christodoulou p. 1146, definition of development. -/
theorem domainOfDevelopment.outgoing {D : Set (ℝ × ℝ)}
    (hD : domainOfDevelopment D) {u v w : ℝ} (hp : (u, v) ∈ D)
    (hw : w ∈ Ioc u v) : (u, w) ∈ D :=
  hD.2 (u, v) hp ⟨⟨(hD.1 hp).1, le_rfl⟩, hw⟩

/-- Outgoing compact segments ending below a point remain in its development.
Paper `e1a0fd5`, line 1411; Christodoulou p. 1146. -/
theorem domainOfDevelopment.outSeg {D : Set (ℝ × ℝ)}
    (hD : domainOfDevelopment D) {u v a b : ℝ} (hp : (u, v) ∈ D)
    (hua : u < a) (hbv : b ≤ v) : outSeg u a b ⊆ D := by
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  simp only [mem_singleton_iff] at hx
  subst x
  exact hD.outgoing hp ⟨hua.trans_le hy.1, hy.2.trans hbv⟩

/-- The entire right neighborhood of an outgoing axis endpoint lies on its ray.
Paper `e1a0fd5`, lines 220–275 and 1411; Christodoulou pp. 1146–1147. -/
theorem domainOfDevelopment.outgoing_filter {D : Set (ℝ × ℝ)}
    (hD : domainOfDevelopment D) {u v : ℝ} (hp : (u, v) ∈ D) :
    𝓝[>] u ≤ 𝓟 {w | (u, w) ∈ D} := by
  apply le_principal_iff.mpr
  filter_upwards [Ioo_mem_nhdsGT (hD.1 hp).2] with w hw
  exact hD.outgoing hp ⟨hw.1, hw.2.le⟩

/-- Each point's outgoing axis endpoint is adjacent to the development.
Paper `e1a0fd5`, line 1411; Christodoulou pp. 1146–1147. -/
theorem domainOfDevelopment.outgoing_axis {D : Set (ℝ × ℝ)}
    (hD : domainOfDevelopment D) {u v : ℝ} (hp : (u, v) ∈ D) :
    u ∈ adjacentAxis D := by
  have ht : Tendsto (fun w : ℝ => (u, w)) (𝓝[>] u) (𝓝 (u, u)) :=
    tendsto_const_nhds.prodMk_nhds (tendsto_id.mono_left nhdsWithin_le_nhds)
  exact mem_closure_of_tendsto ht (le_principal_iff.mp (hD.outgoing_filter hp))

/-- Outgoing radius primitives are AC on compact segments.
Paper `e1a0fd5`, `eq:radius`, lines 220–275; Christodoulou (1.12). -/
theorem ChrBVCore.radius_ac_out {D : Set (ℝ × ℝ)} {A : Set ℝ} {S : SSFields}
    (h : ChrBVCore D A S) {u a b : ℝ} (hab : a ≤ b) (hs : outSeg u a b ⊆ D) :
    AbsolutelyContinuousOnInterval (S.r u) a b := by
  apply intervalPrimitive_ac (g := S.lam u) hab
  intro x hx
  exact h.radius_out u a x hx.1 (fun p hp => hs ⟨hp.1, hp.2.1, hp.2.2.trans hx.2⟩)

/-- Outgoing mass primitives are AC on compact segments.
Paper `e1a0fd5`, `eq:mass`, lines 220–275; Christodoulou (1.15b). -/
theorem ChrBVCore.mass_ac_out {D : Set (ℝ × ℝ)} {A : Set ℝ} {S : SSFields}
    (h : ChrBVCore D A S) {u a b : ℝ} (hab : a ≤ b) (hs : outSeg u a b ⊆ D) :
    AbsolutelyContinuousOnInterval (S.m u) a b := by
  apply intervalPrimitive_ac (g := S.massV u) hab
  intro x hx
  exact h.mass_out u a x hx.1 (fun p hp => hs ⟨hp.1, hp.2.1, hp.2.2.trans hx.2⟩)

/-- Outgoing incoming-expansion primitives are AC on compact segments.
Paper `e1a0fd5`, `eq:radius`, lines 220–275; Christodoulou (1.14b). -/
theorem ChrBVCore.nu_ac_out {D : Set (ℝ × ℝ)} {A : Set ℝ} {S : SSFields}
    (h : ChrBVCore D A S) {u a b : ℝ} (hab : a ≤ b) (hs : outSeg u a b ⊆ D) :
    AbsolutelyContinuousOnInterval (S.nu u) a b := by
  apply intervalPrimitive_ac (g := S.radiusCoeff u) hab
  intro x hx
  exact h.nu_out u a x hx.1 (fun p hp => hs ⟨hp.1, hp.2.1, hp.2.2.trans hx.2⟩)

/-- Positive outgoing expansion is explicit in the global class.
Paper `e1a0fd5`, lines 220–275; Christodoulou pp. 1146–1147, inf λ > 0. -/
theorem ChristodoulouBV.lam_pos {D : Set (ℝ × ℝ)} {A : Set ℝ} {S : SSFields}
    (h : ChristodoulouBV D A S) {p : ℝ × ℝ} (hp : p ∈ D) :
    0 < S.lam p.1 p.2 := by
  obtain ⟨c, N, hc, hb⟩ := h.2.expansion_bounds
  exact hc.trans_le (hb p ⟨mem_univ _, hp⟩).1

/-- Uniform lower radius comparison, using an outgoing limit rather than axis values.
Paper `e1a0fd5`, `eq:radius-from-axis`, lines 220–275;
Christodoulou (1.7a), (1.12) and inf λ > 0 on pp. 1146–1147. -/
theorem ChristodoulouBV.radius_lower {D : Set (ℝ × ℝ)} {S : SSFields}
    (h : ChristodoulouBV D (adjacentAxis D) S) (hD : domainOfDevelopment D) :
    ∃ c : ℝ, 0 < c ∧ ∀ p ∈ D, c * (p.2 - p.1) ≤ S.r p.1 p.2 := by
  obtain ⟨c, N, hc, hb⟩ := h.2.expansion_bounds
  refine ⟨c, hc, ?_⟩
  rintro ⟨u, v⟩ hp
  have ht := (h.1.radius_axis_limit u (hD.outgoing_axis hp)).mono_left
    (le_inf le_rfl (hD.outgoing_filter hp))
  have hlim : Tendsto (fun a => S.r u a + c * (v - a)) (𝓝[>] u)
      (𝓝 (c * (v - u))) := by
    simpa using ht.add (tendsto_const_nhds.mul
      (tendsto_const_nhds.sub nhdsWithin_le_nhds))
  apply le_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsGT (hD.1 hp).2] with a ha
  have hs := hD.outSeg hp ha.1 le_rfl
  have hi := h.1.radius_out u a v ha.2.le hs
  have hle : c * (v - a) ≤ ∫ s in a..v, S.lam u s := by
    calc
      _ = ∫ _ in a..v, c := by simp [mul_comm]
      _ ≤ _ := intervalIntegral.integral_mono_on ha.2.le intervalIntegrable_const hi.1
        (fun s hs' => (hb (u, s) ⟨mem_univ _, hs ⟨by simp, hs'⟩⟩).1)
  linarith [hi.2]

/-- Strict positivity of the radius follows from the class and the domain condition.
Paper `e1a0fd5`, line 66, `eq:radius-from-axis`; Christodoulou pp. 1146–1147. -/
theorem ChristodoulouBV.r_pos {D : Set (ℝ × ℝ)} {S : SSFields}
    (h : ChristodoulouBV D (adjacentAxis D) S) (hD : domainOfDevelopment D)
    {p : ℝ × ℝ} (hp : p ∈ D) : 0 < S.r p.1 p.2 := by
  obtain ⟨c, hc, hb⟩ := h.radius_lower hD
  exact (mul_pos hc (sub_pos.mpr (hD.1 hp).2)).trans_le (hb p hp)

/-- The expansion-axis cancellation and uniform outgoing BV bound supply a
global upper bound for λ. Paper `e1a0fd5`, lines 220–275 and 1411;
Christodoulou pp. 1146–1148, items 1/2 and inf ν > −∞. -/
theorem ChristodoulouBV.lam_upper {D : Set (ℝ × ℝ)} {S : SSFields}
    (h : ChristodoulouBV D (adjacentAxis D) S) (hD : domainOfDevelopment D) :
    ∃ L : ℝ, 0 < L ∧ ∀ p ∈ D, S.lam p.1 p.2 ≤ L := by
  obtain ⟨c, N, hc, hb⟩ := h.2.expansion_bounds
  obtain ⟨C, hout, hin⟩ := h.2.variation_bounds
  refine ⟨|N| + (ENNReal.ofReal C).toReal + 1, by positivity, ?_⟩
  rintro ⟨u, v⟩ hp
  have hTV := (hout u).1
  have hf : BoundedVariationOn (S.lam u)
      {w | (u, w) ∈ (univ : Set (ℝ × ℝ)) ∩ D} :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hTV
  have ht := (h.1.expansion_axis_limit u (hD.outgoing_axis hp)).mono_left
    (le_inf le_rfl (hD.outgoing_filter hp))
  have hev := ht.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨a, hsum, ha⟩ := (hev.and (Ioo_mem_nhdsGT (hD.1 hp).2)).exists
  have hpa := hD.outgoing hp ⟨ha.1, ha.2.le⟩
  have hdist : |S.lam u v - S.lam u a| ≤ (ENNReal.ofReal C).toReal := by
    have hd := hf.dist_le ⟨mem_univ _, hp⟩ ⟨mem_univ _, hpa⟩
    have hd' : |S.lam u v - S.lam u a| ≤ (eVariationOn (S.lam u)
        {w | (u, w) ∈ (univ : Set (ℝ × ℝ)) ∩ D}).toReal := by
      simpa only [Real.dist_eq] using hd
    exact hd'.trans
      (ENNReal.toReal_mono ENNReal.ofReal_ne_top hTV)
  have hn := (hb (u, a) ⟨mem_univ _, hpa⟩).2
  have hdiff := le_abs_self (S.lam u v - S.lam u a)
  have hN := le_abs_self N
  linarith

/-- Uniform upper radius comparison from outgoing primitives and their axis
limits. Paper `e1a0fd5`, `eq:radius-from-axis`, lines 220–275;
Christodoulou (1.7a), (1.12), pp. 1146–1148. -/
theorem ChristodoulouBV.radius_upper {D : Set (ℝ × ℝ)} {S : SSFields}
    (h : ChristodoulouBV D (adjacentAxis D) S) (hD : domainOfDevelopment D) :
    ∃ L : ℝ, 0 < L ∧ ∀ p ∈ D, S.r p.1 p.2 ≤ L * (p.2 - p.1) := by
  obtain ⟨L, hL, hb⟩ := h.lam_upper hD
  refine ⟨L, hL, ?_⟩
  rintro ⟨u, v⟩ hp
  have ht := (h.1.radius_axis_limit u (hD.outgoing_axis hp)).mono_left
    (le_inf le_rfl (hD.outgoing_filter hp))
  have hlim : Tendsto (fun a => S.r u a + L * (v - a)) (𝓝[>] u)
      (𝓝 (L * (v - u))) := by
    simpa using ht.add (tendsto_const_nhds.mul
      (tendsto_const_nhds.sub nhdsWithin_le_nhds))
  apply ge_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsGT (hD.1 hp).2] with a ha
  have hs := hD.outSeg hp ha.1 le_rfl
  have hi := h.1.radius_out u a v ha.2.le hs
  have hle : (∫ s in a..v, S.lam u s) ≤ L * (v - a) := by
    calc
      _ ≤ ∫ _ in a..v, L := intervalIntegral.integral_mono_on ha.2.le hi.1
        intervalIntegrable_const (fun s hs' => hb (u, s) (hs ⟨by simp, hs'⟩))
      _ = _ := by simp [mul_comm]
  linarith [hi.2]

/-- Radius vanishes along incoming rays even at an axis point whose outgoing
ray is absent. Paper `e1a0fd5`, `eq:regular-axis`, lines 220–275 and 1411;
Christodoulou (1.7a), pp. 1147–1148. -/
theorem ChristodoulouBV.incoming_radius_axis_limit {D : Set (ℝ × ℝ)} {S : SSFields}
    (h : ChristodoulouBV D (adjacentAxis D) S) (hD : domainOfDevelopment D) (a : ℝ) :
    Tendsto (fun u => S.r u a)
      (𝓝[<] a ⊓ 𝓟 {u | (u, a) ∈ D}) (𝓝 0) := by
  obtain ⟨L, hL, hb⟩ := h.radius_upper hD
  have hid : Tendsto (fun u : ℝ => u)
      (𝓝[<] a ⊓ 𝓟 {u | (u, a) ∈ D}) (𝓝 a) :=
    tendsto_id.mono_left (inf_le_left.trans nhdsWithin_le_nhds)
  have ht : Tendsto (fun u => L * (a - u))
      (𝓝[<] a ⊓ 𝓟 {u | (u, a) ∈ D}) (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := L)).mul
      ((tendsto_const_nhds (x := a)).sub hid)
  have hev : ∀ᶠ u in 𝓝[<] a ⊓ 𝓟 {u | (u, a) ∈ D}, (u, a) ∈ D :=
    eventually_inf_principal.mpr (Filter.Eventually.of_forall (fun _ hp => hp))
  exact squeeze_zero' (hev.mono (fun u hp => (h.r_pos hD hp).le))
    (hev.mono (fun u hp => hb (u, a) hp)) ht

end AcExtensionPrinciple

end
