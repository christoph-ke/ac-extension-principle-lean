module

public import AcExtensionPrinciple.Continuation.RayAgreement

/-!
# Pointwise agreement of the right-continuous BV representatives

Paper `e1a0fd5`, `equations.tex` lines 222 and 1411–1422. Almost-everywhere
equality determines a right-continuous field wherever the common domain
contains a nontrivial interval to the right. This includes the initial
incoming endpoint and the terminal incoming ray, but excludes the final
outgoing endpoint.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- A right-continuous representative is determined by its a.e. values on a
nontrivial right interval. Paper `e1a0fd5`, lines 222 and 1411–1422;
component lemma for the Luk–Oh BV representative convention. -/
theorem right_continuous_eq_of_ae_eq {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {f g : ℝ → Y} {x b : ℝ} (hxb : x < b)
    (hf : ContinuousWithinAt f (Icc x b) x)
    (hg : ContinuousWithinAt g (Icc x b) x)
    (he : ∀ᵐ y, y ∈ Ioo x b → f y = g y) : f x = g x := by
  apply tendsto_nhds_unique_of_frequently_eq hf.tendsto hg.tendsto
  by_contra hfreq
  have hne : ∀ᶠ y in 𝓝[Icc x b] x, f y ≠ g y := not_frequently.mp hfreq
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhdsWithin_iff.mp hne
  have hxm : x < min b (x + δ) := lt_min hxb (by linarith)
  have hpos : volume (Ioo x (min b (x + δ))) ≠ 0 := by
    rw [Real.volume_Ioo]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hxm))
  obtain ⟨y, hy, hye⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos
    (ae_restrict_of_ae he)
  have hyb : y < b := hy.2.trans_le (min_le_left _ _)
  have hyd : dist y x < δ := by
    rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hy.1)]
    have := hy.2.trans_le (min_le_right _ _)
    linarith
  exact hsub ⟨hyd, hy.1.le, hyb.le⟩ (hye ⟨hy.1, hyb⟩)

/-- On a common outgoing segment, θ + λφ supplies right continuity of
∂ᵥψ. Scalar continuity comes from the core's scalar AC clause.
Paper `e1a0fd5`, lines 222 and 1411–1422. -/
theorem ChrBVCore.dvpsi_right_cont_on_outSeg {D : Set (ℝ × ℝ)} {A : Set ℝ}
    {S : SSFields} {u a b x : ℝ} (h : ChrBVCore D A S)
    (hab : a ≤ b) (hs : outSeg u a b ⊆ D) (hx : x ∈ Icc a b) :
    ContinuousWithinAt (S.dvpsi u) (Icc x b) x := by
  have hp : (u, x) ∈ D := hs ⟨by simp, hx⟩
  have hsub : Icc x b ⊆ {w | x ≤ w ∧ (u, w) ∈ D} :=
    fun w hw => ⟨hw.1, hs ⟨by simp, hx.1.trans hw.1, hw.2⟩⟩
  have hlam := (h.lam_right_cont (u, x) hp).mono hsub
  have htheta := (h.theta_right_cont (u, x) hp).mono hsub
  have hphiC : ContinuousOn (S.phi u) (Icc a b) := by
    simpa only [uIcc_of_le hab] using (h.scalar_ac_out u a b hab hs).continuousOn
  have hphi := (hphiC x hx).mono
    (Icc_subset_Icc hx.1 le_rfl)
  convert htheta.add (hlam.mul hphi) using 1
  funext w
  simp [SSFields.theta]

/-- On a common incoming segment, ζ + νφ supplies right continuity of
∂ᵤψ. Paper `e1a0fd5`, lines 222 and 1411–1422. -/
theorem ChrBVCore.dupsi_right_cont_on_inSeg {D : Set (ℝ × ℝ)} {A : Set ℝ}
    {S : SSFields} {v a b x : ℝ} (h : ChrBVCore D A S)
    (hab : a ≤ b) (hs : inSeg v a b ⊆ D) (hx : x ∈ Icc a b) :
    ContinuousWithinAt (fun u => S.dupsi u v) (Icc x b) x := by
  have hp : (x, v) ∈ D := hs ⟨hx, by simp⟩
  have hsub : Icc x b ⊆ {s | x ≤ s ∧ (s, v) ∈ D} :=
    fun s hs' => ⟨hs'.1, hs ⟨⟨hx.1.trans hs'.1, hs'.2⟩, by simp⟩⟩
  have hnu := (h.nu_right_cont (x, v) hp).mono hsub
  have hzeta := (h.zeta_right_cont (x, v) hp).mono hsub
  have hphiC : ContinuousOn (fun u => S.phi u v) (Icc a b) := by
    simpa only [uIcc_of_le hab] using (h.scalar_ac_in v a b hab hs).continuousOn
  have hphi := (hphiC x hx).mono
    (Icc_subset_Icc hx.1 le_rfl)
  convert hzeta.add (hnu.mul hphi) using 1
  funext s
  simp [SSFields.zeta]

/-- Equal primitives determine λ and ∂ᵥψ pointwise up to the last outgoing
endpoint. Paper `e1a0fd5`, lines 222 and 1411–1422. -/
theorem outgoing_derivatives_agree {D : Set (ℝ × ℝ)} {A : Set ℝ}
    {S₁ S₂ : SSFields} {u a b : ℝ} (hab : a ≤ b) (hs : outSeg u a b ⊆ D)
    (h₁ : ChrBVCore D A S₁) (h₂ : ChrBVCore D A S₂)
    (he : ∀ p ∈ D, S₁.r p.1 p.2 = S₂.r p.1 p.2 ∧
      S₁.phi p.1 p.2 = S₂.phi p.1 p.2) :
    ∀ x ∈ Ico a b, S₁.lam u x = S₂.lam u x ∧ S₁.dvpsi u x = S₂.dvpsi u x := by
  intro x hx
  have hp : (u, x) ∈ D := hs ⟨by simp, hx.1, hx.2.le⟩
  have hsub : Icc x b ⊆ {w | x ≤ w ∧ (u, w) ∈ D} :=
    fun w hw => ⟨hw.1, hs ⟨by simp, hx.1.trans hw.1, hw.2⟩⟩
  have hae := outgoing_derivatives_agree_ae hab hs h₁ h₂ he
  constructor
  · apply right_continuous_eq_of_ae_eq hx.2
      ((h₁.lam_right_cont _ hp).mono hsub) ((h₂.lam_right_cont _ hp).mono hsub)
    exact hae.mono (fun w hw hw' => (hw ⟨hx.1.trans_lt hw'.1, hw'.2⟩).1)
  · apply right_continuous_eq_of_ae_eq hx.2
      (h₁.dvpsi_right_cont_on_outSeg hab hs ⟨hx.1, hx.2.le⟩)
      (h₂.dvpsi_right_cont_on_outSeg hab hs ⟨hx.1, hx.2.le⟩)
    exact hae.mono (fun w hw hw' => (hw ⟨hx.1.trans_lt hw'.1, hw'.2⟩).2)

/-- Equal primitives determine ν and ∂ᵤψ pointwise, including the first
incoming endpoint. Paper `e1a0fd5`, lines 222 and 1411–1422. -/
theorem incoming_derivatives_agree {D : Set (ℝ × ℝ)} {A : Set ℝ}
    {S₁ S₂ : SSFields} {v a b : ℝ} (hab : a ≤ b) (hs : inSeg v a b ⊆ D)
    (h₁ : ChrBVCore D A S₁) (h₂ : ChrBVCore D A S₂)
    (he : ∀ p ∈ D, S₁.r p.1 p.2 = S₂.r p.1 p.2 ∧
      S₁.phi p.1 p.2 = S₂.phi p.1 p.2) :
    ∀ x ∈ Ico a b, S₁.nu x v = S₂.nu x v ∧ S₁.dupsi x v = S₂.dupsi x v := by
  intro x hx
  have hp : (x, v) ∈ D := hs ⟨⟨hx.1, hx.2.le⟩, by simp⟩
  have hsub : Icc x b ⊆ {s | x ≤ s ∧ (s, v) ∈ D} :=
    fun s hs' => ⟨hs'.1, hs ⟨⟨hx.1.trans hs'.1, hs'.2⟩, by simp⟩⟩
  have hae := incoming_derivatives_agree_ae hab hs h₁ h₂ he
  constructor
  · apply right_continuous_eq_of_ae_eq hx.2
      ((h₁.nu_right_cont _ hp).mono hsub) ((h₂.nu_right_cont _ hp).mono hsub)
    exact hae.mono (fun s hs' hs'' => (hs' ⟨hx.1.trans_lt hs''.1, hs''.2⟩).1)
  · apply right_continuous_eq_of_ae_eq hx.2
      (h₁.dupsi_right_cont_on_inSeg hab hs ⟨hx.1, hx.2.le⟩)
      (h₂.dupsi_right_cont_on_inSeg hab hs ⟨hx.1, hx.2.le⟩)
    exact hae.mono (fun s hs' hs'' => (hs' ⟨hx.1.trans_lt hs''.1, hs''.2⟩).2)

/-- Almost-everywhere ray agreement becomes pointwise for the BV representatives:
outgoing fields for v < b, and incoming fields for v ≤ b, including u = 0.
Paper `e1a0fd5`, lines 222 and 1411–1422. -/
theorem late_triangle_derivatives_agree {S₁ S₂ : SSFields} {b : ℝ}
    (h₁ : ∀ a ∈ Ico 0 b,
      ChristodoulouBV (pastSet a b) (adjacentAxis (pastSet a b)) S₁)
    (h₂ : ChristodoulouBV smallBVDomain (Ici 0) S₂)
    (he : ∀ p : ℝ × ℝ, 0 ≤ p.1 → p.1 < p.2 → p.2 ≤ b →
      S₁.r p.1 p.2 = S₂.r p.1 p.2 ∧ S₁.phi p.1 p.2 = S₂.phi p.1 p.2) :
    (∀ u ∈ Ico 0 b, ∀ v ∈ Ioo u b,
      S₁.lam u v = S₂.lam u v ∧ S₁.dvpsi u v = S₂.dvpsi u v) ∧
    (∀ v ∈ Ioc 0 b, ∀ u ∈ Ico 0 v,
      S₁.nu u v = S₂.nu u v ∧ S₁.dupsi u v = S₂.dupsi u v) := by
  constructor
  · intro u hu v hv
    have hs : outSeg u v b ⊆ pastSet u b := by
      rintro ⟨x, y⟩ ⟨hx, hy⟩
      simp only [mem_singleton_iff] at hx
      subst x
      exact ⟨⟨hu.1, le_rfl⟩, hv.1.trans_le hy.1, hy.2⟩
    exact outgoing_derivatives_agree hv.2.le hs (h₁ u hu).1
      (h₂.on_pastSet u b).1 (fun p hp => he p hp.1.1 hp.2.1 hp.2.2) v ⟨le_rfl, hv.2⟩
  · intro v hv u hu
    obtain ⟨c, huc, hcv⟩ := exists_between hu.2
    have hc : c ∈ Ico 0 b := ⟨hu.1.trans huc.le, hcv.trans_le hv.2⟩
    have hs : inSeg v u c ⊆ pastSet c b := by
      rintro ⟨x, y⟩ ⟨hx, hy⟩
      simp only [mem_singleton_iff] at hy
      subst y
      exact ⟨⟨hu.1.trans hx.1, hx.2⟩, hx.2.trans_lt hcv, hv.2⟩
    exact incoming_derivatives_agree huc.le hs (h₁ c hc).1
      (h₂.on_pastSet c b).1 (fun p hp => he p hp.1.1 hp.2.1 hp.2.2) u ⟨le_rfl, huc⟩

end AcExtensionPrinciple

end
