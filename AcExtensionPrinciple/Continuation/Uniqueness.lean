module

public import AcExtensionPrinciple.Continuation.InitialData
public import AcExtensionPrinciple.External.BVUniqueness
public import AcExtensionPrinciple.Solution.PrimitiveCalculus

/-!
# The uniqueness step on the late triangle

Components for paper `e1a0fd5`, `equations.tex` line 1411.
E2 is a hypothesis. Original class membership in the selected chart is supplied by
`StandingFull.exists_selected_chart_bv` in `Continuation/SelectedChart.lean`.
Restriction and initial scalar reconstruction are proved in the imported modules.
Derivative agreement is almost everywhere on each characteristic segment.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- Equal primitives have equal densities almost everywhere on a segment.
Paper `e1a0fd5`, lines 1411–1422, characteristic integral interpretation Q8. -/
theorem primitive_density_agreement {f F g G : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, IntervalPrimitive f g a x)
    (hF : ∀ x ∈ Icc a b, IntervalPrimitive F G a x)
    (he : EqOn f F (Icc a b)) :
    ∀ᵐ x, x ∈ Ioo a b → g x = G x := by
  filter_upwards [intervalPrimitive_ae_hasDerivAt hab hf,
    intervalPrimitive_ae_hasDerivAt hab hF] with x hx hX
  intro hxi
  have hFX : HasDerivAt f (G x) x := by
    apply (hX hxi).congr_of_eventuallyEq
    filter_upwards [Icc_mem_nhds hxi.1 hxi.2] with y hy
    exact he hy
  exact (hx hxi).unique hFX

/-- Uniqueness on a causal past: E2 needs only the two BV classes and initial r,φ. Paper `e1a0fd5`,
line 1411. -/
theorem uniqueness_on_pastSet {S₁ S₂ : SSFields} {a b : ℝ}
    (hE2 : BVUniqueness)
    (h₁ : ChristodoulouBV (pastSet a b) (adjacentAxis (pastSet a b)) S₁)
    (h₂ : ChristodoulouBV smallBVDomain (Ici 0) S₂)
    (hgauge : ∀ v, (0, v) ∈ pastSet a b → S₁.r 0 v = v / 2)
    (hdata : ∀ v, (0, v) ∈ pastSet a b →
      S₁.r 0 v = S₂.r 0 v ∧ S₁.phi 0 v = S₂.phi 0 v) :
    ∀ p ∈ pastSet a b, S₁.r p.1 p.2 = S₂.r p.1 p.2 ∧
      S₁.phi p.1 p.2 = S₂.phi p.1 p.2 ∧ S₁.m p.1 p.2 = S₂.m p.1 p.2 :=
  hE2 _ (pastSet_domainOfDevelopment a b) S₁ S₂ h₁ (h₂.on_pastSet a b) hgauge hdata

/-- Uniqueness from class membership, restriction and derivative data: agreement includes v = ṽ₀ and
excludes only Γ. Paper `e1a0fd5`, line 1411, `eq:continuation-initial-datum`. The transformed
original's class membership is supplied by `StandingFull.exists_selected_chart_bv` in
`Continuation/SelectedChart.lean`. -/
theorem uniqueness_on_late_triangle_of_bv {S₁ S₂ : SSFields} {b : ℝ} (hb : 0 < b)
    (hE2 : BVUniqueness)
    (h₁ : ∀ a ∈ Ico 0 b,
      ChristodoulouBV (pastSet a b) (adjacentAxis (pastSet a b)) S₁)
    (h₂ : ChristodoulouBV smallBVDomain (Ici 0) S₂)
    (hr₁ : ∀ v ∈ Ioc 0 b, S₁.r 0 v = v / 2)
    (hr₂ : ∀ v ∈ Ioc 0 b, S₂.r 0 v = v / 2)
    (hd : ∀ v ∈ Ioc 0 b, S₁.dvpsi 0 v = S₂.dvpsi 0 v) :
    ∀ p : ℝ × ℝ, 0 ≤ p.1 → p.1 < p.2 → p.2 ≤ b →
      S₁.r p.1 p.2 = S₂.r p.1 p.2 ∧ S₁.phi p.1 p.2 = S₂.phi p.1 p.2 ∧
        S₁.m p.1 p.2 = S₂.m p.1 p.2 := by
  have hdata := initial_data_agreement hb (h₁ 0 ⟨le_rfl, hb⟩) h₂ hr₁ hr₂ hd
  intro p hu huv hv
  exact uniqueness_on_pastSet hE2 (h₁ p.1 ⟨hu, huv.trans_le hv⟩) h₂
    (fun v hv => hr₁ v ⟨hv.2.1.trans_le' hv.1.1, hv.2.2⟩) (fun v hv => hdata v hv.2) p
    ⟨⟨hu, le_rfl⟩, huv, hv⟩

/-- Outgoing derivative agreement: λ and ∂ᵥψ agree almost everywhere on every common closed outgoing
segment. Paper `e1a0fd5`, lines 1411–1422. The statement makes no choice of BV representatives at
segment endpoints. -/
theorem outgoing_derivatives_agree_ae {D : Set (ℝ × ℝ)} {A : Set ℝ}
    {S₁ S₂ : SSFields} {u a b : ℝ} (hab : a ≤ b) (hs : outSeg u a b ⊆ D)
    (h₁ : ChrBVCore D A S₁) (h₂ : ChrBVCore D A S₂)
    (he : ∀ p ∈ D, S₁.r p.1 p.2 = S₂.r p.1 p.2 ∧
      S₁.phi p.1 p.2 = S₂.phi p.1 p.2) :
    ∀ᵐ v, v ∈ Ioo a b →
      S₁.lam u v = S₂.lam u v ∧ S₁.dvpsi u v = S₂.dvpsi u v := by
  have hsub (x : ℝ) (hx : x ∈ Icc a b) : outSeg u a x ⊆ D := by
    apply Subset.trans _ hs
    exact prod_mono_right (Icc_subset_Icc le_rfl hx.2)
  have hr : EqOn (S₁.r u) (S₂.r u) (Icc a b) :=
    fun v hv => (he (u, v) (hs ⟨by simp, hv⟩)).1
  have hpsi : EqOn (fun v => S₁.r u v * S₁.phi u v)
      (fun v => S₂.r u v * S₂.phi u v) (Icc a b) := by
    intro v hv
    rcases he (u, v) (hs ⟨by simp, hv⟩) with ⟨hr, hphi⟩
    exact congrArg₂ (· * ·) hr hphi
  filter_upwards [primitive_density_agreement hab
    (fun x hx => h₁.radius_out u a x hx.1 (hsub x hx))
    (fun x hx => h₂.radius_out u a x hx.1 (hsub x hx)) hr,
    primitive_density_agreement hab
    (fun x hx => h₁.psi_out u a x hx.1 (hsub x hx))
    (fun x hx => h₂.psi_out u a x hx.1 (hsub x hx)) hpsi] with v hv hV
  exact fun hvi => ⟨hv hvi, hV hvi⟩

/-- Incoming derivative agreement: ν and ∂ᵤψ agree almost everywhere on every common closed incoming
segment, including segments on the terminal ray v = ṽ₀. Paper `e1a0fd5`, lines 1411–1422. -/
theorem incoming_derivatives_agree_ae {D : Set (ℝ × ℝ)} {A : Set ℝ}
    {S₁ S₂ : SSFields} {v a b : ℝ} (hab : a ≤ b) (hs : inSeg v a b ⊆ D)
    (h₁ : ChrBVCore D A S₁) (h₂ : ChrBVCore D A S₂)
    (he : ∀ p ∈ D, S₁.r p.1 p.2 = S₂.r p.1 p.2 ∧
      S₁.phi p.1 p.2 = S₂.phi p.1 p.2) :
    ∀ᵐ u, u ∈ Ioo a b →
      S₁.nu u v = S₂.nu u v ∧ S₁.dupsi u v = S₂.dupsi u v := by
  have hsub (x : ℝ) (hx : x ∈ Icc a b) : inSeg v a x ⊆ D := by
    apply Subset.trans _ hs
    exact prod_mono_left (Icc_subset_Icc le_rfl hx.2)
  have hr : EqOn (fun u => S₁.r u v) (fun u => S₂.r u v) (Icc a b) :=
    fun u hu => (he (u, v) (hs ⟨hu, by simp⟩)).1
  have hpsi : EqOn (fun u => S₁.r u v * S₁.phi u v)
      (fun u => S₂.r u v * S₂.phi u v) (Icc a b) := by
    intro u hu
    rcases he (u, v) (hs ⟨hu, by simp⟩) with ⟨hr, hphi⟩
    exact congrArg₂ (· * ·) hr hphi
  filter_upwards [primitive_density_agreement hab
    (fun x hx => h₁.radius_in v a x hx.1 (hsub x hx))
    (fun x hx => h₂.radius_in v a x hx.1 (hsub x hx)) hr,
    primitive_density_agreement hab
    (fun x hx => h₁.psi_in v a x hx.1 (hsub x hx))
    (fun x hx => h₂.psi_in v a x hx.1 (hsub x hx)) hpsi] with u hu hU
  exact fun hui => ⟨hu hui, hU hui⟩

end AcExtensionPrinciple

end
