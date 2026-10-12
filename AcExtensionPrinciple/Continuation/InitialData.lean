module

public import AcExtensionPrinciple.Continuation.Domain
public import AcExtensionPrinciple.Gauge.Variation
public import AcExtensionPrinciple.Gauge.Primitive

/-!
# Reconstructing the scalar data on the selected cone

Components for paper `e1a0fd5`, `equations.tex`
`eq:continuation-initial-datum` and line 1404. The argument uses primitives
strictly off the axis and a zero limit there; it needs no mass datum.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- Equal derivative data determine a primitive on a punctured interval once
its zero axis limit is fixed. Paper `e1a0fd5`, line 1404. -/
theorem punctured_primitive_unique {f F g : ℝ → ℝ} {b : ℝ}
    (hf : ∀ x y, 0 < x → x ≤ y → y ≤ b → IntervalPrimitive f g x y)
    (hF : ∀ x y, 0 < x → x ≤ y → y ≤ b → IntervalPrimitive F g x y)
    (hf0 : Tendsto f (𝓝[>] 0) (𝓝 0)) (hF0 : Tendsto F (𝓝[>] 0) (𝓝 0)) :
    ∀ v ∈ Ioc 0 b, f v = F v := by
  intro v hv
  have hconst : ∀ᶠ x in 𝓝[>] (0 : ℝ), f x - F x = f v - F v := by
    filter_upwards [Ioo_mem_nhdsGT hv.1] with x hx
    have he := (hf x v hx.1 hx.2.le hv.2).2
    have hE := (hF x v hx.1 hx.2.le hv.2).2
    linarith
  have ht : Tendsto (fun _ : ℝ => f v - F v) (𝓝[>] 0) (𝓝 0) := by
    simpa using (hf0.sub hF0).congr' hconst
  have he : f v - F v = 0 := tendsto_nhds_unique tendsto_const_nhds ht
  linarith

/-- Finite scalar variation and the radius axis limit force ψ to vanish at
the initial vertex. Paper `e1a0fd5`, line 1404, `eq:regular-axis`.
This also applies to the development without assuming continuity at Γ. -/
theorem ChristodoulouBV.initial_psi_limit {D : Set (ℝ × ℝ)} {A : Set ℝ}
    {S : SSFields} {b : ℝ} (h : ChristodoulouBV D A S) (hb : 0 < b)
    (hcone : ∀ v ∈ Ioc 0 b, (0, v) ∈ D) (haxis : 0 ∈ A) :
    Tendsto (fun v => S.r 0 v * S.phi 0 v) (𝓝[>] 0) (𝓝 0) := by
  rcases h.2.variation_bounds with ⟨C, hout, _⟩
  have hs : Ioc 0 b ⊆ {v | (0, v) ∈ (univ : Set (ℝ × ℝ)) ∩ D} :=
    fun v hv => ⟨mem_univ _, hcone v hv⟩
  have hTV : BoundedVariationOn (S.phi 0) (Ioc 0 b) :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((eVariationOn.mono _ hs).trans (hout 0).2.1)
  have hbound : ∀ᶠ v in 𝓝[>] (0 : ℝ), |S.phi 0 v| ≤
      (eVariationOn (S.phi 0) (Ioc 0 b)).toReal + |S.phi 0 b| := by
    filter_upwards [Ioo_mem_nhdsGT hb] with v hv
    exact boundedVariation_abs_bound hTV ⟨hv.1, hv.2.le⟩ ⟨hb, le_rfl⟩
  have hfilter : 𝓝[>] (0 : ℝ) ≤ 𝓟 {v | (0, v) ∈ D} := by
    apply le_principal_iff.mpr
    filter_upwards [Ioo_mem_nhdsGT hb] with v hv
    exact hcone v ⟨hv.1, hv.2.le⟩
  have hr := (h.1.radius_axis_limit 0 haxis).mono_left (le_inf le_rfl hfilter)
  simpa only [mul_comm] using bdd_le_mul_tendsto_zero' _ hbound hr

/-- Equal radius and equal derivative datum, together with ψ = 0 at Γ, give equal scalar fields on
the initial segment. Paper `e1a0fd5`, line 1404. The positive radius premise is discharged by r =
ṽ/2. -/
theorem initial_scalar_agreement {S₁ S₂ : SSFields} {b : ℝ}
    (h₁ : ChrBVCore (pastSet 0 b) (adjacentAxis (pastSet 0 b)) S₁)
    (h₂ : ChrBVCore (pastSet 0 b) (adjacentAxis (pastSet 0 b)) S₂)
    (hr : ∀ v ∈ Ioc 0 b, S₁.r 0 v = S₂.r 0 v)
    (hpos : ∀ v ∈ Ioc 0 b, S₁.r 0 v ≠ 0)
    (hd : ∀ v ∈ Ioc 0 b, S₁.dvpsi 0 v = S₂.dvpsi 0 v)
    (hψ₁ : Tendsto (fun v => S₁.r 0 v * S₁.phi 0 v) (𝓝[>] 0) (𝓝 0))
    (hψ₂ : Tendsto (fun v => S₂.r 0 v * S₂.phi 0 v) (𝓝[>] 0) (𝓝 0)) :
    ∀ v ∈ Ioc 0 b, S₁.phi 0 v = S₂.phi 0 v := by
  have hs (x y : ℝ) (hx : 0 < x) (hy : y ≤ b) : outSeg 0 x y ⊆ pastSet 0 b := by
    rintro ⟨u, v⟩ ⟨hu, hv⟩
    simp only [mem_singleton_iff] at hu
    subst u
    exact ⟨⟨le_rfl, le_rfl⟩, hx.trans_le hv.1, hv.2.trans hy⟩
  have he := punctured_primitive_unique
    (fun x y hx hxy hy => h₁.psi_out 0 x y hxy (hs x y hx hy))
    (fun x y hx hxy hy => (h₂.psi_out 0 x y hxy (hs x y hx hy)).congr
      (fun _ _ => rfl) (fun v hv => (hd v (by
        rw [uIcc_of_le hxy] at hv
        exact ⟨hx.trans_le hv.1, hv.2.trans hy⟩)).symm)) hψ₁ hψ₂
  intro v hv
  have he' := he v hv
  rw [← hr v hv] at he'
  exact mul_left_cancel₀ (hpos v hv) he'

/-- Initial cone data in the radial gauge agree in precisely the sense E2
requires. Paper `e1a0fd5`, `eq:continuation-initial-datum`, line 1404.
Mass reconstruction is therefore unnecessary for the uniqueness step. -/
theorem initial_data_agreement {S₁ S₂ : SSFields} {b : ℝ} (hb : 0 < b)
    (h₁ : ChristodoulouBV (pastSet 0 b) (adjacentAxis (pastSet 0 b)) S₁)
    (h₂ : ChristodoulouBV smallBVDomain (Ici 0) S₂)
    (hr₁ : ∀ v ∈ Ioc 0 b, S₁.r 0 v = v / 2)
    (hr₂ : ∀ v ∈ Ioc 0 b, S₂.r 0 v = v / 2)
    (hd : ∀ v ∈ Ioc 0 b, S₁.dvpsi 0 v = S₂.dvpsi 0 v) :
    ∀ v ∈ Ioc 0 b, S₁.r 0 v = S₂.r 0 v ∧ S₁.phi 0 v = S₂.phi 0 v := by
  have hcone : ∀ v ∈ Ioc 0 b, (0, v) ∈ pastSet 0 b :=
    fun _ hv => ⟨⟨le_rfl, le_rfl⟩, hv⟩
  have hr : ∀ v ∈ Ioc 0 b, S₁.r 0 v = S₂.r 0 v :=
    fun v hv => (hr₁ v hv).trans (hr₂ v hv).symm
  have hphi := initial_scalar_agreement h₁.1 (h₂.on_pastSet 0 b).1 hr
    (fun v hv => by rw [hr₁ v hv]; exact ne_of_gt (div_pos hv.1 (by norm_num))) hd
    (h₁.initial_psi_limit hb hcone (zero_mem_pastSet_adjacentAxis le_rfl hb))
    (h₂.initial_psi_limit hb (fun v hv => ⟨le_rfl, hv.1⟩) (by simp))
  exact fun v hv => ⟨hr v hv, hphi v hv⟩

end AcExtensionPrinciple

end
