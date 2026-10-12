module

public import AcExtensionPrinciple.Observability.LemmaA3Scalar

/-!
# Lemma A.3: mass difference along the incoming ray

Paper `e1a0fd5`, `eq:observability-annular-differential`, lines 1593–1603.
The incoming ray is `t=0`; its radius is `S.r s 0`, so its characteristic
mass derivative is already the null derivative in the normalized chart.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory

/-- The quadratic algebra in the annular differential inequality. Paper
`e1a0fd5`, `eq:observability-annular-differential`, lines 1593–1603.
The premises are the lapse and annular scalar bounds. -/
theorem lemmaA3_differential_algebra {q g d D L U V : ℝ}
    (_hq : 0 ≤ q) (hg : 0 < g) (hd : 0 < d)
    (hql : q ≤ g / d) (hs : (V - U) ^ 2 ≤ 2 * D / g * L) :
    q / 2 * U ^ 2 - g / 2 * V ^ 2 ≤
      (2 / d - 1) * (g / 2 * V ^ 2) + 2 * L / d * D := by
  have hsq : U ^ 2 ≤ 2 * V ^ 2 + 4 * D / g * L := by
    simp only [div_eq_mul_inv] at hs ⊢
    nlinarith [sq_nonneg (U - 2 * V)]
  have hmul := mul_le_mul_of_nonneg_left hsq (show 0 ≤ g / d / 2 by positivity)
  have hqmul := mul_le_mul_of_nonneg_right hql (show 0 ≤ U ^ 2 / 2 by positivity)
  have he : g / d / 2 * (2 * V ^ 2 + 4 * D / g * L) =
      2 / d * (g / 2 * V ^ 2) + 2 * L / d * D := by
    field_simp [hg.ne', hd.ne']
    ring
  rw [he] at hmul
  nlinarith

namespace NormalizedChartData

variable {b T K : ℝ} {S : SSFields} (h : NormalizedChartData b T K S)

include h

/-- Both the incoming radius and the mass difference are AC. Paper
`e1a0fd5`, lines 1567–1569, 1593–1603. -/
theorem lemmaA3_ray_ac {τ : ℝ} (hτ : τ ∈ Icc 0 T)
    (hseg : inSeg 0 0 τ ⊆ chartCylinder h.g T) :
    AbsolutelyContinuousOnInterval (fun s => S.r s 0) 0 τ ∧
      AbsolutelyContinuousOnInterval (fun s => S.m s s - S.m s 0) 0 τ := by
  have hsub {s : ℝ} (hs : s ∈ Icc 0 τ) : inSeg 0 0 s ⊆ chartCylinder h.g T :=
    fun q hq => hseg ⟨⟨hq.1.1, hq.1.2.trans hs.2⟩, hq.2⟩
  have hR := intervalPrimitive_ac hτ.1 (fun s hs => h.equations.radius_s 0 0 s hs.1 (hsub hs))
  have hM := intervalPrimitive_ac hτ.1 (fun s hs => h.equations.mass_s 0 0 s hs.1 (hsub hs))
  have hB := h.boundary_traces_ac.2.mono (by
    rw [uIcc_of_le hτ.1, uIcc_of_le h.T_nonneg]
    exact Icc_subset_Icc le_rfl hτ.2)
  exact ⟨hR, hB.sub hM⟩

/-- The derivative of the mass difference is the boundary balance minus the
incoming null mass derivative. Paper `e1a0fd5`, lines 1593–1603. -/
theorem lemmaA3_ray_difference_ae {τ : ℝ} (hτ : τ ∈ Icc 0 T)
    (hseg : inSeg 0 0 τ ⊆ chartCylinder h.g T) :
    ∀ᵐ s, s ∈ Ioo 0 τ →
      HasDerivAt (fun s => S.r s 0) (S.nu s 0) s ∧
      HasDerivAt (fun s => S.m s s - S.m s 0)
        (chartIncomingFluxDensity S s - chartOutgoingFluxDensity S s +
          (1 - S.mu s 0) / (-2 * S.nu s 0) * S.zeta s 0 ^ 2) s := by
  have hR := intervalPrimitive_ae_hasDerivAt hτ.1 (fun s hs =>
    h.equations.radius_s 0 0 s hs.1 (fun q hq => hseg ⟨⟨hq.1.1, hq.1.2.trans hs.2⟩, hq.2⟩))
  filter_upwards [hR, h.boundary_mass_ae_hasDerivAt, h.mass_s_ae hτ.1 hseg] with s hr hb hm hs
  have hsT : s ∈ Icc 0 T := ⟨hs.1.le, hs.2.le.trans hτ.2⟩
  refine ⟨hr hs, ?_⟩
  apply ((hb hsT).sub (hm hs)).congr_deriv
  have hg := h.boundary_gauge s hsT
  unfold chartIncomingFluxDensity chartOutgoingFluxDensity SSFields.massU SSFields.massV
  rw [hg.2.1, hg.2.2]
  ring

/-- The exact paper differential inequality along the incoming ray, with
lapse and scalar estimates discharged from the chart. Paper `e1a0fd5`,
`eq:observability-annular-differential`, lines 1593–1603. -/
theorem lemmaA3_annular_differential {s p : ℝ}
    (hq : (s, 0) ∈ chartInterior (chartCylinder h.g T) S)
    (hm : ∀ z ∈ Icc 0 s, S.m s z ≤ p) (hp : 2 * p < S.r s 0)
    (hd : HasDerivAt (fun s => S.m s s - S.m s 0)
      (chartIncomingFluxDensity S s - chartOutgoingFluxDensity S s +
        (1 - S.mu s 0) / (-2 * S.nu s 0) * S.zeta s 0 ^ 2) s) :
    deriv (fun s => S.m s s - S.m s 0) s ≤
      chartIncomingFluxDensity S s + (2 / (1 - 2 * p / S.r s 0) - 1) *
        chartOutgoingFluxDensity S s +
        2 * ((S.r s 0)⁻¹ - b⁻¹) / (1 - 2 * p / S.r s 0) * (S.m s s - S.m s 0) := by
  have hl := h.lemmaA3_annular_lapse_bounds hq hm hp
  have hscalar := h.lemmaA3_annular_scalar hq
  have hn : 0 < -S.nu s 0 := neg_pos.mpr (h.signs s 0 hq.1).2.1
  have hg := h.gap_pos hq.1
  have hgb := h.gap_pos (h.boundary_mem ⟨hq.1.1, hq.1.2.1⟩)
  have hdpos : 0 < 1 - 2 * p / S.r s 0 := sub_pos.mpr ((div_lt_one hq.2).mpr hp)
  have ha := lemmaA3_differential_algebra (div_pos hg hn).le hgb hdpos hl.2 hscalar
  have he : (1 - S.mu s 0) / (-S.nu s 0) / 2 = (1 - S.mu s 0) / (-2 * S.nu s 0) := by ring
  rw [he] at ha
  rw [hd.deriv]
  unfold chartOutgoingFluxDensity at *
  linarith

end NormalizedChartData

end AcExtensionPrinciple

end
