module

public import AcExtensionPrinciple.Observability.InnerChartCalculus
public import AcExtensionPrinciple.Observability.ChartMassRegularity

/-!
# Uniform annular bounds from the normalized chart

Paper `e1a0fd5`, `equations.tex` line 1522 and lines 1877–1907.
Uniform scalar BV bounds control the quadratic mass densities even when
their representatives have jumps.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory

/-- The outgoing logarithmic incoming-expansion coefficient. Paper
`e1a0fd5`, `eq:logarithmic-expansions`, lines 1460–1473 and 1901. -/
@[expose] noncomputable def innerNuCoefficient (S : SSFields) (s t : ℝ) : ℝ :=
  innerExpansionCoefficient (S.r s t, S.m s t, S.lam s t)

/-- The incoming logarithmic outgoing-expansion coefficient. Paper
`e1a0fd5`, `eq:logarithmic-expansions`, lines 1460–1473 and 1901. -/
@[expose] noncomputable def innerLamCoefficient (S : SSFields) (s t : ℝ) : ℝ :=
  innerExpansionCoefficient (S.r s t, S.m s t, S.nu s t)

namespace NormalizedChartData

variable {b T K : ℝ} {S : SSFields} (h : NormalizedChartData b T K S)

/-- The compact annular part consisting of entered rays and r≥δ.
Paper `e1a0fd5`, lines 1877–1907 and 1522. -/
@[expose] def innerAnnulus (δ : ℝ) : Set (ℝ × ℝ) :=
  {p | p ∈ chartCylinder h.g T ∧ δ ≤ S.r p.1 p.2 ∧ 0 ≤ p.2}

/-- The closed annulus is compact. Paper `e1a0fd5`, lines 1522 and 1901. -/
theorem innerAnnulus_compact (δ : ℝ) : IsCompact (h.innerAnnulus δ) := by
  let D := chartCylinder h.g T
  obtain ⟨R, hR⟩ := (⟨_, h.continuous_r.domRestrict⟩ : C(D, ℝ)).exists_restrict_eq
    h.inner_source_compact.isClosed
  have heq (p : ℝ × ℝ) (hp : p ∈ D) : R p = S.r p.1 p.2 :=
    congrArg (fun G : C(D, ℝ) => G ⟨p, hp⟩) hR
  have he : h.innerAnnulus δ = (D ∩ R ⁻¹' Ici δ) ∩ {p | 0 ≤ p.2} := by
    ext p
    constructor
    · intro hp
      refine ⟨⟨hp.1, ?_⟩, hp.2.2⟩
      change δ ≤ R p
      rw [heq p hp.1]
      exact hp.2.1
    · intro hp
      have hh : δ ≤ R p := hp.1.2
      rw [heq p hp.1.1] at hh
      exact ⟨hp.1.1, hh, hp.2⟩
  rw [he]
  exact (h.inner_source_compact.inter_right (isClosed_Ici.preimage R.continuous)).inter_right
    (isClosed_le continuous_const continuous_snd)

/-- A positive closed annulus is an off-axis source domain. Paper
`e1a0fd5`, lines 1522 and 1901. -/
theorem innerAnnulus_subset {δ : ℝ} (hδ : 0 < δ) :
    h.innerAnnulus δ ⊆ chartInterior (chartCylinder h.g T) S :=
  fun _ hp => ⟨hp.1, hδ.trans_le hp.2.1⟩

/-- Both logarithmic coefficients are continuous on the annulus. Paper
`e1a0fd5`, `eq:logarithmic-expansions`, lines 1460–1473 and 1901. -/
theorem inner_coefficients_continuous {δ : ℝ} (hδ : 0 < δ) :
    ContinuousOn (fun p => innerNuCoefficient S p.1 p.2) (h.innerAnnulus δ) ∧
      ContinuousOn (fun p => innerLamCoefficient S p.1 p.2) (h.innerAnnulus δ) := by
  have hs := h.innerAnnulus_subset hδ
  have hg := h.geometry_continuous_on hs
  have hr : ContinuousOn (fun p => S.r p.1 p.2) (h.innerAnnulus δ) :=
    h.continuous_r.mono (fun p hp => hp.1)
  have hden : ∀ p ∈ h.innerAnnulus δ, (1 - S.mu p.1 p.2) * S.r p.1 p.2 ≠ 0 :=
    fun p hp => mul_ne_zero (h.gap_pos hp.1).ne' (hs hp).2.ne'
  constructor
  · apply ((hg.1.mul hg.2.2.1).div ((continuousOn_const.sub hg.1).mul hr) hden).congr
    intro p hp
    exact innerExpansionCoefficient_eq S (hs hp).2.ne' (h.gap_pos hp.1).ne'
  · apply ((hg.1.mul hg.2.1).div ((continuousOn_const.sub hg.1).mul hr) hden).congr
    intro p hp
    exact innerExpansionCoefficient_eq S (hs hp).2.ne' (h.gap_pos hp.1).ne'

/-- All fields, primitive densities, and logarithmic coefficients have
a common annular bound. The scalar derivative fields use characteristic
BV bounds; their continuity is unnecessary. Paper `e1a0fd5`, line 1522
and lines 1460–1473, 1901. -/
theorem inner_annular_bounds {δ : ℝ} (hδ : 0 < δ) : ∃ B : ℝ, 0 ≤ B ∧
    ∀ p ∈ h.innerAnnulus δ,
      |S.r p.1 p.2| ≤ B ∧ |S.m p.1 p.2| ≤ B ∧
      |S.lam p.1 p.2| ≤ B ∧ |S.nu p.1 p.2| ≤ B ∧
      |S.massU p.1 p.2| ≤ B ∧ |S.massV p.1 p.2| ≤ B ∧
      |S.radiusCoeff p.1 p.2| ≤ B ∧
      |innerNuCoefficient S p.1 p.2| ≤ B ∧ |innerLamCoefficient S p.1 p.2| ≤ B := by
  let A := h.innerAnnulus δ
  have hc := h.innerAnnulus_compact δ
  have hs := h.innerAnnulus_subset hδ
  have hg := h.geometry_continuous_on hs
  obtain ⟨M, hM, hb⟩ := h.inner_source_scalar_bound
  obtain ⟨U, hU, hbU⟩ := chart_quadratic_bound (U := fun p => S.dupsi p.1 p.2)
    (A := fun p => (1 - S.mu p.1 p.2) / (2 * S.nu p.1 p.2))
    (D := fun p => S.nu p.1 p.2 * S.phi p.1 p.2) hc hM
    (fun p hp => (hb _ _ hp.1 hp.2.2).1)
    ((continuousOn_const.sub hg.1).div (continuousOn_const.mul hg.2.1)
      (fun p hp => mul_ne_zero (by norm_num) (h.signs _ _ hp.1).2.1.ne))
    (hg.2.1.mul hg.2.2.2)
  obtain ⟨V, hV, hbV⟩ := chart_quadratic_bound (U := fun p => S.dvpsi p.1 p.2)
    (A := fun p => (1 - S.mu p.1 p.2) / (2 * S.lam p.1 p.2))
    (D := fun p => S.lam p.1 p.2 * S.phi p.1 p.2) hc hM
    (fun p hp => (hb _ _ hp.1 hp.2.2).2)
    ((continuousOn_const.sub hg.1).div (continuousOn_const.mul hg.2.2.1)
      (fun p hp => mul_ne_zero (by norm_num) (h.signs _ _ hp.1).1.ne'))
    (hg.2.2.1.mul hg.2.2.2)
  have hr : ContinuousOn (fun p => S.r p.1 p.2) A :=
    h.continuous_r.mono (fun p hp => hp.1)
  have hm : ContinuousOn (fun p => S.m p.1 p.2) A :=
    h.continuous_m.mono (fun p hp => hp.1)
  have hrc : ContinuousOn (fun p => S.radiusCoeff p.1 p.2) A :=
    ((hg.1.mul hg.2.2.1).mul hg.2.1).div ((continuousOn_const.sub hg.1).mul hr)
      (fun p hp => mul_ne_zero (h.gap_pos hp.1).ne' (hs hp).2.ne')
  obtain ⟨R, hbR⟩ := hc.exists_bound_of_continuousOn hr
  obtain ⟨N, hbN⟩ := hc.exists_bound_of_continuousOn hm
  obtain ⟨L, hbL⟩ := hc.exists_bound_of_continuousOn hg.2.2.1
  obtain ⟨F, hbF⟩ := hc.exists_bound_of_continuousOn hg.2.1
  obtain ⟨C, hbC⟩ := hc.exists_bound_of_continuousOn hrc
  obtain ⟨D, hbD⟩ := hc.exists_bound_of_continuousOn (h.inner_coefficients_continuous hδ).1
  obtain ⟨E, hbE⟩ := hc.exists_bound_of_continuousOn (h.inner_coefficients_continuous hδ).2
  let B := |R| + |N| + |L| + |F| + U + V + |C| + |D| + |E|
  refine ⟨B, by dsimp [B]; positivity, ?_⟩
  intro p hp
  have hR := (hbR p hp).trans (le_abs_self R)
  have hN := (hbN p hp).trans (le_abs_self N)
  have hL := (hbL p hp).trans (le_abs_self L)
  have hF := (hbF p hp).trans (le_abs_self F)
  have hC := (hbC p hp).trans (le_abs_self C)
  have hD := (hbD p hp).trans (le_abs_self D)
  have hE := (hbE p hp).trans (le_abs_self E)
  simp only [Real.norm_eq_abs] at hR hN hL hF hC hD hE
  have hu : |S.massU p.1 p.2| ≤ U := by
    simpa only [SSFields.massU, SSFields.zeta, div_mul_eq_mul_div] using hbU p hp
  have hv : |S.massV p.1 p.2| ≤ V := by
    simpa only [SSFields.massV, SSFields.theta, div_mul_eq_mul_div] using hbV p hp
  dsimp only [B]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    linarith [abs_nonneg R, abs_nonneg N, abs_nonneg L, abs_nonneg F,
      abs_nonneg C, abs_nonneg D, abs_nonneg E]

/-- The geometric gap places every annular field triple in the same
convex positive-denominator box. Paper `e1a0fd5`, lines 1460–1473 and 1901. -/
theorem inner_coefficient_box_mem {δ B s t E : ℝ} (hδ : 0 < δ)
    (hp : (s, t) ∈ h.innerAnnulus δ)
    (hr : |S.r s t| ≤ B) (hm : |S.m s t| ≤ B) (hE : |E| ≤ B) :
    (S.r s t, S.m s t, E) ∈ innerCoefficientBox δ (δ / K) B := by
  have hK : 0 < K := zero_lt_one.trans_le h.K_ge_one
  have hrg : S.r s t - 2 * S.m s t = S.r s t * (1 - S.mu s t) := by
    unfold SSFields.mu massRatio
    field_simp [(hδ.trans_le hp.2.1).ne']
  refine ⟨hp.2.1, ?_, hr, hm, hE⟩
  rw [hrg]
  calc
    δ / K = δ * K⁻¹ := div_eq_mul_inv _ _
    _ ≤ S.r s t * K⁻¹ := mul_le_mul_of_nonneg_right hp.2.1 (inv_nonneg.mpr hK.le)
    _ ≤ S.r s t * (1 - S.mu s t) :=
      mul_le_mul_of_nonneg_left (h.gap s t hp.1) (hδ.trans_le hp.2.1).le

end NormalizedChartData

end AcExtensionPrinciple

end
