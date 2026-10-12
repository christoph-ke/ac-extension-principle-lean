module

public import AcExtensionPrinciple.Observability.Chart
public import AcExtensionPrinciple.BoundaryEnergy.Pointwise

/-!
# Integral and almost everywhere equations in the normalized chart

Paper `e1a0fd5`, `eq:observability-chart-equations` and
`eq:observability-shifted-balance`, lines 1484–1518. Radial derivatives
are represented by their characteristic derivatives multiplied by `r_t`.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory

/-- Scalar amplitude in chart coordinates. Paper `e1a0fd5`,
`equations.tex` lines 1475–1476, `eq:scalar-and-mass-ratio`. -/
@[expose] noncomputable def chartPsi (S : SSFields) (s t : ℝ) : ℝ := S.r s t * S.phi s t

/-- Nonnegative wave potential. Paper `e1a0fd5`,
`eq:observability-chart-equations`, lines 1490–1492. -/
@[expose] noncomputable def chartPotential (S : SSFields) (s t : ℝ) : ℝ :=
  -(S.mu s t * S.nu s t * S.lam s t / ((1 - S.mu s t) * S.r s t ^ 2))

/-- The shifted boundary energy. Paper `e1a0fd5`,
`eq:observability-energy-integral`, lines 1477–1480. -/
@[expose] noncomputable def chartShiftedEnergy (b : ℝ) (S : SSFields) (s : ℝ) : ℝ :=
  boundaryEnergy b (S.m s s) (chartPsi S s s / b)

/-- The wave coefficient equals `-Pψ` off the axis. Paper `e1a0fd5`,
`eq:observability-chart-equations`, lines 1490–1492. -/
theorem chart_wave_coefficient {S : SSFields} {s t : ℝ} (hr : 0 < S.r s t)
    (hgap : 0 < 1 - S.mu s t) :
    S.radiusCoeff s t * S.phi s t = -chartPotential S s t * chartPsi S s t := by
  unfold SSFields.radiusCoeff chartPotential chartPsi
  field_simp

/-- Outgoing mass derivative in radial form. Paper `e1a0fd5`,
`eq:observability-chart-equations`, lines 1485–1486. -/
theorem chart_radial_mass_coefficient {S : SSFields} {s t : ℝ} (hl : 0 < S.lam s t) :
    S.massV s t = (1 - S.mu s t) / 2 * (S.theta s t / S.lam s t) ^ 2 * S.lam s t := by
  unfold SSFields.massV
  field_simp

/-- The incoming mass equation has the printed normalization. Paper `e1a0fd5`,
`eq:observability-chart-equations`, lines 1485–1486. -/
theorem chart_incoming_mass_coefficient (S : SSFields) (s t : ℝ) :
    S.massU s t = (1 - S.mu s t) / (2 * S.nu s t) * S.zeta s t ^ 2 := by
  unfold SSFields.massU
  ring

/-- The expansion equation in radial form. Paper `e1a0fd5`,
`eq:observability-chart-equations`, lines 1488–1489. -/
theorem chart_radial_expansion_coefficient (S : SSFields) (s t : ℝ) :
    S.radiusCoeff s t = S.mu s t * S.nu s t / ((1 - S.mu s t) * S.r s t) * S.lam s t := by
  unfold SSFields.radiusCoeff
  ring

/-- The derivative of `φ = ψ/r` follows from its two primitives. Paper
`e1a0fd5`, `eq:observability-chart-equations`, lines 1484–1492. -/
theorem chart_hasDerivAt_phi_t {S : SSFields} {s t : ℝ} (hr : 0 < S.r s t)
    (hR : HasDerivAt (S.r s) (S.lam s t) t)
    (hΨ : HasDerivAt (chartPsi S s) (S.dvpsi s t) t) :
    HasDerivAt (S.phi s) (S.dvphi s t) t := by
  have hd := hΨ.div hR hr.ne'
  apply (hd.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [hR.continuousAt.eventually_ne hr.ne'] with z hz
    simp [chartPsi, hz]
  · unfold SSFields.dvphi SSFields.theta chartPsi
    field_simp

/-- The incoming scalar derivative likewise follows from `φ = ψ/r`.
Paper `e1a0fd5`, `eq:observability-chart-equations`, lines 1484–1492. -/
theorem chart_hasDerivAt_phi_s {S : SSFields} {s t : ℝ} (hr : 0 < S.r s t)
    (hR : HasDerivAt (fun s => S.r s t) (S.nu s t) s)
    (hΨ : HasDerivAt (fun s => chartPsi S s t) (S.dupsi s t) s) :
    HasDerivAt (fun s => S.phi s t) (S.duphi s t) s := by
  have hd := hΨ.div hR hr.ne'
  apply (hd.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [hR.continuousAt.eventually_ne hr.ne'] with z hz
    simp [chartPsi, hz]
  · unfold SSFields.duphi SSFields.zeta chartPsi
    field_simp

namespace NormalizedChartData

variable {b T K : ℝ} {S : SSFields} (h : NormalizedChartData b T K S)

/-- The potential has the asserted sign. Paper `e1a0fd5`, `eq:observability-chart-equations`, lines
1490–1492; the geometric bounds at line 1451. -/
theorem potential_nonneg {s t : ℝ} (hq : (s, t) ∈ chartCylinder h.g T) :
    0 ≤ chartPotential S s t := by
  have hs := h.signs s t hq
  unfold chartPotential
  exact neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hs.2.2 hs.2.1.le)
      hs.1.le) (mul_nonneg (h.gap_pos hq).le (sq_nonneg _)))

/-- The mixed equation for `ψ_t`, in characteristic integral form. Paper
`e1a0fd5`, `eq:observability-chart-equations`, lines 1490–1492. -/
theorem wave_s_integral {t a c : ℝ} (hac : a ≤ c)
    (hseg : inSeg t a c ⊆ chartInterior (chartCylinder h.g T) S) :
    IntervalPrimitive (fun s => S.dvpsi s t)
      (fun s => -chartPotential S s t * chartPsi S s t) a c := by
  have hi := h.equations.dvpsi_s t a c hac hseg
  have he : ∀ s ∈ uIcc a c, S.radiusCoeff s t * S.phi s t =
      -chartPotential S s t * chartPsi S s t := by
    intro s hs
    rw [uIcc_of_le hac] at hs
    have hq := hseg (show (s, t) ∈ inSeg t a c from ⟨hs, by simp⟩)
    exact chart_wave_coefficient hq.2 (h.gap_pos hq.1)
  refine ⟨hi.1.congr (fun s hs => he s (uIoc_subset_uIcc hs)), ?_⟩
  rw [hi.2]
  exact intervalIntegral.integral_congr he

/-- The mixed equation for `ψ_s`, in characteristic integral form. Paper
`e1a0fd5`, `eq:observability-chart-equations`, lines 1490–1492. -/
theorem wave_t_integral {s a c : ℝ} (hac : a ≤ c)
    (hseg : outSeg s a c ⊆ chartInterior (chartCylinder h.g T) S) :
    IntervalPrimitive (S.dupsi s)
      (fun t => -chartPotential S s t * chartPsi S s t) a c := by
  have hi := h.equations.dupsi_t s a c hac hseg
  have he : ∀ t ∈ uIcc a c, S.radiusCoeff s t * S.phi s t =
      -chartPotential S s t * chartPsi S s t := by
    intro t ht
    rw [uIcc_of_le hac] at ht
    have hq := hseg (show (s, t) ∈ outSeg s a c from ⟨by simp, ht⟩)
    exact chart_wave_coefficient hq.2 (h.gap_pos hq.1)
  refine ⟨hi.1.congr (fun t ht => he t (uIoc_subset_uIcc ht)), ?_⟩
  rw [hi.2]
  exact intervalIntegral.integral_congr he

/-- Radial mass, radial expansion, and `∂ᵣ(rφ_s)` hold almost everywhere on
each positive-radius outgoing segment. Paper `e1a0fd5`,
`eq:observability-chart-equations`, lines 1485–1489. -/
theorem equations_t_ae {s a c : ℝ} (hac : a ≤ c)
    (hseg : outSeg s a c ⊆ chartInterior (chartCylinder h.g T) S) :
    ∀ᵐ t, t ∈ Ioo a c →
      HasDerivAt (S.m s)
        ((1 - S.mu s t) / 2 * (S.theta s t / S.lam s t) ^ 2 * S.lam s t) t ∧
      HasDerivAt (S.nu s)
        (S.mu s t * S.nu s t / ((1 - S.mu s t) * S.r s t) * S.lam s t) t ∧
      HasDerivAt (S.zeta s) (-S.nu s t * S.dvphi s t) t := by
  have hsub {z : ℝ} (hz : z ∈ Icc a c) : outSeg s a z ⊆ chartInterior (chartCylinder h.g T) S :=
    fun q hq => hseg ⟨hq.1, hq.2.1, hq.2.2.trans hz.2⟩
  have hm := intervalPrimitive_ae_hasDerivAt hac (fun z hz =>
    h.equations.mass_t s a z hz.1 (fun q hq => (hsub hz hq).1))
  have hn := intervalPrimitive_ae_hasDerivAt hac (fun z hz => h.equations.nu_t s a z hz.1 (hsub hz))
  have hR := intervalPrimitive_ae_hasDerivAt hac (fun z hz =>
    h.equations.radius_t s a z hz.1 (fun q hq => (hsub hz hq).1))
  have hΨ := intervalPrimitive_ae_hasDerivAt hac (fun z hz =>
    h.equations.psi_t s a z hz.1 (fun q hq => (hsub hz hq).1))
  have hU := intervalPrimitive_ae_hasDerivAt hac (fun z hz =>
    h.equations.dupsi_t s a z hz.1 (hsub hz))
  filter_upwards [hm, hn, hR, hΨ, hU] with t hmt hnt hRt hΨt hUt
  intro ht
  have hq := hseg (show (s, t) ∈ outSeg s a c from ⟨by simp, ht.1.le, ht.2.le⟩)
  have hphi := chart_hasDerivAt_phi_t hq.2 (hRt ht) (hΨt ht)
  refine ⟨(hmt ht).congr_deriv (chart_radial_mass_coefficient (h.signs s t hq.1).1),
    (hnt ht).congr_deriv (chart_radial_expansion_coefficient S s t), ?_⟩
  change HasDerivAt (fun t => S.dupsi s t - S.nu s t * S.phi s t) _ t
  convert (hUt ht).sub ((hnt ht).mul hphi) using 1
  ring

/-- Incoming mass holds almost everywhere on positive-radius segments.
Paper `e1a0fd5`, `eq:observability-chart-equations`, lines 1485–1486. -/
theorem mass_s_ae {t a c : ℝ} (hac : a ≤ c)
    (hseg : inSeg t a c ⊆ chartCylinder h.g T) :
    ∀ᵐ s, s ∈ Ioo a c → HasDerivAt (fun s => S.m s t)
      ((1 - S.mu s t) / (2 * S.nu s t) * S.zeta s t ^ 2) s := by
  have hd := intervalPrimitive_ae_hasDerivAt hac (fun z hz =>
    h.equations.mass_s t a z hz.1 (fun q hq => hseg ⟨⟨hq.1.1, hq.1.2.trans hz.2⟩, hq.2⟩))
  filter_upwards [hd] with s hs
  intro hs'
  exact (hs hs').congr_deriv (chart_incoming_mass_coefficient S s t)

/-- Radial monotonicity compares every enclosed mass with the outer mass.
Paper `e1a0fd5`, `eq:observability-shifted-balance`, lines 1497–1499, 1518. -/
theorem mass_le_boundary {s t : ℝ} (hq : (s, t) ∈ chartCylinder h.g T) :
    S.m s t ≤ S.m s s := by
  have hs : s ∈ Icc 0 T := ⟨hq.1, hq.2.1⟩
  have hi := h.equations.mass_t s t s hq.2.2.2 (h.out_subset hs hq.2.2.1 le_rfl)
  have hp : 0 ≤ ∫ z in t..s, S.massV s z := by
    apply intervalIntegral.integral_nonneg hq.2.2.2
    intro z hz
    have hmem := h.out_subset hs hq.2.2.1 le_rfl
      (show (s, z) ∈ outSeg s t s from ⟨by simp, hz⟩)
    unfold SSFields.massV
    exact div_nonneg (mul_nonneg (h.gap_pos hmem).le (sq_nonneg _))
      (by linarith [(h.signs s z hmem).1])
  linarith [hi.2]

/-- The shifted energy dominates every enclosed mass. Paper `e1a0fd5`,
`eq:observability-shifted-balance`, lines 1497–1499, 1518. -/
theorem mass_le_shiftedEnergy {s t : ℝ} (hq : (s, t) ∈ chartCylinder h.g T) :
    S.m s t ≤ chartShiftedEnergy b S s := by
  have hs : s ∈ Icc 0 T := ⟨hq.1, hq.2.1⟩
  have hμ : massRatio b (S.m s s) < 1 := by
    have hg := h.gap_pos (h.boundary_mem hs)
    rw [SSFields.mu, (h.boundary_gauge s hs).1] at hg
    linarith
  exact (h.mass_le_boundary hq).trans (mass_le_boundaryEnergy h.b_pos hμ)

end NormalizedChartData

end AcExtensionPrinciple

end
