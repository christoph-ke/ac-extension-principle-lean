module

public import AcExtensionPrinciple.Observability.LemmaA3Observation

/-!
# Lemma A.3: wave identities after constant scalar translation

Paper `e1a0fd5`, `equations.tex` line 1540 and lines 1650–1663.
The translated amplitude is `ψ+q r`. The proof uses the radius primitive
and the original wave primitive, so it needs no extra BV premise for
translated characteristic derivatives.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory

/-- Amplitude after translating φ by `q`. Paper `e1a0fd5`, line 1540. -/
@[expose] noncomputable def chartTranslatedPsi (S : SSFields) (q s t : ℝ) : ℝ :=
  chartPsi S s t + q * S.r s t

/-- Observed energy after a constant scalar translation. Paper `e1a0fd5`,
line 1540, `eq:observability-energy-integral`, lines 1477–1480. The boundary
trace translates by the constant `q b`, so its derivative is unchanged. -/
@[expose] noncomputable def chartTranslatedEnergy (S : SSFields) (T q : ℝ) : ℝ :=
  ∫ s in 0..T, (S.dvpsi s s + q) ^ 2 + deriv (fun s => chartPsi S s s) s ^ 2

namespace NormalizedChartData

variable {b T K : ℝ} {S : SSFields} (h : NormalizedChartData b T K S)

include h

/-- The translated boundary trace is AC, with its original derivative.
Paper `e1a0fd5`, line 1540 and lines 1650–1655. -/
theorem lemmaA3_translated_boundary_ac (q : ℝ) :
    AbsolutelyContinuousOnInterval (fun s => chartPsi S s s + q * b) 0 T := by
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => q * b) 0 T :=
    (LipschitzWith.const _).lipschitzOnWith.absolutelyContinuousOnInterval
  exact h.boundary_traces_ac.1.fun_add hc

/-- Translation preserves finite observed square integrability. Paper
`e1a0fd5`, line 1540 and the local AC/BV justification at line 1522. -/
theorem lemmaA3_translated_square_integrable (q : ℝ) :
    IntervalIntegrable (fun s => (S.dvpsi s s + q) ^ 2) volume 0 T := by
  have hi := (h.boundary_scalar_square_integrable.2.add
    (h.boundary_dvpsi_integrable.const_mul (2 * q))).add
    (show IntervalIntegrable (fun _ : ℝ => q ^ 2) volume 0 T from intervalIntegrable_const)
  convert hi using 1
  funext s
  ring

/-- The translated amplitude satisfies the same positive-kernel Volterra
formula. Paper `e1a0fd5`, line 1540, `eq:observability-volterra`, lines 1504–1522. -/
theorem lemmaA3_translated_volterra (q : ℝ) {s t : ℝ} (ht : 0 ≤ t)
    (hq : (s, t) ∈ chartInterior (chartCylinder h.g T) S) :
    chartTranslatedPsi S q s t = chartPsi S s s + q * b -
      (∫ σ in t..s, S.dvpsi σ σ + q) +
      triangleVolterra (fun x => chartPotential S x.1 x.2)
        (fun x => chartTranslatedPsi S q x.1 x.2) s t := by
  have hts := hq.1.2.2.2
  have hsT := hq.1.2.1
  have htri := h.volterra_triangle_subset ht hq
  have hΨ : ContinuousOn (fun x => chartTranslatedPsi S q x.1 x.2) (chartTriangle t s) :=
    (h.continuous_psi.mono (fun x hx => (htri hx).1)).add
      (continuousOn_const.mul (h.continuous_r.mono (fun x hx => (htri hx).1)))
  have hprod := (h.continuous_potential_on htri).mul hΨ
  obtain ⟨Q, hQ, hQeq⟩ := chartTriangle_continuous_extension hprod
  let J : ℝ → ℝ := fun σ => ∫ z in t..σ, Q (σ, z)
  have hJ : Continuous J := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (f := fun σ z => Q (σ, z)) hQ continuous_id
  have hJeq (σ : ℝ) (hσ : σ ∈ Icc t s) : J σ =
      ∫ z in t..σ, chartPotential S σ z * chartTranslatedPsi S q σ z := by
    apply intervalIntegral.integral_congr
    intro z hz
    rw [uIcc_of_le hσ.1] at hz
    exact hQeq (σ, z) ⟨hz.1, hz.2, hσ.2⟩
  have hsub {σ : ℝ} (hσ : σ ∈ Icc t s) : inSeg t t σ ⊆ chartInterior (chartCylinder h.g T) S :=
    (chartTriangle_in_subset le_rfl le_rfl hσ.2).trans htri
  have hψAC := intervalPrimitive_ac hts (fun σ hσ =>
    h.equations.psi_s t t σ hσ.1 (fun x hx => (hsub hσ hx).1))
  have hrAC := intervalPrimitive_ac hts (fun σ hσ =>
    h.equations.radius_s t t σ hσ.1 (fun x hx => (hsub hσ hx).1))
  have hψDer := intervalPrimitive_ae_hasDerivAt hts (fun σ hσ =>
    h.equations.psi_s t t σ hσ.1 (fun x hx => (hsub hσ hx).1))
  have hrDer := intervalPrimitive_ae_hasDerivAt hts (fun σ hσ =>
    h.equations.radius_s t t σ hσ.1 (fun x hx => (hsub hσ hx).1))
  have hcharAC : AbsolutelyContinuousOnInterval (fun σ => chartTranslatedPsi S q σ t) t s :=
    hψAC.fun_add (hrAC.const_mul q)
  have hboundaryAC := (h.lemmaA3_translated_boundary_ac q).mono (by
    rw [uIcc_of_le hts, uIcc_of_le h.T_nonneg]
    exact Icc_subset_Icc ht hsT)
  have hF : AbsolutelyContinuousOnInterval
      (fun σ => chartTranslatedPsi S q σ t - (chartPsi S σ σ + q * b)) t s :=
    hcharAC.sub hboundaryAC
  have hder : ∀ᵐ σ, σ ∈ Ioo t s → HasDerivAt
      (fun σ => chartTranslatedPsi S q σ t - (chartPsi S σ σ + q * b))
      (-(S.dvpsi σ σ + q) + J σ) σ := by
    filter_upwards [hψDer, hrDer, h.boundary_psi_ae_hasDerivAt] with σ hψ hr hb hσ
    have hσI : σ ∈ Icc t s := ⟨hσ.1.le, hσ.2.le⟩
    have hσT : σ ∈ Icc 0 T := ⟨ht.trans hσ.1.le, hσ.2.le.trans hsT⟩
    have hseg := (chartTriangle_out_subset le_rfl le_rfl hσ.2.le).trans htri
    have hi := h.equations.dupsi_t σ t σ hσ.1.le hseg
    have hn := h.equations.nu_t σ t σ hσ.1.le hseg
    have hw : (S.dupsi σ σ + q * S.nu σ σ) - (S.dupsi σ t + q * S.nu σ t) = -J σ := by
      rw [hJeq σ hσI]
      have heq : ∀ z ∈ uIcc t σ, S.radiusCoeff σ z * S.phi σ z + q * S.radiusCoeff σ z =
          -(chartPotential S σ z * chartTranslatedPsi S q σ z) := by
        intro z hz
        rw [uIcc_of_le hσ.1.le] at hz
        have hm := hseg (show (σ, z) ∈ outSeg σ t σ from ⟨by simp, hz⟩)
        have he := chart_wave_coefficient (S := S) hm.2 (h.gap_pos hm.1)
        have her : S.radiusCoeff σ z = -chartPotential S σ z * S.r σ z := by
          unfold SSFields.radiusCoeff chartPotential
          field_simp [hm.2.ne']
        rw [he, her]
        unfold chartTranslatedPsi
        ring
      have he := intervalIntegral.integral_congr (μ := volume) heq
      rw [intervalIntegral.integral_add hi.1 (hn.1.const_mul q),
        intervalIntegral.integral_const_mul, ← hi.2, ← hn.2, intervalIntegral.integral_neg] at he
      linarith
    have hd := ((hψ hσ).add ((hr hσ).const_mul q)).sub ((hb hσT).add_const (q * b))
    change HasDerivAt (fun σ => chartTranslatedPsi S q σ t - (chartPsi S σ σ + q * b))
      (S.dupsi σ t + q * S.nu σ t - (S.dupsi σ σ + S.dvpsi σ σ)) σ at hd
    rw [(h.boundary_gauge σ hσT).2.1] at hw
    exact hd.congr_deriv (by linarith)
  have hi := (ac_integral_eq_sub hts hF hder).2
  have hxi : IntervalIntegrable (fun σ => S.dvpsi σ σ + q) volume t s := (h.boundary_dvpsi_integrable.add intervalIntegrable_const).mono_set (by
    rw [uIcc_of_le hts, uIcc_of_le h.T_nonneg]
    exact Icc_subset_Icc ht hsT)
  have hstart : chartTranslatedPsi S q t t = chartPsi S t t + q * b := by
    rw [chartTranslatedPsi, (h.boundary_gauge t ⟨ht, hts.trans hsT⟩).1]
  change chartTranslatedPsi S q s t - (chartPsi S s s + q * b) -
    (chartTranslatedPsi S q t t - (chartPsi S t t + q * b)) =
      ∫ σ in t..s, -(S.dvpsi σ σ + q) + J σ at hi
  rw [hstart, sub_self, sub_zero, intervalIntegral.integral_add (f := fun σ => -(S.dvpsi σ σ + q)) hxi.neg (hJ.intervalIntegrable t s),
    intervalIntegral.integral_neg] at hi
  have hJint : (∫ σ in t..s, J σ) = triangleVolterra (fun x => chartPotential S x.1 x.2)
      (fun x => chartTranslatedPsi S q x.1 x.2) s t := by
    apply intervalIntegral.integral_congr
    intro σ hσ
    rw [uIcc_of_le hts] at hσ
    exact hJeq σ hσ
  rw [hJint] at hi
  linarith

end NormalizedChartData

end AcExtensionPrinciple

end
