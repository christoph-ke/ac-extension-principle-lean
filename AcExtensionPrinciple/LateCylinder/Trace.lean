module

public import AcExtensionPrinciple.LateCylinder.TraceFields
public import AcExtensionPrinciple.Cylinder.TraceCalculus
public import AcExtensionPrinciple.ACDatum.TailVariation
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# AC and differentiation of the cylinder datum

Paper `e1a0fd5`, `eq:cylinder-datum-derivative`, equations.tex lines
819–822, with the separated rough datum argument at lines 731–737.
Keeping the initial datum composed with the curve avoids pulling an a.e.
identity back to a graph before proving the required trace calculus.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology NNReal

/-- Normalized datum along a cylinder graph. Paper `e1a0fd5`,
`eq:cylinder-datum-derivative`, lines 819–822. -/
@[expose] noncomputable def lateCylinderDatum (S : SSFields) (v : ℝ → ℝ) (u : ℝ) : ℝ :=
  S.dvpsi u (v u) / S.lam u (v u)

/-- Boundary time increment on a cylinder graph. Paper `e1a0fd5`,
`eq:cylinder-time`, lines 671–673, used at lines 823–831. -/
@[expose] noncomputable def lateCylinderTime (S : SSFields) (v : ℝ → ℝ) (a0 a1 : ℝ) : ℝ :=
  ∫ s in a0..a1, -S.nu s (v s)

/-- Compose a continuous total derivative with a differentiable graph.
Paper `e1a0fd5`, chain rule at lines 731–737 and 819–822. -/
theorem late_graph_hasDerivAt {F : ℝ → ℝ → ℝ} {v : ℝ → ℝ} {u Fu Fv d : ℝ}
    (hf : HasFDerivAt (fun p : ℝ × ℝ => F p.1 p.2)
      ((late_cylinderLinear Fu).coprod (late_cylinderLinear Fv)) (u, v u))
    (hv : HasDerivAt v d u) :
    HasDerivAt (fun s => F s (v s)) (Fu + Fv * d) u := by
  have hc : HasDerivAt (fun s : ℝ => (s, v s)) (1, d) u := by
    simpa only [id_eq] using ((hasDerivAt_id u).prodMk hv)
  convert hf.comp_hasDerivAt u hc using 1
  · rfl
  · simp only [ContinuousLinearMap.coprod_apply, late_cylinderLinear,
      ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
    ring

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The expansion and correction restricted to a regular graph are AC.
The graph tangent is supplied by the canonical cylinder theorem.
Paper `e1a0fd5`, lines 731–737. -/
theorem late_smooth_traces_ac {v : ℝ → ℝ} {a0 a1 : ℝ} (ha : a0 ≤ a1)
    (hv : ContinuousOn v (Icc a0 a1))
    (hp : ∀ u ∈ Icc a0 a1, (u, v u) ∈ late_cylinderInterior ui)
    (ht : ∀ u ∈ Icc a0 a1, HasDerivAt v (-S.nu u (v u) / S.lam u (v u)) u) :
    AbsolutelyContinuousOnInterval (fun u => S.lam u (v u)) a0 a1 ∧
      AbsolutelyContinuousOnInterval (fun u => datumCorrection ui S u (v u)) a0 a1 := by
  have hc := continuousOn_id.prodMk hv
  have hD := (h.regularCenter.continuous_nu.mono (late_cylinderInterior_subset ui)).comp hc hp
  have hL := (h.regularCenter.continuous_lam.mono (late_cylinderInterior_subset ui)).comp hc hp
  have hT := hD.neg.div hL (fun u hu => (h.lam_pos
    (late_cylinderInterior_subset ui (hp u hu))).ne')
  have hU := h.late_radiusCoeff_continuous.comp hc hp
  have hP := (h.regularCenter.continuous_phi.mono (late_cylinderInterior_subset ui)).comp hc hp
  have hV := (late_continuousOn_of_rectangles (fun _U _a _b hui hab hU hUa hb =>
    h.lambdaOutgoingDerivative_continuous_rectangle hui hab hU hUa hb)).comp hc hp
  have hC := (late_continuousOn_of_rectangles (fun _U _a _b hui hab hU hUa hb =>
    h.datumCorrectionOutgoingDerivative_continuous_rectangle hui hab hU hUa hb)).comp hc hp
  constructor
  · exact ac_of_continuous_hasDerivAt ha (hU.add (hV.mul hT)) (fun u hu =>
      late_graph_hasDerivAt (h.late_lam_hasStrictFDerivAt (hp u hu)).hasFDerivAt (ht u hu))
  · exact ac_of_continuous_hasDerivAt ha ((hU.mul hP).add (hC.mul hT)) (fun u hu =>
      late_graph_hasDerivAt (h.late_correction_hasStrictFDerivAt (hp u hu)).hasFDerivAt (ht u hu))

/-- AC and the exact separated derivative on any regular monotone Lipschitz
cylinder graph. All graph premises are discharged for cylinderV in
`LateCylinder.Uniform`. Paper `e1a0fd5`,
`eq:cylinder-datum-derivative`, lines 819–822 and 731–737. -/
theorem late_cylinder_trace_calculus {v : ℝ → ℝ} {a0 a1 : ℝ} {Kv : ℝ≥0}
    (ha : a0 ≤ a1) (hv : ContinuousOn v (Icc a0 a1))
    (hmono : MonotoneOn v (Icc a0 a1)) (hLip : LipschitzOnWith Kv v (Icc a0 a1))
    (hp : ∀ u ∈ Icc a0 a1, (u, v u) ∈ late_cylinderInterior ui)
    (ht : ∀ u ∈ Icc a0 a1, HasDerivAt v (-S.nu u (v u) / S.lam u (v u)) u) :
    AbsolutelyContinuousOnInterval (lateCylinderDatum S v) a0 a1 ∧
    AbsolutelyContinuousOnInterval (fun u => S.dvpsi ui (v u)) a0 a1 ∧
    (∀ᵐ u, u ∈ Ioo a0 a1 → deriv (lateCylinderDatum S v) u =
      deriv (fun s => S.dvpsi ui (v s)) u / S.lam u (v u) + (-S.nu u (v u)) *
        (radialDatumRemainderIntegral ui S u (v u) +
          S.varkappa u (v u) / (1 - S.mu u (v u)) * outgoingAmplitude S u (v u))) := by
  have hmaps : MapsTo v (uIcc a0 a1) (uIcc ui 0) := by
    intro u hu
    rw [uIcc_of_le ha] at hu
    rw [uIcc_of_le h.initial_negative.le]
    have hpu := hp u hu
    exact ⟨(hpu.1.trans hpu.2.1).le, hpu.2.2.le⟩
  have hFac := cylinder_ac_comp_monotone_lipschitz h.initial_ac_data
    (by simpa only [uIcc_of_le ha] using hmono)
    (by simpa only [uIcc_of_le ha] using hLip) hmaps
  obtain ⟨hLac, hCac⟩ := h.late_smooth_traces_ac ha hv hp ht
  have hLi := positive_ac_inv hLac (fun u hu =>
    h.lam_pos (late_cylinderInterior_subset ui (hp u (by simpa only [uIcc_of_le ha] using hu))))
  have hRep : ∀ u ∈ Icc a0 a1,
      S.dvpsi ui (v u) + datumCorrection ui S u (v u) = S.dvpsi u (v u) := by
    intro u hu
    have hpu := hp u hu
    exact (h.dvpsi_eq_initial_add_correction hpu.1.le
      (hpu.2.1.trans hpu.2.2) hpu.2.1 hpu.2.2.le).symm
  have hPac : AbsolutelyContinuousOnInterval (lateCylinderDatum S v) a0 a1 := by
    apply ((hFac.fun_add hCac).fun_mul hLi).congr
    intro u hu
    rw [uIcc_of_le ha] at hu
    dsimp only [lateCylinderDatum]
    rw [hRep u hu, div_eq_mul_inv]
  refine ⟨hPac, hFac, ?_⟩
  filter_upwards [hFac.ae_differentiableAt] with u hFu
  intro hu
  have huC := Ioo_subset_Icc_self hu
  have hpu := hp u huC
  have hl := h.lam_pos (late_cylinderInterior_subset ui hpu)
  have hg := (sub_pos.mpr (h.mu_bounds (late_cylinderInterior_subset ui hpu)).2).ne'
  have hFd := (hFu (by simpa only [uIcc_of_le ha] using huC)).hasDerivAt
  have hLd := late_graph_hasDerivAt (h.late_lam_hasStrictFDerivAt hpu).hasFDerivAt (ht u huC)
  have hCd := late_graph_hasDerivAt (h.late_correction_hasStrictFDerivAt hpu).hasFDerivAt (ht u huC)
  have he : lateCylinderDatum S v =ᶠ[𝓝 u]
      (fun s => (S.dvpsi ui (v s) + datumCorrection ui S s (v s)) / S.lam s (v s)) := by
    filter_upwards [Icc_mem_nhds hu.1 hu.2] with s hs
    dsimp only [lateCylinderDatum]
    rw [hRep s hs]
  have hPd := ((hFd.add hCd).div hLd hl.ne').congr_of_eventuallyEq he
  rw [hPd.deriv]
  dsimp only [Pi.add_apply]
  rw [hRep u huC]
  have hR := h.late_smooth_remainder_identity hpu.1.le
    (hpu.2.1.trans hpu.2.2) hpu.2.1 hpu.2.2
  have heq : datumCorrectionOutgoingDerivative ui S u (v u) =
      (S.dvpsi u (v u) / S.lam u (v u)) * lambdaOutgoingDerivative ui S u (v u) +
        S.lam u (v u) ^ 2 * radialDatumRemainderIntegral ui S u (v u) := by linarith
  rw [heq, S.radiusCoeff_eq_lam_gamma]
  dsimp only [SSFields.gamma, gammaOf, SSFields.varkappa, varkappaOf,
    outgoingAmplitude, SSFields.theta]
  field_simp [hl.ne', hg]
  ring

/-- The initial contribution to cylinder variation is bounded by ω(u₀).
This is the monotone change of variables in variation form, which remains
valid for an AC datum. Paper `e1a0fd5`,
`eq:cylinder-initial-tail`, lines 825–831. -/
theorem late_initial_trace_derivative_bound {v : ℝ → ℝ} {a0 a1 u0 : ℝ}
    (ha : a0 ≤ a1) (hu0 : ui ≤ u0) (hu1 : u0 ≤ 0)
    (hmono : MonotoneOn v (Icc a0 a1))
    (hv : MapsTo v (Icc a0 a1) (Icc u0 0))
    (hF : AbsolutelyContinuousOnInterval (fun u => S.dvpsi ui (v u)) a0 a1) :
    (∫ u in a0..a1, |deriv (fun s => S.dvpsi ui (v s)) u|) ≤ initialACTail ui S u0 := by
  have hBV : BoundedVariationOn (fun u => S.dvpsi ui (v u)) (Icc a0 a1) := by
    simpa only [uIcc_of_le ha] using hF.boundedVariationOn
  have hvar : eVariationOn (fun u => S.dvpsi ui (v u)) (Icc a0 a1) ≤
      ENNReal.ofReal (initialACTail ui S u0) := by
    have he : eVariationOn (fun u => S.dvpsi ui (v u)) (Icc a0 a1) =
        eVariationOn (S.dvpsi ui) (v '' Icc a0 a1) := by
      simpa only [Function.comp_def] using
        eVariationOn.comp_eq_of_monotoneOn (S.dvpsi ui) v hmono
    rw [he]
    apply (eVariationOn.mono _ (by rintro _ ⟨u, hu, rfl⟩; exact hv hu)).trans
    exact (h.initialACTail_eq_variation hu0 hu1).le
  exact (integral_abs_deriv_le_variation ha hBV).trans
    ((ENNReal.toReal_mono ENNReal.ofReal_ne_top hvar).trans_eq
      (ENNReal.toReal_ofReal (initialACTail_nonneg hu1)))

end StandingFull

end AcExtensionPrinciple

end
