module

public import AcExtensionPrinciple.Weighted.ClassKernels
public import AcExtensionPrinciple.Weighted.ClassWeights

/-!
# Flux control of the transported-datum kernel

Paper `e1a0fd5`, `lem:weighted-radial-estimates`,
`equations.tex` lines 1189–1201. The actual incoming amplitude is retained
inside the kernel and its quadratic incoming flux supplies the bound.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory
open scoped ENNReal

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- A single kernel's outgoing squared norm is bounded by its incoming
flux density. Paper `e1a0fd5`, lines 1193–1199. -/
theorem weighted_transport_kernel_cone_le {u a δ : ℝ}
    (hu : ui ≤ u) (hu0 : u < 0) (hua : u < a) (ha0 : a ≤ 0) (hδ : δ < 3)
    (hsmall : ∀ v ∈ Icc a 0, S.mu u v / (1 - S.mu u v) ≤ δ) :
    (∫⁻ v in Ioc u 0, ENNReal.ofReal
      ((-S.nu u v) * S.lam u v * |weightedTransportKernel S a (u, v)| ^ 2)) ≤
      ENNReal.ofReal (S.incomingFlux u a / (3 - δ)) := by
  let A := weightedIncomingAmplitude S u a
  have he : (fun v => ENNReal.ofReal
      ((-S.nu u v) * S.lam u v * |weightedTransportKernel S a (u, v)| ^ 2)) =
      (Ioi a).indicator (fun v => ENNReal.ofReal (A ^ 2) * ENNReal.ofReal
        ((-S.nu u v) * S.lam u v * S.r u a ^ 2 / S.r u v ^ 4)) := by
    funext v
    by_cases hav : a < v
    · simp only [weightedTransportKernel, hua, hav, and_self, ite_true]
      rw [indicator_of_mem (show v ∈ Ioi a from hav)]
      rw [← ENNReal.ofReal_mul (sq_nonneg A), sq_abs, mul_pow, div_pow]
      congr 1
      dsimp only [A]
      simp only [div_eq_mul_inv, ← pow_mul]
      ring
    · simp [weightedTransportKernel, hav, indicator, mem_Ioi]
  have hs : Ioi a ∩ Ioc u 0 = Ioc a 0 := by
    ext v
    simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
    constructor
    · tauto
    · intro hv
      exact ⟨hv.1, hua.trans hv.1, hv.2⟩
  rw [he, setLIntegral_indicator measurableSet_Ioi, hs,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hk := h.weighted_outgoing_transport_kernel_le hu hu0 hua ha0 le_rfl hδ hsmall
  refine (mul_le_mul le_rfl hk zero_le zero_le).trans_eq ?_
  rw [← ENNReal.ofReal_mul (sq_nonneg A)]
  have hp : (u, a) ∈ pastTriangle ui := ⟨hu, hu0, hua.le, ha0⟩
  have hr := (h.r_pos hp hua).ne'
  have hn := (h.nu_neg hp).ne
  congr 1
  dsimp only [A, weightedIncomingAmplitude, SSFields.incomingFlux]
  field_simp

omit h in
/-- The transported kernel vanishes on a cone starting beyond its label.
Paper `e1a0fd5`, `lem:weighted-radial-estimates`, line 1189. -/
theorem weighted_transport_kernel_cone_zero {u a : ℝ} (hau : a ≤ u) :
    (∫⁻ v in Ioc u 0, ENNReal.ofReal
      ((-S.nu u v) * S.lam u v * |weightedTransportKernel S a (u, v)| ^ 2)) = 0 := by
  simp [weightedTransportKernel, not_lt.mpr hau]

/-- W3: the uniform two-dimensional L² kernel bound, from G6.
Paper `e1a0fd5`, `lem:weighted-radial-estimates`, lines 1198–1201. -/
theorem weighted_transport_kernel_energy_le {u₀ U a δ : ℝ}
    (hi : ui ≤ u₀) (hU : U < 0) (ha : a ∈ Ioc u₀ 0) (hδ : δ < 3)
    (hsmall : ∀ p ∈ pastTriangle ui, u₀ ≤ p.1 → S.mu p.1 p.2 / (1 - S.mu p.1 p.2) ≤ δ) :
    (∫⁻ p in weightedTruncatedDomain u₀ U, ENNReal.ofReal
      ((-S.nu p.1 p.2) * S.lam p.1 p.2 * |weightedTransportKernel S a p| ^ 2)) ≤
      ENNReal.ofReal ((Bstar ui S + Real.log (1 / initialGap ui S)) / (3 - δ)) := by
  let K := ENNReal.ofReal (1 / (3 - δ))
  have hcone (u : ℝ) (hu : u ∈ Icc u₀ U) :
      (∫⁻ v in Ioc u 0, ENNReal.ofReal
        ((-S.nu u v) * S.lam u v * |weightedTransportKernel S a (u, v)| ^ 2)) ≤
      K * (Iio a).indicator (fun u => ENNReal.ofReal (S.incomingFlux u a)) u := by
    by_cases hua : u < a
    · rw [indicator_of_mem (show u ∈ Iio a from hua)]
      have hp : (u, a) ∈ pastTriangle ui :=
        ⟨hi.trans hu.1, hu.2.trans_lt hU, hua.le, ha.2⟩
      have hf := h.weighted_transport_kernel_cone_le (hi.trans hu.1) (hu.2.trans_lt hU)
        hua ha.2 hδ (fun v hv => hsmall (u, v)
          ⟨hi.trans hu.1, hu.2.trans_lt hU, (hua.trans_le hv.1).le, hv.2⟩ hu.1)
      refine hf.trans_eq ?_
      dsimp only [K]
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / (3 - δ))]
      congr 1
      ring
    · rw [weighted_transport_kernel_cone_zero (S := S) (le_of_not_gt hua),
        indicator_of_notMem (show u ∉ Iio a from hua),
        mul_zero]
  calc
    _ ≤ ∫⁻ u in Icc u₀ U, ∫⁻ v in Ioc u 0, ENNReal.ofReal
        ((-S.nu u v) * S.lam u v * |weightedTransportKernel S a (u, v)| ^ 2) :=
      weighted_triangle_lintegral_le u₀ U _
    _ ≤ K * ∫⁻ u in Icc u₀ U, (Iio a).indicator
        (fun u => ENNReal.ofReal (S.incomingFlux u a)) u := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact setLIntegral_mono' measurableSet_Icc hcone
    _ ≤ K * ∫⁻ u in Ioc ui a, ENNReal.ofReal (S.incomingFlux u a) := by
      rw [setLIntegral_indicator measurableSet_Iio]
      have hs : Iio a ∩ Icc u₀ U ⊆ Icc ui a :=
        fun u hu => ⟨hi.trans hu.2.1, hu.1.le⟩
      rw [restrict_Ioc_eq_restrict_Icc]
      exact mul_le_mul le_rfl (lintegral_mono_set hs) zero_le zero_le
    _ = K * ∫⁻ u in Ioo ui a, ENNReal.ofReal (S.incomingFlux u a) := by
      rw [restrict_Ioo_eq_restrict_Ioc]
    _ ≤ K * ENNReal.ofReal (Bstar ui S + Real.log (1 / initialGap ui S)) :=
      mul_le_mul le_rfl (h.incoming_flux_le ⟨hi.trans_lt ha.1, ha.2⟩) zero_le zero_le
    _ = _ := by
      dsimp only [K]
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / (3 - δ))]
      congr 1
      ring

end StandingFull

end AcExtensionPrinciple

end
