module

public import AcExtensionPrinciple.Observability.PropA4InnerInterface
public import AcExtensionPrinciple.Observability.PropA4AmplitudeMass
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Outer boundary data transported to the inner cylinder

Paper `e1a0fd5`, `eq:observability-inner-boundary-measure`, lines 1887–1892.
The inner trace Jacobian is `(-ν)/λ`. Monotone change of variables applies
to the squared BV boundary data, without a continuity assumption on them.
-/

public section

namespace AcExtensionPrinciple
namespace PropA4

open Set MeasureTheory

/-- The incoming boundary derivative contributes at most `2E` on any
subinterval, by the actual boundary chain rule. Paper `e1a0fd5`, lines 1890–1892. -/
theorem boundary_incoming_energy_le {b T K u v : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ T) :
    (∫ s in u..v, S.dupsi s s ^ 2) ≤ 2 * chartScalarEnergy S T := by
  have hsub : uIcc u v ⊆ uIcc 0 T := by
    rw [uIcc_of_le huv, uIcc_of_le h.T_nonneg]
    exact Icc_subset_Icc hu hv
  have hUi := h.boundary_scalar_square_integrable.1.mono_set hsub
  have hVi := h.boundary_scalar_square_integrable.2.mono_set hsub
  have hDi := h.boundary_psi_deriv_square_integrable.mono_set hsub
  have hb := intervalIntegral.integral_mono_ae_restrict huv hUi ((hVi.add hDi).const_mul 2) (by
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
    filter_upwards [h.boundary_psi_ae_hasDerivAt] with s hs
    intro hsI
    have hsT : s ∈ Icc 0 T := ⟨hu.trans hsI.1, hsI.2.trans hv⟩
    rw [(hs hsT).deriv]
    nlinarith [sq_nonneg (S.dupsi s s + 2 * S.dvpsi s s)])
  have hEi := h.boundary_scalar_square_integrable.2.add h.boundary_psi_deriv_square_integrable
  have hmono := intervalIntegral.integral_mono_interval hu huv hv
    (Filter.Eventually.of_forall (fun s => add_nonneg (sq_nonneg _) (sq_nonneg _))) hEi
  rw [intervalIntegral.integral_const_mul] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left hmono (by norm_num))

/-- The outer radial data transported along a differentiable increasing
inner-radius curve has energy at most `2E`. Its integrability follows from
monotone substitution and continuous geometry. The curve premises are
supplied by `InnerChartStatement`. Paper `e1a0fd5`, lines 1887–1890. -/
theorem inner_boundary_data_energy_le {b T K P u v : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hP : 0 < P)
    (hmass : ∀ σ z, (σ, z) ∈ chartCylinder h.g T → S.m σ z ≤ P)
    (tₐ : ℝ → ℝ) (huv : u ≤ v)
    (hcurve : ∀ s ∈ Icc u v, (s, tₐ s) ∈ exteriorDomain h P)
    (hc : ContinuousOn tₐ (Icc u v)) (hmono : MonotoneOn tₐ (Icc u v))
    (hd : ∀ s ∈ Icc u v,
      HasDerivWithinAt tₐ ((-S.nu s (tₐ s)) / S.lam s (tₐ s)) (Icc u v) s) :
    IntervalIntegrable (fun s => (-S.nu s (tₐ s)) *
      (S.dvpsi (tₐ s) (tₐ s) / S.lam s (tₐ s)) ^ 2) volume u v ∧
    (∫ s in u..v, (-S.nu s (tₐ s)) *
      (S.dvpsi (tₐ s) (tₐ s) / S.lam s (tₐ s)) ^ 2) ≤ 2 * chartScalarEnergy S T := by
  let d := fun s => (-S.nu s (tₐ s)) / S.lam s (tₐ s)
  have hmap : ContinuousOn (fun s => (s, tₐ s)) (Icc u v) := continuousOn_id.prodMk hc
  have hLam : ContinuousOn (fun s => S.lam s (tₐ s)) (Icc u v) :=
    h.continuous_lam.comp hmap (fun s hs => (hcurve s hs).1)
  have hN : ContinuousOn (fun s => -S.nu s (tₐ s)) (Icc u v) :=
    (h.continuous_nu.comp hmap (fun s hs => (hcurve s hs).1)).neg
  have hLamPos (s : ℝ) (hs : s ∈ Icc u v) : 0 < S.lam s (tₐ s) :=
    (h.signs s (tₐ s) (hcurve s hs).1).1
  have hdPos (s : ℝ) (hs : s ∈ Icc u v) : 0 ≤ d s :=
    div_nonneg (neg_nonneg.mpr (h.signs s (tₐ s) (hcurve s hs).1).2.1.le) (hLamPos s hs).le
  have hdAt (s : ℝ) (hs : s ∈ Ioo (min u v) (max u v)) : HasDerivAt tₐ (d s) s := by
    rw [min_eq_left huv, max_eq_right huv] at hs
    exact (hd s ⟨hs.1.le, hs.2.le⟩).hasDerivAt (Icc_mem_nhds hs.1 hs.2)
  have hc' : ContinuousOn tₐ (uIcc u v) := by rwa [uIcc_of_le huv]
  have hmonoEnds := hmono ⟨le_rfl, huv⟩ ⟨huv, le_rfl⟩ huv
  have hu0 : 0 ≤ tₐ u :=
    (mul_nonneg (by linarith only [h.K_ge_one]) h.b_pos.le).trans (hcurve u ⟨le_rfl, huv⟩).2.1
  have hvT : tₐ v ≤ T := (hcurve v ⟨huv, le_rfl⟩).1.2.2.2.trans
    (hcurve v ⟨huv, le_rfl⟩).1.2.1
  have hsub : uIcc (tₐ u) (tₐ v) ⊆ uIcc 0 T := by
    rw [uIcc_of_le hmonoEnds, uIcc_of_le h.T_nonneg]
    exact Icc_subset_Icc hu0 hvT
  have hfi := h.boundary_scalar_square_integrable.2.mono_set hsub
  have hGi : IntervalIntegrable
      (fun s => S.dvpsi (tₐ s) (tₐ s) ^ 2 * d s) volume u v :=
    (intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg hc' hdAt
      (fun s hs => hdPos s (by
        rw [min_eq_left huv, max_eq_right huv] at hs
        exact ⟨hs.1.le, hs.2.le⟩))).mpr hfi
  have hEq : (∫ s in u..v, S.dvpsi (tₐ s) (tₐ s) ^ 2 * d s) =
      ∫ t in tₐ u..tₐ v, S.dvpsi t t ^ 2 :=
    intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
      (g := fun t => S.dvpsi t t ^ 2) hc' hdAt
      (fun s hs => hdPos s (by
        rw [min_eq_left huv, max_eq_right huv] at hs
        exact ⟨hs.1.le, hs.2.le⟩))
  have hInv : ContinuousOn (fun s => (S.lam s (tₐ s))⁻¹) (uIcc u v) := by
    rw [uIcc_of_le huv]
    exact hLam.inv₀ (fun s hs => (hLamPos s hs).ne')
  have hi : IntervalIntegrable (fun s => (-S.nu s (tₐ s)) *
      (S.dvpsi (tₐ s) (tₐ s) / S.lam s (tₐ s)) ^ 2) volume u v := by
    apply (hGi.mul_continuousOn hInv).congr
    intro s hs
    dsimp [d]
    ring
  have hb := intervalIntegral.integral_mono_on huv hi (hGi.const_mul 2) (by
    intro s hs
    have hext := hcurve s hs
    have ht0 := (mul_nonneg (by linarith only [h.K_ge_one]) h.b_pos.le).trans hext.2.1
    have hlower := (exterior_geometry_of_mass_bound h hP ht0
      (exteriorDomain_interior h hP hext) hext.2.2 hmass).2.2.1
    have hrec : (S.lam s (tₐ s))⁻¹ ≤ 2 := by
      rw [inv_eq_one_div, div_le_iff₀ (hLamPos s hs)]
      linarith only [hlower]
    have hmult := mul_le_mul_of_nonneg_left hrec
      (mul_nonneg (sq_nonneg (S.dvpsi (tₐ s) (tₐ s))) (hdPos s hs))
    convert hmult using 1 <;> dsimp [d] <;> ring)
  refine ⟨hi, ?_⟩
  rw [intervalIntegral.integral_const_mul, hEq] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left
    (boundary_radial_energy_le h hu0 hmonoEnds hvT) (by norm_num))

end PropA4
end AcExtensionPrinciple

end
