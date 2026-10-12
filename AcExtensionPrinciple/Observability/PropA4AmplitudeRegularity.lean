module

public import AcExtensionPrinciple.Observability.PropA4Axis
public import AcExtensionPrinciple.Renormalized.ClassACComposition

/-!
# Absolute continuity and oscillation of the scalar amplitude

Paper `e1a0fd5`, `eq:observability-amplitude-variation`, lines 1700–1707,
and its use in the remainder estimate at lines 1770–1779. The oscillation
bound is derived directly from the boundary energy and the axis Lipschitz
bound, without requiring a scalar chain rule at every axis label.
-/

public section

namespace AcExtensionPrinciple
namespace PropA4

open Set Filter MeasureTheory

/-- Rewrite the amplitude using one fixed-base boundary primitive.
Paper `e1a0fd5`, `eq:observability-amplitude`, lines 1700–1703. -/
theorem amplitude_eq_fixed_primitive {b T K s : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hs : s ∈ Icc (K * b) T) :
    amplitude h s = chartPsi S s s - (∫ z in 0..s, S.dvpsi z z) +
      ∫ z in 0..h.g s, S.dvpsi z z := by
  have hKb : 0 ≤ K * b := mul_nonneg (by linarith [h.K_ge_one]) h.b_pos.le
  have hsI : s ∈ Icc 0 T := ⟨hKb.trans hs.1, hs.2⟩
  have hg0 := axis_label_nonneg h hsI hs.1
  have hgs := (h.axis_before_boundary s hsI).le
  have hsub₁ : uIcc 0 (h.g s) ⊆ uIcc 0 T := by
    rw [uIcc_of_le hg0, uIcc_of_le h.T_nonneg]
    exact Icc_subset_Icc le_rfl (hgs.trans hs.2)
  have hsub₂ : uIcc (h.g s) s ⊆ uIcc 0 T := by
    rw [uIcc_of_le hgs, uIcc_of_le h.T_nonneg]
    exact Icc_subset_Icc hg0 hs.2
  have he := intervalIntegral.integral_add_adjacent_intervals
    (h.boundary_dvpsi_integrable.mono_set hsub₁)
    (h.boundary_dvpsi_integrable.mono_set hsub₂)
  unfold amplitude
  linarith

/-- The late scalar amplitude is absolutely continuous, as a sum of
the boundary trace and two boundary primitives. Paper `e1a0fd5`,
`eq:observability-amplitude-variation`, lines 1700–1707. -/
theorem amplitude_ac {b T K : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hT : K * b ≤ T) :
    AbsolutelyContinuousOnInterval (amplitude h) (K * b) T := by
  have hKb : 0 ≤ K * b := mul_nonneg (by linarith [h.K_ge_one]) h.b_pos.le
  have hsub : uIcc (K * b) T ⊆ uIcc 0 T := by
    rw [uIcc_of_le hT, uIcc_of_le h.T_nonneg]
    exact Icc_subset_Icc hKb le_rfl
  let Q := fun s => ∫ z in 0..s, S.dvpsi z z
  have hQ : AbsolutelyContinuousOnInterval Q 0 T :=
    h.boundary_dvpsi_integrable.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hg : MonotoneOn h.g (uIcc (K * b) T) := by
    simpa only [uIcc_of_le hT] using
      h.monotone_g.mono (Icc_subset_Icc hKb le_rfl)
  have hL : LipschitzOnWith ⟨K, by linarith [h.K_ge_one]⟩ h.g (uIcc (K * b) T) := by
    simpa only [uIcc_of_le hT] using axis_lipschitz h hT
  have hmaps : MapsTo h.g (uIcc (K * b) T) (uIcc 0 T) := by
    intro s hs
    rw [uIcc_of_le hT] at hs
    rw [uIcc_of_le h.T_nonneg]
    exact ⟨axis_label_nonneg h ⟨hKb.trans hs.1, hs.2⟩ hs.1,
      (h.axis_before_boundary s ⟨hKb.trans hs.1, hs.2⟩).le.trans hs.2⟩
  have hcomp := ac_comp_monotone_lipschitz hQ hg hL hmaps
  apply ((h.boundary_traces_ac.1.mono hsub).sub (hQ.mono hsub)).add hcomp |>.congr
  intro s hs
  rw [uIcc_of_le hT] at hs
  exact (amplitude_eq_fixed_primitive h hs).symm

/-- The exact amplitude increment contains two ordinary boundary
increments and the primitive between the two axis labels.
Paper `e1a0fd5`, lines 1704–1707 and 1770–1779. -/
theorem amplitude_increment {b T K x y : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hx : x ∈ Icc (K * b) T)
    (hy : y ∈ Icc (K * b) T) (hxy : x ≤ y) :
    amplitude h y - amplitude h x =
      (∫ z in x..y, deriv (fun s => chartPsi S s s) z) -
      (∫ z in x..y, S.dvpsi z z) + ∫ z in h.g x..h.g y, S.dvpsi z z := by
  have hKb : 0 ≤ K * b := mul_nonneg (by linarith [h.K_ge_one]) h.b_pos.le
  have hxI : x ∈ Icc 0 T := ⟨hKb.trans hx.1, hx.2⟩
  have hyI : y ∈ Icc 0 T := ⟨hKb.trans hy.1, hy.2⟩
  have hgxy := h.monotone_g hxI hyI hxy
  have hgx : h.g x ∈ Icc 0 T := ⟨axis_label_nonneg h hxI hx.1,
    (h.axis_before_boundary x hxI).le.trans hx.2⟩
  have hgy : h.g y ∈ Icc 0 T := ⟨axis_label_nonneg h hyI hy.1,
    (h.axis_before_boundary y hyI).le.trans hy.2⟩
  have hsub {l r : ℝ} (hl : l ∈ Icc 0 T) (hr : r ∈ Icc 0 T) :
      uIcc l r ⊆ uIcc 0 T := by
    rw [uIcc_of_le h.T_nonneg]
    exact uIcc_subset_Icc hl hr
  have hd := (h.boundary_traces_ac.1.mono (hsub hxI hyI)).integral_deriv_eq_sub
  have he := intervalIntegral.integral_add_adjacent_intervals
    (h.boundary_dvpsi_integrable.mono_set (hsub ⟨le_rfl, h.T_nonneg⟩ hxI))
    (h.boundary_dvpsi_integrable.mono_set (hsub hxI hyI))
  have heg := intervalIntegral.integral_add_adjacent_intervals
    (h.boundary_dvpsi_integrable.mono_set (hsub ⟨le_rfl, h.T_nonneg⟩ hgx))
    (h.boundary_dvpsi_integrable.mono_set (hsub hgx hgy))
  rw [amplitude_eq_fixed_primitive h hx, amplitude_eq_fixed_primitive h hy]
  linarith

/-- The precise square-root oscillation bound used in the remainder
estimate follows from the energy and the axis label bound. Paper
`e1a0fd5`, lines 1704–1707 and 1770–1779. -/
theorem amplitude_oscillation_sq {b T K x y : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hx : x ∈ Icc (K * b) T)
    (hy : y ∈ Icc (K * b) T) (hxy : x ≤ y) :
    (amplitude h y - amplitude h x) ^ 2 ≤
      3 * (1 + K) * (y - x) * chartScalarEnergy S T := by
  have hKb : 0 ≤ K * b := mul_nonneg (by linarith [h.K_ge_one]) h.b_pos.le
  have hxI : x ∈ Icc 0 T := ⟨hKb.trans hx.1, hx.2⟩
  have hyI : y ∈ Icc 0 T := ⟨hKb.trans hy.1, hy.2⟩
  have hgxy := h.monotone_g hxI hyI hxy
  have hgx := axis_label_nonneg h hxI hx.1
  have hgyT := (h.axis_before_boundary y hyI).le.trans hy.2
  have hsub : uIcc x y ⊆ uIcc 0 T := by
    rw [uIcc_of_le hxy, uIcc_of_le h.T_nonneg]
    exact Icc_subset_Icc hxI.1 hy.2
  have hsubg : uIcc (h.g x) (h.g y) ⊆ uIcc 0 T := by
    rw [uIcc_of_le hgxy, uIcc_of_le h.T_nonneg]
    exact Icc_subset_Icc hgx hgyT
  have hD := primitive_sq_le hxy
    (h.boundary_traces_ac.1.intervalIntegrable_deriv.mono_set hsub)
    (h.boundary_psi_deriv_square_integrable.mono_set hsub)
  have hB := primitive_sq_le hxy (h.boundary_dvpsi_integrable.mono_set hsub)
    (h.boundary_scalar_square_integrable.2.mono_set hsub)
  have hG := primitive_sq_le hgxy (h.boundary_dvpsi_integrable.mono_set hsubg)
    (h.boundary_scalar_square_integrable.2.mono_set hsubg)
  have hlocal : (∫ z in x..y, deriv (fun s => chartPsi S s s) z ^ 2) +
      (∫ z in x..y, S.dvpsi z z ^ 2) ≤ chartScalarEnergy S T := by
    rw [← intervalIntegral.integral_add
      (h.boundary_psi_deriv_square_integrable.mono_set hsub)
      (h.boundary_scalar_square_integrable.2.mono_set hsub)]
    unfold chartScalarEnergy
    simpa only [add_comm] using intervalIntegral.integral_mono_interval hxI.1 hxy hy.2
      (Eventually.of_forall (fun z => by positivity))
      (h.boundary_psi_deriv_square_integrable.add h.boundary_scalar_square_integrable.2)
  have hglobal : (∫ z in h.g x..h.g y, S.dvpsi z z ^ 2) ≤ chartScalarEnergy S T := by
    have hm := intervalIntegral.integral_mono_interval hgx hgxy hgyT
      (Eventually.of_forall (fun z => sq_nonneg (S.dvpsi z z)))
      h.boundary_scalar_square_integrable.2
    have hn := intervalIntegral.integral_nonneg (μ := volume) h.T_nonneg
      (fun z _ => sq_nonneg (deriv (fun s => chartPsi S s s) z))
    unfold chartScalarEnergy
    rw [intervalIntegral.integral_add h.boundary_scalar_square_integrable.2
      h.boundary_psi_deriv_square_integrable]
    linarith
  have hlen : h.g y - h.g x ≤ K * (y - x) := by
    have hh := (axis_lipschitz h (hx.1.trans hx.2)).dist_le_mul x hx y hy
    change dist (h.g x) (h.g y) ≤ K * dist x y at hh
    simpa only [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hgxy),
      abs_of_nonpos (sub_nonpos.mpr hxy), neg_sub] using hh
  have hDB := (add_le_add hD hB).trans
    (by simpa only [mul_add] using
      mul_le_mul_of_nonneg_left hlocal (sub_nonneg.mpr hxy))
  have hG' := hG.trans ((mul_le_mul_of_nonneg_left hglobal (sub_nonneg.mpr hgxy)).trans
    (mul_le_mul_of_nonneg_right hlen h.scalar_energy_nonneg))
  rw [amplitude_increment h hx hy hxy]
  have hthree (a b c : ℝ) : (a - b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
    nlinarith [sq_nonneg (a + b), sq_nonneg (a - c), sq_nonneg (b + c)]
  exact (hthree _ _ _).trans (by nlinarith [hDB, hG'])

/-- Absolute-value version of the amplitude oscillation bound.
Paper `e1a0fd5`, lines 1770–1779. -/
theorem amplitude_oscillation {b T K x y : ℝ} {S : SSFields}
    (h : NormalizedChartData b T K S) (hx : x ∈ Icc (K * b) T)
    (hy : y ∈ Icc (K * b) T) (hxy : x ≤ y) :
    |amplitude h y - amplitude h x| ≤
      Real.sqrt (3 * (1 + K) * (y - x) * chartScalarEnergy S T) := by
  have hh := amplitude_oscillation_sq h hx hy hxy
  exact (Real.le_sqrt (abs_nonneg _) (le_trans (sq_nonneg _) hh)).mpr (by
    simpa only [sq_abs] using hh)

end PropA4
end AcExtensionPrinciple

end
