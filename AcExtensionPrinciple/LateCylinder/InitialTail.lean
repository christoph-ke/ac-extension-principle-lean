module

public import AcExtensionPrinciple.LateCylinder.Estimate

/-!
# Tangential identity and the transported initial tail

Paper `e1a0fd5`, `eq:cylinder-datum-derivative` and
`eq:cylinder-initial-tail`, equations.tex lines 819–831.
These helpers also check the literal integral change of variables in the proof.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory

/-- Dividing the incoming and outgoing tangential derivatives by -ν gives
the exact boundary-time identity. Paper `e1a0fd5`,
`eq:cylinder-datum-derivative`, lines 819–822. -/
theorem cylinder_datum_tangential_identity {lam nu mu vk A q : ℝ}
    (hl : lam ≠ 0) (hn : nu ≠ 0) (hg : 1 - mu ≠ 0) :
    (-(gammaOf nu mu * vk) * A + (-nu / lam) * (lam * q)) / (-nu) =
      q + vk / (1 - mu) * A := by
  dsimp [gammaOf]
  field_simp
  ring

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The transported rough initial term has a uniform cylinder integral
bound, using monotone substitution dτ = λ dv. Graph premises are supplied
by the canonical cylinder calculus. Paper `e1a0fd5`,
`eq:cylinder-initial-tail`, lines 825–831. -/
theorem cylinder_initial_tail_integral {v : ℝ → ℝ} {K a0 a1 u0 : ℝ}
    (hK : LateCylinderGeometry ui S K) (ha : a0 ≤ a1) (hu0 : ui ≤ u0) (hu1 : u0 ≤ 0)
    (hv : ContinuousOn v (Icc a0 a1)) (hmono : MonotoneOn v (Icc a0 a1))
    (hp : ∀ u ∈ Icc a0 a1, (u, v u) ∈ pastTriangle ui)
    (hlabels : MapsTo v (Icc a0 a1) (Icc u0 0))
    (ht : ∀ u ∈ Ioo a0 a1, HasDerivAt v (-S.nu u (v u) / S.lam u (v u)) u) :
    (∫ u in a0..a1, |deriv (S.dvpsi ui) (v u)| / S.lam u (v u) ^ 2 * (-S.nu u (v u))) ≤
      K * initialACTail ui S u0 := by
  let G := fun w => |deriv (S.dvpsi ui) w|
  let V := fun u => -S.nu u (v u) / S.lam u (v u)
  let J := fun u => G (v u) * V u
  have hK0 : 0 < K := zero_lt_one.trans_le hK.1
  have hVa : v a0 ∈ Icc u0 0 := hlabels (left_mem_Icc.mpr ha)
  have hVb : v a1 ∈ Icc u0 0 := hlabels (right_mem_Icc.mpr ha)
  have hVab : v a0 ≤ v a1 := hmono (left_mem_Icc.mpr ha) (right_mem_Icc.mpr ha) ha
  have hGi : IntervalIntegrable G volume (v a0) (v a1) :=
    h.initial_second_derivative_integrable.abs.mono_set (by
      rw [uIcc_of_le hVab, uIcc_of_le h.initial_negative.le]
      exact Icc_subset_Icc (hu0.trans hVa.1) hVb.2)
  have hd : ∀ u ∈ Ioo (min a0 a1) (max a0 a1), HasDerivAt v (V u) u := by
    simpa only [min_eq_left ha, max_eq_right ha] using ht
  have hV0 : ∀ u ∈ Ioo (min a0 a1) (max a0 a1), 0 ≤ V u := by
    intro u hu
    rw [min_eq_left ha, max_eq_right ha] at hu
    exact div_nonneg (neg_nonneg.mpr (h.nu_neg (hp u (Ioo_subset_Icc_self hu))).le)
      (h.lam_pos (hp u (Ioo_subset_Icc_self hu))).le
  have hvU : ContinuousOn v (uIcc a0 a1) := by simpa only [uIcc_of_le ha] using hv
  have hJi : IntervalIntegrable J volume a0 a1 :=
    (intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg hvU hd hV0).mpr hGi
  have hlc := h.regularCenter.continuous_lam.comp (continuousOn_id.prodMk hv) hp
  have hinv : ContinuousOn (fun u => (S.lam u (v u))⁻¹) (uIcc a0 a1) := by
    rw [uIcc_of_le ha]
    exact hlc.inv₀ (fun u hu => (h.lam_pos (hp u hu)).ne')
  have hweighted := hJi.mul_continuousOn hinv
  have hJ : (∫ u in a0..a1, J u) ≤ initialACTail ui S u0 := by
    have he : (∫ u in a0..a1, J u) = ∫ w in v a0..v a1, G w := by
      simpa only [J, Function.comp_apply] using
        intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg (g := G) hvU hd hV0
    rw [he]
    apply intervalIntegral.integral_mono_interval hVa.1 hVab hVb.2
      (Eventually.of_forall (fun _w => abs_nonneg _))
    exact h.initial_second_derivative_integrable.abs.mono_set (by
      rw [uIcc_of_le hu1, uIcc_of_le h.initial_negative.le]
      exact Icc_subset_Icc hu0 le_rfl)
  have hmajor : (∫ u in a0..a1, J u * (S.lam u (v u))⁻¹) ≤ K * ∫ u in a0..a1, J u := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on ha hweighted (hJi.const_mul K)
    intro u hu
    have hinvK : (S.lam u (v u))⁻¹ ≤ K := by
      simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr hK0) (hK.2 _ (hp u hu)).1
    have hJ0 : 0 ≤ J u := mul_nonneg (abs_nonneg _)
      (div_nonneg (neg_nonneg.mpr (h.nu_neg (hp u hu)).le) (h.lam_pos (hp u hu)).le)
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hinvK hJ0
  have heq : (∫ u in a0..a1,
      |deriv (S.dvpsi ui) (v u)| / S.lam u (v u) ^ 2 * (-S.nu u (v u))) =
        ∫ u in a0..a1, J u * (S.lam u (v u))⁻¹ := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ha] at hu
    dsimp [J, G, V]
    field_simp [(h.lam_pos (hp u hu)).ne']
  rw [heq]
  exact hmajor.trans (mul_le_mul_of_nonneg_left hJ hK0.le)

end StandingFull

end AcExtensionPrinciple

end
