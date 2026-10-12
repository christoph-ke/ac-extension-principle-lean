module

public import AcExtensionPrinciple.Weighted.CauchySchwarz
public import AcExtensionPrinciple.Weighted.Prop35Selection

/-!
# From finite weighted remainder energy to logarithmic integrability

Helpers, paper `e1a0fd5`, `prop:small-outgoing-bv-cones`,
`equations.tex` lines 1346–1356. All integrals retain their finiteness
conditions; the cone integral is never replaced by a default-valued integral.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- The normalized cone L¹ square is bounded by its weighted energy, with
infinite cone energy permitted. Paper `e1a0fd5`, lines 1346–1350.
Only the cone L¹ integral must be finite. -/
theorem cone_l1_sq_div_le_lintegral_energy {ω j : ℝ → ℝ} {u c : ℝ}
    (hu : u < 0) (hc : 0 < c) (hω : Measurable ω) (hj : Measurable j)
    (hlower : ∀ v ∈ Ioc u 0, c ≤ ω v)
    (hJ : IntegrableOn j (Ioc u 0)) :
    ENNReal.ofReal ((∫ v in u..0, |j v|) ^ 2 / (-u)) ≤
      ENNReal.ofReal c⁻¹ * ∫⁻ v in Ioc u 0, ENNReal.ofReal (ω v * |j v| ^ 2) := by
  have hcs := weighted_lintegral_cone_length_bound hu hc hω hj hlower
  have hnonneg : 0 ≤ ∫ v in Ioc u 0, |j v| :=
    integral_nonneg (fun _ => abs_nonneg _)
  have hnorm : IntegrableOn (fun v => |j v|) (Ioc u 0) := by
    simpa only [IntegrableOn, Real.norm_eq_abs] using hJ.norm
  rw [← ofReal_integral_eq_lintegral_ofReal hnorm
      (ae_of_all _ (fun _ => abs_nonneg _)), ← ENNReal.ofReal_pow hnonneg] at hcs
  rw [intervalIntegral.integral_of_le hu.le, ENNReal.ofReal_div_of_pos (neg_pos.mpr hu)]
  apply (ENNReal.div_le_iff (ENNReal.ofReal_ne_zero_iff.mpr (neg_pos.mpr hu))
    ENNReal.ofReal_ne_top).mpr
  refine hcs.trans_eq ?_
  rw [mul_right_comm (ENNReal.ofReal c⁻¹),
    ← ENNReal.ofReal_mul (inv_nonneg.mpr hc.le)]
  congr 2
  ring

/-- The same cone estimate for an integrable representative, without a
global measurability premise. Paper `e1a0fd5`, lines 1346–1350.
Changing an incoming transport representative on a null set preserves
both the real L¹ integral and the lower energy integral. -/
theorem cone_l1_sq_div_le_lintegral_energy_of_integrable
    {ω j : ℝ → ℝ} {u c : ℝ}
    (hu : u < 0) (hc : 0 < c) (hω : Measurable ω)
    (hlower : ∀ v ∈ Ioc u 0, c ≤ ω v)
    (hJ : IntegrableOn j (Ioc u 0)) :
    ENNReal.ofReal ((∫ v in u..0, |j v|) ^ 2 / (-u)) ≤
      ENNReal.ofReal c⁻¹ * ∫⁻ v in Ioc u 0, ENNReal.ofReal (ω v * |j v| ^ 2) := by
  let j' := hJ.aestronglyMeasurable.mk j
  have hm : StronglyMeasurable j' := hJ.aestronglyMeasurable.stronglyMeasurable_mk
  have he : j =ᵐ[volume.restrict (Ioc u 0)] j' := hJ.aestronglyMeasurable.ae_eq_mk
  have hi : IntegrableOn j' (Ioc u 0) := hJ.congr he
  have hbound := cone_l1_sq_div_le_lintegral_energy hu hc hω hm.measurable hlower hi
  have hL : (∫ v in u..0, |j v|) = ∫ v in u..0, |j' v| := by
    rw [intervalIntegral.integral_of_le hu.le, intervalIntegral.integral_of_le hu.le]
    exact integral_congr_ae (he.fun_comp abs)
  have hE : (∫⁻ v in Ioc u 0, ENNReal.ofReal (ω v * |j v| ^ 2)) =
      ∫⁻ v in Ioc u 0, ENNReal.ofReal (ω v * |j' v| ^ 2) := by
    apply lintegral_congr_ae
    filter_upwards [he] with v hv
    rw [hv]
  rw [hL, hE]
  exact hbound

/-- Weighted energy yields exactly the logarithmic remainder integrability
used in the paper's selection argument. Paper `e1a0fd5`,
`eq:logarithmic-remainder-integrability`, lines 1346–1354. -/
theorem logarithmic_cone_l1_lintegral_lt_top {u₀ c : ℝ}
    {ω J : ℝ × ℝ → ℝ} (hc : 0 < c) (hω : Measurable ω) (hJ : Measurable J)
    (hlower : ∀ u ∈ Ioo u₀ 0, ∀ v ∈ Ioc u 0, c ≤ ω (u, v))
    (hcone : ∀ u ∈ Ioo u₀ 0, IntegrableOn (fun v => J (u, v)) (Ioc u 0))
    (henergy : (∫⁻ u in Ioo u₀ 0, ∫⁻ v in Ioc u 0,
      ENNReal.ofReal (ω (u, v) * |J (u, v)| ^ 2)) < ⊤) :
    (∫⁻ u in Ioo u₀ 0,
      ENNReal.ofReal ((∫ v in u..0, |J (u, v)|) ^ 2 / (-u))) < ⊤ := by
  calc
    _ ≤ ∫⁻ u in Ioo u₀ 0, ENNReal.ofReal c⁻¹ *
        ∫⁻ v in Ioc u 0, ENNReal.ofReal (ω (u, v) * |J (u, v)| ^ 2) := by
      apply setLIntegral_mono' measurableSet_Ioo
      intro u hu
      exact cone_l1_sq_div_le_lintegral_energy hu.2 hc
        (hω.comp (measurable_const.prodMk measurable_id))
        (hJ.comp (measurable_const.prodMk measurable_id))
        (hlower u hu) (hcone u hu)
    _ = ENNReal.ofReal c⁻¹ * ∫⁻ u in Ioo u₀ 0, ∫⁻ v in Ioc u 0,
        ENNReal.ofReal (ω (u, v) * |J (u, v)| ^ 2) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top henergy

/-- The energy-to-sequence part of Proposition 3.5, with precisely the
variation bound and initial tail left as analytic inputs. Paper `e1a0fd5`,
`eq:outgoing-variation-remainder`, `eq:logarithmic-remainder-integrability`,
lines 1340–1356. The result has the closed-cone variation conclusion of
`SmallOutgoingConesStatement`. -/
theorem small_outgoing_cones_of_weighted_energy
    {ui u₀ c C : ℝ} {S : SSFields} {ω J : ℝ × ℝ → ℝ} {A : ℝ → ℝ}
    (hi : ui ≤ u₀) (hu₀ : u₀ < 0) (hc : 0 < c)
    (hω : Measurable ω) (hJ : Measurable J)
    (hlower : ∀ u ∈ Ioo u₀ 0, ∀ v ∈ Ioc u 0, c ≤ ω (u, v))
    (hcone : ∀ u ∈ Ioo u₀ 0, IntegrableOn (fun v => J (u, v)) (Ioc u 0))
    (henergy : (∫⁻ u in Ioo u₀ 0, ∫⁻ v in Ioc u 0,
      ENNReal.ofReal (ω (u, v) * |J (u, v)| ^ 2)) < ⊤)
    (hA : Tendsto A (𝓝[Ioo u₀ 0] 0) (𝓝 0))
    (hvariation : ∀ u ∈ Ioo u₀ 0, S.outgoingVariation u ≤ ENNReal.ofReal
      (C * (A u + ∫ v in u..0, |J (u, v)|))) :
    ∃ u : ℕ → ℝ, (∀ n, u n ∈ Ioo ui 0) ∧ Tendsto u atTop (𝓝 0) ∧
      Tendsto (fun n => eVariationOn
        (fun v => S.dvpsi (u n) v / S.lam (u n) v) (Icc (u n) 0)) atTop (𝓝 0) :=
  small_outgoing_cones_of_logarithmic_remainder hi hu₀ hA
    (logarithmic_cone_l1_lintegral_lt_top hc hω hJ hlower hcone henergy) hvariation

end AcExtensionPrinciple

end
