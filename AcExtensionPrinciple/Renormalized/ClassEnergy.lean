module

public import AcExtensionPrinciple.Renormalized.ClassRemainder

/-!
# Finite weighted initial energy from an L¹ remainder

Paper `e1a0fd5`, `equations.tex` lines 1112–1125.
The estimate does not require an L² initial derivative. Its premises are
the previously obtained remainder bound, cone integrability, and the
positive geometric lower bounds.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory

/-- Weighted remainder energy density. Paper `e1a0fd5`,
`eq:renormalized-initial-energy`, lines 1112–1115. -/
@[expose] noncomputable def SSFields.renormalizedRemainderEnergy
    (S : SSFields) (q : ℝ → ℝ → ℝ) (ui u v : ℝ) : ℝ :=
  S.r u v * S.renormalizedRemainder q ui u v ^ 2 / ((1 - S.mu u v) ^ 2 * S.lam u v)

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Uniform initial domination transports an L¹ initial datum to any proper
cone. Paper `e1a0fd5`, `eq:renormalized-initial-domination`, lines 1092–1097.
Measurability comes from the explicit κ-ratio and the initial datum. -/
theorem renormalizedInitial_integrable_of_domination {q : ℝ → ℝ → ℝ} {u ci : ℝ}
    (hu : ui ≤ u) (hu0 : u < 0) (hci : 0 < ci)
    (hκ : ∀ p ∈ pastTriangle ui,
      Real.exp (-Bstar ui S) ≤ S.kappa p.1 p.2 ∧ S.kappa p.1 p.2 ≤ 1 / ci)
    (hJi : IntegrableOn (S.renormalizedDerivative q ui) (Ioc ui 0))
    (hmeas : AEStronglyMeasurable (S.renormalizedInitial q ui u) (volume.restrict (Ioc u 0))) :
    IntegrableOn (S.renormalizedInitial q ui u) (Ioc u 0) := by
  have htail := hJi.mono_set (Ioc_subset_Ioc_left hu)
  apply (htail.norm.const_mul ((1 / ci) / Real.exp (-Bstar ui S))).mono' hmeas
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
  simpa only [Real.norm_eq_abs] using
    h.renormalizedInitial_domination_of_geometric q hci hκ (u, v) ⟨hu, hu0, hv.1.le, hv.2⟩

omit h in
/-- Subtracting two cone L¹ functions gives the remainder's cone L¹ property.
Paper `e1a0fd5`, `eq:renormalized-initial-energy`, lines 1122–1124. -/
theorem renormalizedRemainder_integrable_of_cone_l1 {q : ℝ → ℝ → ℝ} {u : ℝ}
    (hj : IntegrableOn (S.renormalizedDerivative q u) (Ioc u 0))
    (hi : IntegrableOn (S.renormalizedInitial q ui u) (Ioc u 0)) :
    IntegrableOn (S.renormalizedRemainder q ui u) (Ioc u 0) := hj.sub hi

/-- The weighted initial energy is finite and bounded by the cone L¹ norm.
Paper `e1a0fd5`, `eq:renormalized-initial-energy`, lines 1112–1124.
For the paper take `c = cᵢ exp(-B*)`, `d = exp(-B*)`; cone L¹ comes from
local renormalized integrability and initial domination, and `r |J| ≤ M`
from variation of constants. Measurability is inherited from the class
fields, the AC datum derivative, and the explicit κ-ratio splitting. -/
theorem renormalized_initial_energy_of_l1_and_geometric {q : ℝ → ℝ → ℝ} {u c d M : ℝ}
    (hu : ui ≤ u) (hu0 : u < 0) (hc : 0 < c) (hd : 0 < d)
    (hgeometry : ∀ v ∈ Ioc u 0, c ≤ 1 - S.mu u v ∧ d ≤ S.lam u v)
    (hpoint : ∀ v ∈ Ioc u 0, S.r u v * |S.renormalizedRemainder q ui u v| ≤ M)
    (hJ : IntegrableOn (fun v => S.renormalizedRemainder q ui u v) (Ioc u 0))
    (hmeas : AEStronglyMeasurable (S.renormalizedRemainderEnergy q ui u)
      (volume.restrict (Ioc u 0))) :
    IntegrableOn (S.renormalizedRemainderEnergy q ui u) (Ioc u 0) ∧
    (∫ v in Ioc u 0, S.renormalizedRemainderEnergy q ui u v) ≤
      (M / (c ^ 2 * d)) * ∫ v in Ioc u 0, |S.renormalizedRemainder q ui u v| := by
  have hbound (v : ℝ) (hv : v ∈ Ioc u 0) :
      0 ≤ S.renormalizedRemainderEnergy q ui u v ∧
      S.renormalizedRemainderEnergy q ui u v ≤
        (M / (c ^ 2 * d)) * |S.renormalizedRemainder q ui u v| := by
    have hp : (u, v) ∈ pastTriangle ui := ⟨hu, hu0, hv.1.le, hv.2⟩
    have hr := (h.r_pos hp hv.1).le
    refine ⟨div_nonneg (mul_nonneg hr (sq_nonneg _))
      (mul_nonneg (sq_nonneg _) (h.lam_pos hp).le), ?_⟩
    exact renormalized_energy_density_le hr hc hd (hgeometry v hv).1
      (hgeometry v hv).2 (hpoint v hv)
  have hi : IntegrableOn (S.renormalizedRemainderEnergy q ui u) (Ioc u 0) := by
    refine renormalized_energy_integrable_of_l1 (C := M / (c ^ 2 * d)) hmeas hJ ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    rw [abs_of_nonneg (hbound v hv).1]
    exact (hbound v hv).2
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ v in Ioc u 0, (M / (c ^ 2 * d)) * |S.renormalizedRemainder q ui u v| := by
      apply integral_mono_ae hi (hJ.norm.const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
      exact (hbound v hv).2
    _ = _ := integral_const_mul _ _

end StandingFull

end AcExtensionPrinciple

end
