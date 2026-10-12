module

public import AcExtensionPrinciple.ACDatum.WeightedTransport

/-!
# Radial datum transport and remainder identification

Paper `e1a0fd5`, `lem:ac-datum-propagation`, lines 564–574 and 594–603.
The incoming identities hold on every proper segment for almost every
incoming label, the labels where the initial AC datum is differentiable.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- q is AC in the incoming direction at each differentiable initial label.
Paper `e1a0fd5`, `eq:radial-datum-transport`, lines 564–570. -/
theorem radialDatumDerivative_ac_in_of_initial_deriv {u v : ℝ}
    (hu : ui ≤ u) (hu0 : u < 0) (huv : u < v) (hv : v < 0)
    (hinit : HasDerivAt (S.dvpsi ui) (deriv (S.dvpsi ui) v) v) :
    AbsolutelyContinuousOnInterval (fun s => radialDatumDerivative S s v) ui u := by
  have hl := h.lam_ac_in hu le_rfl hu0 huv hv.le
  have hi := positive_ac_inv hl (fun s hs => by
    rw [uIcc_of_le hu] at hs
    exact h.lam_pos (p := (s, v)) ⟨hs.1, hs.2.trans_lt hu0,
      (hs.2.trans_lt huv).le, hv.le⟩)
  apply ((h.weightedRadialDatum_ac_in hu hu0 huv hv).fun_mul (hi.fun_mul hi)).congr
  intro s hs
  rw [uIcc_of_le hu] at hs
  change weightedRadialDatum ui S s v * ((S.lam s v)⁻¹ * (S.lam s v)⁻¹) =
    radialDatumDerivative S s v
  rw [h.radialDatumDerivative_eq_weighted hs.1 (hs.2.trans_lt hu0)
    (hs.2.trans_lt huv) hv hinit]
  simp only [div_eq_mul_inv, pow_two, mul_inv_rev]

/-- Incoming q transport is derived by dividing the weighted transport by λ².
Paper `e1a0fd5`, `eq:radial-datum-transport`, lines 564–570. -/
theorem radialDatumDerivative_ae_transport_of_initial_deriv {u v : ℝ}
    (hu : ui ≤ u) (hu0 : u < 0) (huv : u < v) (hv : v < 0)
    (hinit : HasDerivAt (S.dvpsi ui) (deriv (S.dvpsi ui) v) v) :
    ∀ᵐ s, s ∈ Ioo ui u → HasDerivAt (fun t => radialDatumDerivative S t v)
      (-2 * (S.gamma s v * S.varkappa s v) * radialDatumDerivative S s v +
        radialDatumSource S s v) s := by
  have hl := intervalPrimitive_ae_hasDerivAt hu
    (fun x hx => h.regularCenter.localBV.lam_in v ui x hx.1
      (inSeg_subset_offAxis le_rfl (hx.2.trans_lt hu0) (hx.2.trans_lt huv) hv.le))
  filter_upwards [hl, h.weightedRadialDatum_ae_transport hu hu0 huv hv] with s hls hws
  intro hs
  have hp : (s, v) ∈ pastTriangle ui :=
    ⟨hs.1.le, hs.2.trans hu0, (hs.2.trans huv).le, hv.le⟩
  have hl0 := h.lam_pos hp
  have he : (fun t => radialDatumDerivative S t v) =ᶠ[𝓝 s]
      (fun t => weightedRadialDatum ui S t v / S.lam t v ^ 2) := by
    filter_upwards [Icc_mem_nhds hs.1 hs.2] with t ht
    exact h.radialDatumDerivative_eq_weighted ht.1 (ht.2.trans_lt hu0)
      (ht.2.trans_lt huv) hv hinit
  convert ((hws hs).div ((hls hs).pow 2) (pow_ne_zero 2 hl0.ne')).congr_of_eventuallyEq he using 1
  rw [h.radialDatumDerivative_eq_weighted hs.1.le (hs.2.trans hu0)
    (hs.2.trans huv) hv hinit, S.radiusCoeff_eq_lam_gamma]
  simp only [Pi.pow_apply]
  field_simp [hl0.ne']
  ring

/-- Integral q transport at each differentiable initial label.
Paper `e1a0fd5`, `eq:radial-datum-transport`, line 570. -/
theorem radialDatumDerivative_transport_primitive_of_initial_deriv {u v : ℝ}
    (hu : ui ≤ u) (hu0 : u < 0) (huv : u < v) (hv : v < 0)
    (hinit : HasDerivAt (S.dvpsi ui) (deriv (S.dvpsi ui) v) v) :
    IntervalPrimitive (fun s => radialDatumDerivative S s v)
      (fun s => -2 * (S.gamma s v * S.varkappa s v) * radialDatumDerivative S s v +
        radialDatumSource S s v) ui u :=
  ac_integral_eq_sub hu (h.radialDatumDerivative_ac_in_of_initial_deriv hu hu0 huv hv hinit)
    (h.radialDatumDerivative_ae_transport_of_initial_deriv hu hu0 huv hv hinit)

/-- The actual q remainder equals the previously estimated source integral.
Paper `e1a0fd5`, `eq:rough-derivative-decomposition`, lines 572–574. -/
theorem radialDatumDerivative_decomposition_of_initial_deriv {u v : ℝ}
    (hu : ui ≤ u) (hu0 : u < 0) (huv : u < v) (hv : v < 0)
    (hinit : HasDerivAt (S.dvpsi ui) (deriv (S.dvpsi ui) v) v) :
    radialDatumDerivative S u v = deriv (S.dvpsi ui) v / S.lam u v ^ 2 +
      radialDatumRemainderIntegral ui S u v := by
  have hqi := h.radialDatumDerivative_eq_weighted le_rfl h.initial_negative
    (hu.trans_lt huv) hv hinit
  have hqi' : radialDatumDerivative S ui v = deriv (S.dvpsi ui) v := by
    simpa only [weightedRadialDatum_initial,
      (h.initial_gauge v ⟨(hu.trans_lt huv).le, hv.le⟩).2, one_pow, div_one] using hqi
  exact h.radialDatumDerivative_decomposition_of_transport hu hu0 huv hv.le hqi'
    (h.radialDatumDerivative_ac_in_of_initial_deriv hu hu0 huv hv hinit)
    (h.radialDatumDerivative_ae_transport_of_initial_deriv hu hu0 huv hv hinit)

/-- Derivative transport and identification: for a.e. incoming label, q is incoming AC, satisfies
the differentiated transport a.e. and in integral form, and splits into the rough initial derivative
and the source remainder. Paper `e1a0fd5`, `lem:ac-datum-propagation`, lines 564–574 and 594–603. -/
theorem radialDatumDerivative_ae_incoming_transport :
    ∀ᵐ v, v ∈ Ioo ui 0 → ∀ u, ui ≤ u → u < 0 → u < v →
      AbsolutelyContinuousOnInterval (fun s => radialDatumDerivative S s v) ui u ∧
      (∀ᵐ s, s ∈ Ioo ui u → HasDerivAt (fun t => radialDatumDerivative S t v)
        (-2 * (S.gamma s v * S.varkappa s v) * radialDatumDerivative S s v +
          radialDatumSource S s v) s) ∧
      IntervalPrimitive (fun s => radialDatumDerivative S s v)
        (fun s => -2 * (S.gamma s v * S.varkappa s v) * radialDatumDerivative S s v +
          radialDatumSource S s v) ui u ∧
      radialDatumDerivative S u v = deriv (S.dvpsi ui) v / S.lam u v ^ 2 +
        radialDatumRemainderIntegral ui S u v := by
  filter_upwards [h.initial_ac_data.ae_differentiableAt] with v hvd
  intro hv u hu hu0 huv
  have hinit := (hvd (by simpa only [uIcc_of_le h.initial_negative.le]
    using Ioo_subset_Icc_self hv)).hasDerivAt
  exact ⟨h.radialDatumDerivative_ac_in_of_initial_deriv hu hu0 huv hv.2 hinit,
    h.radialDatumDerivative_ae_transport_of_initial_deriv hu hu0 huv hv.2 hinit,
    h.radialDatumDerivative_transport_primitive_of_initial_deriv hu hu0 huv hv.2 hinit,
    h.radialDatumDerivative_decomposition_of_initial_deriv hu hu0 huv hv.2 hinit⟩

end StandingFull

end AcExtensionPrinciple

end
