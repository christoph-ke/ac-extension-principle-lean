module

public import AcExtensionPrinciple.Renormalized.ClassTransport
public import AcExtensionPrinciple.Weighted.Transport

/-!
# Transported initial datum and remainder in the solution class

Paper `e1a0fd5`, `equations.tex` lines 1082–1125.
Uniform geometric bounds and the Lemma 2.2 datum transport are explicit
premises of the helpers.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- The transported initial renormalized datum. Paper `e1a0fd5`,
`eq:renormalized-initial-transport`, lines 1084–1094. -/
@[expose] noncomputable def SSFields.renormalizedInitial
    (S : SSFields) (q : ℝ → ℝ → ℝ) (ui u v : ℝ) : ℝ :=
  S.kappa ui v / S.kappa u v * S.renormalizedDerivative q ui v

/-- The renormalized remainder. Paper `e1a0fd5`,
`eq:renormalized-splitting`, lines 1088–1089. -/
@[expose] noncomputable def SSFields.renormalizedRemainder
    (S : SSFields) (q : ℝ → ℝ → ℝ) (ui u v : ℝ) : ℝ :=
  S.renormalizedDerivative q u v - S.renormalizedInitial q ui u v

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Zero remainder on the original initial cone. Paper `e1a0fd5`,
`eq:renormalized-remainder-transport`, lines 1100–1105. -/
theorem renormalizedRemainder_initial (q : ℝ → ℝ → ℝ) {v : ℝ}
    (hv : v ∈ Icc ui 0) : S.renormalizedRemainder q ui ui v = 0 := by
  have hp : (ui, v) ∈ pastTriangle ui := ⟨le_rfl, h.initial_negative, hv.1, hv.2⟩
  simp [SSFields.renormalizedRemainder, SSFields.renormalizedInitial,
    ne_of_gt (h.kappa_pos hp)]

/-- The class Raychaudhuri equation gives the derivative of κ a.e.
Paper `e1a0fd5`, `eq:raychaudhuri`, lines 90–92 and 1119. -/
theorem kappa_derivative_ae {v a b : ℝ} (hab : a ≤ b) (ha : ui ≤ a)
    (hb0 : b < 0) (hbv : b < v) (hv0 : v ≤ 0) :
    ∀ᵐ x, x ∈ Ioo a b → HasDerivAt (fun u => S.kappa u v)
      (-S.incomingFlux x v * S.kappa x v) x := by
  filter_upwards [h.incoming_reduced_ae hab ha hb0 hbv hv0] with x hx
  intro hxI
  obtain ⟨hr, hl, hm, _, _⟩ := hx hxI
  have hp : (x, v) ∈ pastTriangle ui :=
    ⟨ha.trans hxI.1.le, hxI.2.trans hb0, (hxI.2.trans hbv).le, hv0⟩
  have hr0 := h.r_pos hp (hxI.2.trans hbv)
  have hn0 := h.nu_neg hp
  have hmu := (h.mu_bounds hp).2
  have hmass := IncomingRay.mass_ratio (r := fun u => S.r u v)
    (m := fun u => S.m u v) (nu := fun u => S.nu u v) (phiU := fun u => S.duphi u v)
    hr hm hr0 hn0
  have he : HasDerivAt (fun u => S.lam u v)
      (S.lam x v * (S.nu x v / (1 - S.mu x v) * (S.mu x v / S.r x v))) x := by
    convert hl using 1
    dsimp [SSFields.kappa, SSFields.varkappa, kappaOf, varkappaOf]
    ring
  convert ray_normalized_expansion (r := fun u => S.r u v) (b := fun u => S.lam u v)
    (mu := fun u => S.mu u v) (x := x) (a := S.nu x v) (p := S.duphi x v)
    he hmass (ne_of_gt hr0) (ne_of_lt hn0)
    (ne_of_gt (sub_pos.mpr hmu)) using 1
  · rfl
  · dsimp [SSFields.incomingFlux, SSFields.kappa, kappaOf]
    field_simp [ne_of_lt hn0]

/-- AC of the transported datum, independently of the initial datum's
regularity in `v`. Paper `e1a0fd5`, lines 1084–1094 and 1119. -/
theorem renormalizedInitial_ac_in (q : ℝ → ℝ → ℝ) {v a b : ℝ}
    (hab : a ≤ b) (ha : ui ≤ a) (hb0 : b < 0) (hbv : b < v) (hv0 : v ≤ 0) :
    AbsolutelyContinuousOnInterval (fun u => S.renormalizedInitial q ui u v) a b := by
  have hi := positive_ac_inv (h.kappa_ac_in hab ha hb0 hbv hv0) (fun x hx => by
    rw [uIcc_of_le hab] at hx
    exact h.kappa_pos (p := (x, v))
      ⟨ha.trans hx.1, hx.2.trans_lt hb0, (hx.2.trans_lt hbv).le, hv0⟩)
  convert hi.const_mul (S.kappa ui v * S.renormalizedDerivative q ui v) using 1
  funext x
  dsimp [SSFields.renormalizedInitial]
  ring

/-- The explicit κ-ratio solves the homogeneous initial transport equation
a.e. Paper `e1a0fd5`, `eq:renormalized-initial-transport`, lines 1084–1094. -/
theorem renormalizedInitial_ae (q : ℝ → ℝ → ℝ) {v a b : ℝ}
    (hab : a ≤ b) (ha : ui ≤ a) (hb0 : b < 0) (hbv : b < v) (hv0 : v ≤ 0) :
    ∀ᵐ x, x ∈ Ioo a b → HasDerivAt (fun u => S.renormalizedInitial q ui u v)
      (S.incomingFlux x v * S.renormalizedInitial q ui x v) x := by
  filter_upwards [h.kappa_derivative_ae hab ha hb0 hbv hv0] with x hx
  intro hxI
  have hp : (x, v) ∈ pastTriangle ui :=
    ⟨ha.trans hxI.1.le, hxI.2.trans hb0, (hxI.2.trans hbv).le, hv0⟩
  convert ((hx hxI).inv (ne_of_gt (h.kappa_pos hp))).const_mul
    (S.kappa ui v * S.renormalizedDerivative q ui v) using 1
  · funext s
    dsimp [SSFields.renormalizedInitial]
    ring
  · dsimp [SSFields.renormalizedInitial]
    field_simp [ne_of_gt (h.kappa_pos hp)]

/-- Integral form of homogeneous initial transport. Paper `e1a0fd5`,
`eq:renormalized-initial-transport`, lines 1084–1094. -/
theorem renormalizedInitial_primitive (q : ℝ → ℝ → ℝ) {v a b : ℝ}
    (hab : a ≤ b) (ha : ui ≤ a) (hb0 : b < 0) (hbv : b < v) (hv0 : v ≤ 0) :
    IntervalPrimitive (fun u => S.renormalizedInitial q ui u v)
      (fun u => S.incomingFlux u v * S.renormalizedInitial q ui u v) a b :=
  ac_integral_eq_sub hab (h.renormalizedInitial_ac_in q hab ha hb0 hbv hv0)
    (h.renormalizedInitial_ae q hab ha hb0 hbv hv0)

/-- Initial domination with a uniform constant chosen before `(u,v)`.
Paper `e1a0fd5`, `eq:renormalized-initial-domination`, lines 1092–1097.
The two κ bounds are exactly the intended Lemma 1.1 G2 conclusions. -/
theorem renormalizedInitial_domination_of_geometric (q : ℝ → ℝ → ℝ) {ci : ℝ}
    (hci : 0 < ci)
    (hκ : ∀ p ∈ pastTriangle ui,
      Real.exp (-Bstar ui S) ≤ S.kappa p.1 p.2 ∧ S.kappa p.1 p.2 ≤ 1 / ci) :
    ∀ p ∈ pastTriangle ui, |S.renormalizedInitial q ui p.1 p.2| ≤
      ((1 / ci) / Real.exp (-Bstar ui S)) * |S.renormalizedDerivative q ui p.2| := by
  intro p hp
  have hi : (ui, p.2) ∈ pastTriangle ui :=
    ⟨le_rfl, h.initial_negative, hp.1.trans hp.2.2.1, hp.2.2.2⟩
  rw [SSFields.renormalizedInitial, abs_mul, abs_of_pos
    (div_pos (h.kappa_pos hi) (h.kappa_pos hp))]
  gcongr
  · exact (hκ (ui, p.2) hi).2
  · exact (hκ p hp).1

/-- Subtraction gives the renormalized remainder equation a.e.
Paper `e1a0fd5`, `eq:renormalized-remainder-transport`, lines 1100–1105. -/
theorem renormalizedRemainder_ae_of_incoming_transport
    (q : ℝ → ℝ → ℝ) {v a b : ℝ}
    (hab : a ≤ b) (ha : ui ≤ a) (hb0 : b < 0) (hbv : b < v) (hv0 : v ≤ 0)
    (hj : ∀ᵐ x, x ∈ Ioo a b → HasDerivAt (fun u => S.renormalizedDerivative q u v)
      (S.incomingFlux x v * S.renormalizedDerivative q x v +
        (3 * S.nu x v / S.r x v) * S.dvphi x v * S.renormalizedInteraction x v) x) :
    ∀ᵐ x, x ∈ Ioo a b → HasDerivAt (fun u => S.renormalizedRemainder q ui u v)
      (S.incomingFlux x v * S.renormalizedRemainder q ui x v +
        (3 * S.nu x v / S.r x v) * S.dvphi x v * S.renormalizedInteraction x v) x := by
  filter_upwards [hj, h.renormalizedInitial_ae q hab ha hb0 hbv hv0] with x hx hix
  intro hxI
  convert (hx hxI).sub (hix hxI) using 1
  · rfl
  · dsimp [SSFields.renormalizedRemainder]
    ring

/-- AC of the remainder on incoming compact segments from AC of `j`.
Paper `e1a0fd5`, `eq:renormalized-splitting`, lines 1088–1105. -/
theorem renormalizedRemainder_ac_of_incoming_ac (q : ℝ → ℝ → ℝ) {v a b : ℝ}
    (hab : a ≤ b) (ha : ui ≤ a) (hb0 : b < 0) (hbv : b < v) (hv0 : v ≤ 0)
    (hj : AbsolutelyContinuousOnInterval (fun u => S.renormalizedDerivative q u v) a b) :
    AbsolutelyContinuousOnInterval (fun u => S.renormalizedRemainder q ui u v) a b :=
  hj.fun_sub (h.renormalizedInitial_ac_in q hab ha hb0 hbv hv0)

/-- Integral form of the remainder transport, subtracting the homogeneous
initial transport. Paper `e1a0fd5`, `eq:renormalized-remainder-transport`,
lines 1100–1105. The inputs are the preceding Lemma 3.1 conclusions. -/
theorem renormalizedRemainder_primitive_of_incoming_transport
    (q : ℝ → ℝ → ℝ) {v a b : ℝ}
    (hab : a ≤ b) (ha : ui ≤ a) (hb0 : b < 0) (hbv : b < v) (hv0 : v ≤ 0)
    (hjAC : AbsolutelyContinuousOnInterval (fun u => S.renormalizedDerivative q u v) a b)
    (hj : ∀ᵐ x, x ∈ Ioo a b → HasDerivAt (fun u => S.renormalizedDerivative q u v)
      (S.incomingFlux x v * S.renormalizedDerivative q x v +
        (3 * S.nu x v / S.r x v) * S.dvphi x v * S.renormalizedInteraction x v) x) :
    IntervalPrimitive (fun u => S.renormalizedRemainder q ui u v)
      (fun u => S.incomingFlux u v * S.renormalizedRemainder q ui u v +
        (3 * S.nu u v / S.r u v) * S.dvphi u v * S.renormalizedInteraction u v) a b :=
  ac_integral_eq_sub hab (h.renormalizedRemainder_ac_of_incoming_ac q hab ha hb0 hbv hv0 hjAC)
    (h.renormalizedRemainder_ae_of_incoming_transport q hab ha hb0 hbv hv0 hj)

end StandingFull

/-- Bounded `r |J|`, a positive mass gap, and a positive outgoing expansion
control the energy density by `|J|`. Paper `e1a0fd5`,
`eq:renormalized-initial-energy`, lines 1112–1124. -/
theorem renormalized_energy_density_le {r J gap lam c d M : ℝ}
    (hr : 0 ≤ r) (hc : 0 < c) (hd : 0 < d) (hgap : c ≤ gap) (hlam : d ≤ lam)
    (hJ : r * |J| ≤ M) :
    r * J ^ 2 / (gap ^ 2 * lam) ≤ (M / (c ^ 2 * d)) * |J| := by
  have hg : 0 < gap := hc.trans_le hgap
  have hl : 0 < lam := hd.trans_le hlam
  have hs : c ^ 2 * d ≤ gap ^ 2 * lam :=
    mul_le_mul (by nlinarith) hlam hd.le (sq_nonneg gap)
  have hden : 0 < c ^ 2 * d := mul_pos (sq_pos_of_pos hc) hd
  have hn : 0 ≤ r * J ^ 2 := mul_nonneg hr (sq_nonneg _)
  calc
    _ ≤ r * J ^ 2 / (c ^ 2 * d) := div_le_div_of_nonneg_left hn hden hs
    _ ≤ M * |J| / (c ^ 2 * d) := by
      apply div_le_div_of_nonneg_right ?_ hden.le
      nlinarith [mul_le_mul_of_nonneg_right hJ (abs_nonneg J), sq_abs J]
    _ = _ := by ring

/-- The initial energy is integrable despite only L¹ control of the remainder.
Paper `e1a0fd5`, `eq:renormalized-initial-energy`, lines 1112–1124.
Measurability follows from the class fields and the transported splitting;
the majorant comes from `renormalized_energy_density_le`. -/
theorem renormalized_energy_integrable_of_l1 {E J : ℝ → ℝ} {a b C : ℝ}
    (hE : AEStronglyMeasurable E (volume.restrict (Ioc a b)))
    (hJ : IntegrableOn J (Ioc a b))
    (hbound : ∀ᵐ v ∂volume.restrict (Ioc a b), |E v| ≤ C * |J v|) :
    IntegrableOn E (Ioc a b) := by
  apply ((hJ.norm).const_mul C).mono' hE
  simpa only [Real.norm_eq_abs] using hbound

end AcExtensionPrinciple

end
