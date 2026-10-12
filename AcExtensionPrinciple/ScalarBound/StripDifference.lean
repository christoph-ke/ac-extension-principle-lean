module

public import AcExtensionPrinciple.ScalarBound.TransportComparison

/-!
# The integrated scalar strip difference

Paper commit `e1a0fd5`, `equations.tex`
lines 498–512, `eq:scalar-bound-strip-difference`. The comparison
constant is chosen before every strip and running-maximum parameter.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory

/-- Explicit constant in the integrated θ comparison; only the geometric
gap, blueshift and incoming flux bound enter. Paper `e1a0fd5`, lines 506–512. -/
@[expose] noncomputable def scalarStripDifferenceConstant (ui : ℝ) (S : SSFields) (g K : ℝ) : ℝ :=
  scalarStripTransportConstant ui S g * (K / 2 + 5 / 4)

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Integrating the transport comparison gives the decisive strip
difference. Gap and flux premises are discharged by G2 and G6; θ is
the bootstrap premise, and M comes from the initial-average bound.
Paper `e1a0fd5`, `eq:scalar-bound-strip-difference`, lines 506–512. -/
theorem scalar_strip_difference {U a b F g K M u : ℝ}
    (hU : ui ≤ U) (hUa : U < a) (hab : a ≤ b) (hb0 : b ≤ 0)
    (hg : 0 < g) (hF : 1 ≤ F) (hwidth : b - a ≤ S.r U b / 2)
    (hgap : ∀ p ∈ Icc ui U ×ˢ Icc a b, g ≤ 1 - S.mu p.1 p.2)
    (htheta : ∀ p ∈ Icc ui U ×ˢ Icc a b, |S.theta p.1 p.2| ≤ 2 * F)
    (hM : ∀ s ∈ Icc ui 0, |S.theta ui s| ≤ M)
    (hu : u ∈ Icc ui U) (hflux : (∫ s in ui..u, S.incomingFlux s b) ≤ K) :
    |S.theta u a - S.theta u b| ≤
      2 * M + scalarStripDifferenceConstant ui S g K * F ^ 2 * (b - a) / S.r u b := by
  have hU0 : U < 0 := hUa.trans_le (hab.trans hb0)
  have hua : u < a := hu.2.trans_lt hUa
  have hub : u < b := hua.trans_le hab
  have hp : (u, b) ∈ pastTriangle ui := ⟨hu.1, hu.2.trans_lt hU0, hub.le, hb0⟩
  have hA := h.theta_primitive_in hu.1 le_rfl hp.2.1 hua (hab.trans hb0)
  have hB := h.theta_primitive_in hu.1 le_rfl hp.2.1 hub hb0
  let C := scalarStripTransportConstant ui S g
  have hC : 0 ≤ C := by
    dsimp [C, scalarStripTransportConstant, scalarStripCoefficientConstant]
    positivity
  have he : S.theta u a - S.theta u b = S.theta ui a - S.theta ui b +
      ∫ s in ui..u, -S.lam s a * S.duphi s a - (-S.lam s b * S.duphi s b) := by
    have heA := hA.2
    have heB := hB.2
    dsimp only at heA heB
    rw [intervalIntegral.integral_sub hA.1 hB.1]
    linarith
  have hI : |∫ s in ui..u, -S.lam s a * S.duphi s a - (-S.lam s b * S.duphi s b)| ≤
      C * F ^ 2 * (b - a) * ((1 + (K / 2 + 1 / 4)) / S.r u b) := by
    have hiR := (h.inv_radius_primitive hu.1 le_rfl hp.2.1 hub hb0).1
    have hiW := h.weighted_time_integrable hp hub
    calc
      _ ≤ ∫ s in ui..u, |-S.lam s a * S.duphi s a - (-S.lam s b * S.duphi s b)| :=
        intervalIntegral.abs_integral_le_integral_abs hu.1
      _ ≤ ∫ s in ui..u, (C * F ^ 2 * (b - a)) *
          ((-S.nu s b) / S.r s b ^ 2 + |S.duphi s b| / S.r s b) :=
        intervalIntegral.integral_mono_on hu.1 (hA.1.sub hB.1).abs
          ((hiR.add hiW).const_mul _) (by
            intro s hs
            exact h.scalar_strip_transport_difference hU hUa hab hb0 hg hF hwidth hgap htheta
              ⟨hs.1, hs.2.trans hu.2⟩)
      _ = C * F ^ 2 * (b - a) *
          ((∫ s in ui..u, -S.nu s b / S.r s b ^ 2) +
            ∫ s in ui..u, |S.duphi s b| / S.r s b) := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hiR hiW]
      _ ≤ C * F ^ 2 * (b - a) *
          (1 / S.r u b + (K / 2 + 1 / 4) / S.r u b) :=
        mul_le_mul_of_nonneg_left (add_le_add (h.radius_time_integral_le hp hub)
          (h.weighted_time_integral_le_of_flux hp hub hflux))
          (mul_nonneg (mul_nonneg hC (sq_nonneg F)) (sub_nonneg.mpr hab))
      _ = _ := by ring
  have hma := hM a ⟨hU.trans hUa.le, hab.trans hb0⟩
  have hmb := hM b ⟨hU.trans (hUa.le.trans hab), hb0⟩
  have hinit : |S.theta ui a - S.theta ui b| ≤ 2 * M :=
    (abs_sub _ _).trans (by linarith)
  rw [he]
  exact (abs_add_le _ _).trans ((add_le_add hinit hI).trans_eq (by
    dsimp [C, scalarStripDifferenceConstant]
    ring))

end StandingFull

end AcExtensionPrinciple

end
