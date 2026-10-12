module

public import AcExtensionPrinciple.ScalarBound.StripDifference
public import AcExtensionPrinciple.ScalarBound.Bootstrap

/-!
# Numerical strip bootstrap improvement

Paper commit `e1a0fd5`, `equations.tex`
lines 506–516, `eq:scalar-bound-strip-difference`. Every parameter
premise here is discharged by the running-maximum construction.
-/

public section

namespace AcExtensionPrinciple.StandingFull

open Set MeasureTheory
open scoped ENNReal

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- At any bootstrapped width up to η, the θ difference is at most F/2.
Gap and flux come from G2/G6; all numerical premises are supplied by
the choices of F, δ and η. Paper `e1a0fd5`, lines 506–515. -/
theorem scalar_bootstrap_difference_le_half {U v F g K M δ η w u s : ℝ}
    (hU : ui ≤ U) (hUη : U < v - η) (hv0 : v ≤ 0)
    (hg : 0 < g) (hK : 0 ≤ K) (hF : 1 ≤ F)
    (hη : 0 ≤ η) (hηhalf : η ≤ S.r U v / 2) (hηeq : η = δ * S.r U v / F)
    (hδ : scalarStripDifferenceConstant ui S g K * δ ≤ 1 / 4)
    (hMsmall : 2 * M ≤ F / 4)
    (hgap : ∀ p ∈ pastTriangle ui, g ≤ 1 - S.mu p.1 p.2)
    (hflux : ∀ v ∈ Ioc ui 0,
      (∫⁻ x in Ioo ui v, ENNReal.ofReal (S.incomingFlux x v)) ≤ ENNReal.ofReal K)
    (hM : ∀ s ∈ Icc ui 0, |S.theta ui s| ≤ M)
    (hw : w ∈ Icc 0 η)
    (htheta : ∀ x ∈ Icc ui U, ∀ t ∈ Icc (v - w) v, |S.theta x t| ≤ 2 * F)
    (hu : u ∈ Icc ui U) (hs : s ∈ Icc (v - w) v) :
    |S.theta u s - S.theta u v| ≤ F / 2 := by
  have hUv : U < v := by linarith
  have hU0 : U < 0 := hUv.trans_le hv0
  have hUs : U < s := by linarith [hs.1, hw.2]
  have hp : (u, v) ∈ pastTriangle ui := ⟨hu.1, hu.2.trans_lt hU0, (hu.2.trans_lt hUv).le, hv0⟩
  have hpU : (U, v) ∈ pastTriangle ui := ⟨hU, hU0, hUv.le, hv0⟩
  have hR := h.r_pos hpU hUv
  have hRu := h.r_pos hp (hu.2.trans_lt hUv)
  have hRmono := h.scalar_radius_in_antitone hu.2 hu.1 hU0 hUv.le hv0
  have hfluxu := h.partial_incoming_flux_le_of_geometric
    (hflux v ⟨hU.trans_lt hUv, hv0⟩) hK hp (hu.2.trans_lt hUv)
  have hdiff := h.scalar_strip_difference hU hUs hs.2 hv0 hg hF
    (by linarith [hs.1, hw.2])
    (fun p hp' => hgap p (h.scalar_rectangle_subset hUs hv0 hp').1)
    (fun p hp' => htheta p.1 hp'.1 p.2 ⟨hs.1.trans hp'.2.1, hp'.2.2⟩)
    hM hu hfluxu
  have hC : 0 ≤ scalarStripDifferenceConstant ui S g K := by
    unfold scalarStripDifferenceConstant scalarStripTransportConstant scalarStripCoefficientConstant
    positivity
  have hfrac : F ^ 2 * (v - s) / S.r u v ≤ δ * F := by
    have hnum : F ^ 2 * (v - s) ≤ F ^ 2 * η :=
      mul_le_mul_of_nonneg_left (by linarith [hs.1, hw.2]) (sq_nonneg F)
    calc
      _ ≤ F ^ 2 * η / S.r U v := div_le_div₀ (mul_nonneg (sq_nonneg F) hη)
        hnum hR hRmono
      _ = δ * F := by rw [hηeq]; field_simp
  have hδF := mul_le_mul_of_nonneg_right hδ (by linarith : 0 ≤ F)
  calc
    _ ≤ _ := hdiff
    _ = 2 * M + scalarStripDifferenceConstant ui S g K *
        (F ^ 2 * (v - s) / S.r u v) := by ring
    _ ≤ 2 * M + scalarStripDifferenceConstant ui S g K * (δ * F) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hfrac hC)
    _ ≤ F / 2 := by nlinarith

end AcExtensionPrinciple.StandingFull

end
