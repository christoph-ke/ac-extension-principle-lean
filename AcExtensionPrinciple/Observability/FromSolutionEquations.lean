module

public import AcExtensionPrinciple.Observability.FromSolutionSegments

/-!
# All characteristic equations in the constructed normalized chart

Paper `e1a0fd5`, `equations.tex` lines 1460–1473 and
`eq:observability-chart-equations`, lines 1484–1492.
Each source primitive is transported by an increasing C¹ inverse coordinate.
-/

public section

namespace AcExtensionPrinciple.NormalizedBoundaryCoordinates

open Set MeasureTheory

variable {ui b a₀ a₁ a d T : ℝ} {S : SSFields} {c : DecayCylinder ui S b a₀ a₁}
variable (q : NormalizedBoundaryCoordinates c a d T)

/-- The ten normalized characteristic equations follow from the standing
integral solution and the constructed coordinates. No boundary chain rule
or extra PDE regularity is assumed. Paper `e1a0fd5`, lines 1460–1473,
`eq:observability-chart-equations`, lines 1484–1492. -/
theorem chart_equations (h : StandingFull ui S) (ha : a₀ ≤ a) (hd : d ≤ a₁) :
    ChartIntegralEquations (chartCylinder q.axisGraph T) q.fields where
  radius_t s x y hxy hseg :=
    (h.regularCenter.localBV.radius_out (q.U s) (q.V x) (q.V y) (q.V.monotone hxy)
      (q.source_outSeg_subset ha hd hseg)).comp (q.gaugeV x y)
  radius_s t x y hxy hseg :=
    (h.regularCenter.localBV.radius_in (q.V t) (q.U x) (q.U y) (q.U.monotone hxy)
      (q.source_inSeg_subset ha hd hseg)).comp (q.gaugeU x y)
  psi_t := by
    intro s x y hxy hseg
    have hp := (h.regularCenter.localBV.psi_out (q.U s) (q.V x) (q.V y)
      (q.V.monotone hxy) (q.source_outSeg_subset ha hd hseg)).comp (q.gaugeV x y)
    apply hp.congr
    · intro z _
      simp only [fields, SSFields.normalizedPullback, sub_zero]
    · intro z _
      simp only [fields, SSFields.normalizedPullback, zero_mul, sub_zero]
  psi_s := by
    intro t x y hxy hseg
    have hp := (h.regularCenter.localBV.psi_in (q.V t) (q.U x) (q.U y)
      (q.U.monotone hxy) (q.source_inSeg_subset ha hd hseg)).comp (q.gaugeU x y)
    apply hp.congr
    · intro z _
      simp only [fields, SSFields.normalizedPullback, sub_zero]
    · intro z _
      simp only [fields, SSFields.normalizedPullback, zero_mul, sub_zero]
  mass_t := by
    intro s x y hxy hseg
    have hp := (h.regularCenter.localBV.mass_out (q.U s) (q.V x) (q.V y)
      (q.V.monotone hxy) (q.source_outSeg_subset ha hd hseg)).comp (q.gaugeV x y)
    exact hp.congr (fun z _ => rfl) (fun z _ => (q.fields_massV s z).symm)
  mass_s := by
    intro t x y hxy hseg
    have hp := (h.regularCenter.localBV.mass_in (q.V t) (q.U x) (q.U y)
      (q.U.monotone hxy) (q.source_inSeg_subset ha hd hseg)).comp (q.gaugeU x y)
    exact hp.congr (fun z _ => rfl) (fun z _ => (q.fields_massU z t).symm)
  lam_s := by
    intro t x y hxy hseg
    have hp := ((h.regularCenter.localBV.lam_in (q.V t) (q.U x) (q.U y)
      (q.U.monotone hxy) (q.source_inSeg_interior h ha hd hseg)).comp
        (q.gaugeU x y)).mul_const (q.dV t)
    apply hp.congr (fun z _ => rfl)
    intro z _
    dsimp only
    rw [q.fields_radiusCoeff]
    ring
  nu_t := by
    intro s x y hxy hseg
    have hp := ((h.regularCenter.localBV.nu_out (q.U s) (q.V x) (q.V y)
      (q.V.monotone hxy) (q.source_outSeg_interior h ha hd hseg)).comp
        (q.gaugeV x y)).mul_const (q.dU s)
    apply hp.congr (fun z _ => rfl)
    intro z _
    dsimp only
    rw [q.fields_radiusCoeff]
    ring
  dvpsi_s := by
    intro t x y hxy hseg
    have hp := ((h.regularCenter.localBV.dvpsi_in (q.V t) (q.U x) (q.U y)
      (q.U.monotone hxy) (q.source_inSeg_interior h ha hd hseg)).comp
        (q.gaugeU x y)).mul_const (q.dV t)
    apply hp.congr
    · intro z _
      simp only [fields, SSFields.normalizedPullback, zero_mul, sub_zero]
    · intro z _
      dsimp only
      rw [q.fields_radiusCoeff, q.fields_phi]
      ring
  dupsi_t := by
    intro s x y hxy hseg
    have hp := ((h.regularCenter.localBV.dupsi_out (q.U s) (q.V x) (q.V y)
      (q.V.monotone hxy) (q.source_outSeg_interior h ha hd hseg)).comp
        (q.gaugeV x y)).mul_const (q.dU s)
    apply hp.congr
    · intro z _
      simp only [fields, SSFields.normalizedPullback, zero_mul, sub_zero]
    · intro z _
      dsimp only
      rw [q.fields_radiusCoeff, q.fields_phi]
      ring

end AcExtensionPrinciple.NormalizedBoundaryCoordinates

end
