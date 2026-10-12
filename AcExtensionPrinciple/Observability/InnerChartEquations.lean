module

public import AcExtensionPrinciple.Observability.InnerChartTransport

/-!
# Covariance and the ten inner-chart primitive equations

Paper `e1a0fd5`, `equations.tex` lines 1460–1473, 1484–1492 and 1901.
-/

public section

namespace AcExtensionPrinciple.InnerBoundaryCoordinates

open Set MeasureTheory

variable {b T K a s₀ s₁ T' : ℝ} {S : SSFields} {h : NormalizedChartData b T K S}
variable {c : InnerCylinder h a s₀ s₁} (q : InnerBoundaryCoordinates c T')

/-- The outgoing mass density acquires exactly the incoming Jacobian,
including points on the regular axis. Paper `e1a0fd5`, lines 1460–1473. -/
theorem fields_massV (s t : ℝ) :
    q.fields.massV s t = S.massV (q.U s) (q.V t) * q.dV t := by
  simp only [SSFields.massV, fields_mu, fields_theta]
  change (1 - S.mu (q.U s) (q.V t)) * (S.theta (q.U s) (q.V t) * q.dV t) ^ 2 /
    (2 * (S.lam (q.U s) (q.V t) * q.dV t)) =
    (1 - S.mu (q.U s) (q.V t)) * S.theta (q.U s) (q.V t) ^ 2 /
      (2 * S.lam (q.U s) (q.V t)) * q.dV t
  rw [mul_pow, show 2 * (S.lam (q.U s) (q.V t) * q.dV t) =
    (2 * S.lam (q.U s) (q.V t)) * q.dV t by ring]
  calc
    _ = (((1 - S.mu (q.U s) (q.V t)) * S.theta (q.U s) (q.V t) ^ 2 * q.dV t) *
        q.dV t) / ((2 * S.lam (q.U s) (q.V t)) * q.dV t) := by ring
    _ = _ := by rw [mul_div_mul_right _ _ (q.dV_positive t).ne']; ring

/-- The incoming mass density acquires exactly the outgoing Jacobian,
including points on the regular axis. Paper `e1a0fd5`, lines 1460–1473. -/
theorem fields_massU (s t : ℝ) :
    q.fields.massU s t = S.massU (q.U s) (q.V t) * q.dU s := by
  simp only [SSFields.massU, fields_mu, fields_zeta]
  change (1 - S.mu (q.U s) (q.V t)) * (S.zeta (q.U s) (q.V t) * q.dU s) ^ 2 /
    (2 * (S.nu (q.U s) (q.V t) * q.dU s)) =
    (1 - S.mu (q.U s) (q.V t)) * S.zeta (q.U s) (q.V t) ^ 2 /
      (2 * S.nu (q.U s) (q.V t)) * q.dU s
  rw [mul_pow, show 2 * (S.nu (q.U s) (q.V t) * q.dU s) =
    (2 * S.nu (q.U s) (q.V t)) * q.dU s by ring]
  calc
    _ = (((1 - S.mu (q.U s) (q.V t)) * S.zeta (q.U s) (q.V t) ^ 2 * q.dU s) *
        q.dU s) / ((2 * S.nu (q.U s) (q.V t)) * q.dU s) := by ring
    _ = _ := by rw [mul_div_mul_right _ _ (q.dU_positive s).ne']; ring


/-- The ten normalized characteristic equations follow from the outer
normalized chart and the constructed coordinates. No boundary chain rule
or extra PDE regularity is assumed. Paper `e1a0fd5`, lines 1460–1473,
`eq:observability-chart-equations`, lines 1484–1492. -/
theorem chart_equations :
    ChartIntegralEquations (chartCylinder q.axisGraph T') q.fields where
  radius_t s x y hxy hseg :=
    (h.equations.radius_t (q.U s) (q.V x) (q.V y) (q.V.monotone hxy)
      (q.source_outSeg_subset hseg)).comp (q.gaugeV x y)
  radius_s t x y hxy hseg :=
    (h.equations.radius_s (q.V t) (q.U x) (q.U y) (q.U.monotone hxy)
      (q.source_inSeg_subset hseg)).comp (q.gaugeU x y)
  psi_t := by
    intro s x y hxy hseg
    have hp := (h.equations.psi_t (q.U s) (q.V x) (q.V y)
      (q.V.monotone hxy) (q.source_outSeg_subset hseg)).comp (q.gaugeV x y)
    apply hp.congr
    · intro z _
      simp only [fields, PropA4.separatePullback]
    · intro z _
      simp only [fields, PropA4.separatePullback]
  psi_s := by
    intro t x y hxy hseg
    have hp := (h.equations.psi_s (q.V t) (q.U x) (q.U y)
      (q.U.monotone hxy) (q.source_inSeg_subset hseg)).comp (q.gaugeU x y)
    apply hp.congr
    · intro z _
      simp only [fields, PropA4.separatePullback]
    · intro z _
      simp only [fields, PropA4.separatePullback]
  mass_t := by
    intro s x y hxy hseg
    have hp := (h.equations.mass_t (q.U s) (q.V x) (q.V y)
      (q.V.monotone hxy) (q.source_outSeg_subset hseg)).comp (q.gaugeV x y)
    exact hp.congr (fun z _ => rfl) (fun z _ => (q.fields_massV s z).symm)
  mass_s := by
    intro t x y hxy hseg
    have hp := (h.equations.mass_s (q.V t) (q.U x) (q.U y)
      (q.U.monotone hxy) (q.source_inSeg_subset hseg)).comp (q.gaugeU x y)
    exact hp.congr (fun z _ => rfl) (fun z _ => (q.fields_massU z t).symm)
  lam_s := by
    intro t x y hxy hseg
    have hp := ((h.equations.lam_s (q.V t) (q.U x) (q.U y)
      (q.U.monotone hxy) (q.source_inSeg_interior hseg)).comp
        (q.gaugeU x y)).mul_const (q.dV t)
    apply hp.congr (fun z _ => rfl)
    intro z _
    dsimp only
    rw [q.fields_radiusCoeff]
    ring
  nu_t := by
    intro s x y hxy hseg
    have hp := ((h.equations.nu_t (q.U s) (q.V x) (q.V y)
      (q.V.monotone hxy) (q.source_outSeg_interior hseg)).comp
        (q.gaugeV x y)).mul_const (q.dU s)
    apply hp.congr (fun z _ => rfl)
    intro z _
    dsimp only
    rw [q.fields_radiusCoeff]
    ring
  dvpsi_s := by
    intro t x y hxy hseg
    have hp := ((h.equations.dvpsi_s (q.V t) (q.U x) (q.U y)
      (q.U.monotone hxy) (q.source_inSeg_interior hseg)).comp
        (q.gaugeU x y)).mul_const (q.dV t)
    apply hp.congr
    · intro z _
      simp only [fields, PropA4.separatePullback]
    · intro z _
      dsimp only
      rw [q.fields_radiusCoeff, fields, PropA4.separatePullback]
      ring
  dupsi_t := by
    intro s x y hxy hseg
    have hp := ((h.equations.dupsi_t (q.U s) (q.V x) (q.V y)
      (q.V.monotone hxy) (q.source_outSeg_interior hseg)).comp
        (q.gaugeV x y)).mul_const (q.dU s)
    apply hp.congr
    · intro z _
      simp only [fields, PropA4.separatePullback]
    · intro z _
      dsimp only
      rw [q.fields_radiusCoeff, fields, PropA4.separatePullback]
      ring


end AcExtensionPrinciple.InnerBoundaryCoordinates

end
