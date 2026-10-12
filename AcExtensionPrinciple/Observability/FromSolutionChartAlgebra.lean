module

public import AcExtensionPrinciple.Observability.FromSolutionChartGeometry

/-!
# Covariance of the normalized characteristic coefficients

Paper `e1a0fd5`, `equations.tex` lines 1460–1473 and
`eq:observability-chart-equations`, lines 1484–1492.
-/

public section

namespace AcExtensionPrinciple.NormalizedBoundaryCoordinates

variable {ui b a₀ a₁ a d T : ℝ} {S : SSFields} {c : DecayCylinder ui S b a₀ a₁}
variable (q : NormalizedBoundaryCoordinates c a d T)

/-- The mass ratio is invariant, including on the axis. Paper `e1a0fd5`,
lines 1460–1473. -/
@[simp] theorem fields_mu (s t : ℝ) : q.fields.mu s t = S.mu (q.U s) (q.V t) := rfl

/-- The scalar is unchanged before applying the observability translation.
Paper `e1a0fd5`, lines 1460–1475. -/
@[simp] theorem fields_phi (s t : ℝ) : q.fields.phi s t = S.phi (q.U s) (q.V t) := by
  simp [fields, SSFields.normalizedPullback]

/-- Outgoing scalar amplitude scales by the incoming Jacobian. Paper
`e1a0fd5`, lines 1460–1473 and 1484–1492. -/
theorem fields_theta (s t : ℝ) :
    q.fields.theta s t = S.theta (q.U s) (q.V t) * q.dV t := by
  simp only [SSFields.theta, fields, SSFields.normalizedPullback, zero_mul, sub_zero]
  ring

/-- Incoming scalar amplitude scales by the outgoing Jacobian. Paper
`e1a0fd5`, lines 1460–1473 and 1484–1492. -/
theorem fields_zeta (s t : ℝ) :
    q.fields.zeta s t = S.zeta (q.U s) (q.V t) * q.dU s := by
  simp only [SSFields.zeta, fields, SSFields.normalizedPullback, zero_mul, sub_zero]
  ring

/-- The mixed radius coefficient acquires both Jacobians. Paper
`e1a0fd5`, lines 1460–1473 and 1484–1492. -/
theorem fields_radiusCoeff (s t : ℝ) :
    q.fields.radiusCoeff s t = S.radiusCoeff (q.U s) (q.V t) * (q.dU s * q.dV t) := by
  simp only [SSFields.radiusCoeff, fields_mu]
  simp only [fields, SSFields.normalizedPullback]
  ring

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

end AcExtensionPrinciple.NormalizedBoundaryCoordinates

end
