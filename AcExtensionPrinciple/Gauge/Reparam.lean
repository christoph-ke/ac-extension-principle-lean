module

public import AcExtensionPrinciple.Solution.Fields
public import Mathlib.Tactic

/-!
# Pullback of the spherical fields

Components for paper commit `e1a0fd5`, `equations.tex`
lines 1390–1445, especially `eq:continuation-null-gauge` and
`eq:terminal-expansion-gauge`. The derivative of the coordinate map is
supplied separately; these algebraic identities do not require differentiability.
-/

public section

namespace AcExtensionPrinciple
namespace SSFields

/-- Pullback with a supplied derivative. Paper `e1a0fd5`,
`eq:continuation-null-gauge`, lines 1390–1394 and 1422. -/
@[expose] noncomputable def pullback (S : SSFields) (T dT : ℝ → ℝ) : SSFields where
  r u v := S.r (T u) (T v)
  phi u v := S.phi (T u) (T v)
  m u v := S.m (T u) (T v)
  lam u v := S.lam (T u) (T v) * dT v
  nu u v := S.nu (T u) (T v) * dT u
  dvpsi u v := S.dvpsi (T u) (T v) * dT v
  dupsi u v := S.dupsi (T u) (T v) * dT u

/-- Mass ratio is invariant, including on the axis. Paper `e1a0fd5`,
`eq:continuation-null-gauge`, lines 1390–1394. -/
@[simp] theorem pullback_mu (S : SSFields) (T dT : ℝ → ℝ) (u v : ℝ) :
    (S.pullback T dT).mu u v = S.mu (T u) (T v) := rfl

/-- The outgoing scalar quotient is invariant. Paper `e1a0fd5`,
`eq:continuation-initial-datum`, lines 1396–1400. -/
theorem pullback_dvpsi_div_lam (S : SSFields) (T dT : ℝ → ℝ) (u v : ℝ)
    (hv : dT v ≠ 0) :
    (S.pullback T dT).dvpsi u v / (S.pullback T dT).lam u v =
      S.dvpsi (T u) (T v) / S.lam (T u) (T v) := by
  exact mul_div_mul_right _ _ hv

/-- The incoming scalar quotient is invariant. Paper `e1a0fd5`,
`equations.tex` lines 1431–1433. -/
theorem pullback_dupsi_div_nu (S : SSFields) (T dT : ℝ → ℝ) (u v : ℝ)
    (hu : dT u ≠ 0) :
    (S.pullback T dT).dupsi u v / (S.pullback T dT).nu u v =
      S.dupsi (T u) (T v) / S.nu (T u) (T v) := by
  exact mul_div_mul_right _ _ hu

/-- The outgoing normalized expansion scales in the outgoing variable.
Paper `e1a0fd5`, `eq:continuation-null-gauge`, lines 1390–1394. -/
theorem pullback_kappa (S : SSFields) (T dT : ℝ → ℝ) (u v : ℝ) :
    (S.pullback T dT).kappa u v = S.kappa (T u) (T v) * dT v := by
  simp only [kappa, kappaOf]
  rw [pullback_mu]
  simp only [pullback]
  ring

/-- The incoming normalized expansion scales in the incoming variable.
Paper `e1a0fd5`, `eq:continuation-null-gauge`, lines 1390–1394. -/
theorem pullback_gamma (S : SSFields) (T dT : ℝ → ℝ) (u v : ℝ) :
    (S.pullback T dT).gamma u v = S.gamma (T u) (T v) * dT u := by
  simp only [gamma, gammaOf]
  rw [pullback_mu]
  simp only [pullback]
  ring

/-- The radial mass coefficient is invariant. Paper `e1a0fd5`,
`eq:continuation-null-gauge`, lines 1390–1394. -/
@[simp] theorem pullback_varkappa (S : SSFields) (T dT : ℝ → ℝ) (u v : ℝ) :
    (S.pullback T dT).varkappa u v = S.varkappa (T u) (T v) := rfl

/-- The outgoing scalar amplitude scales in the outgoing variable.
Paper `e1a0fd5`, `eq:continuation-null-gauge`, lines 1390–1394. -/
theorem pullback_theta (S : SSFields) (T dT : ℝ → ℝ) (u v : ℝ) :
    (S.pullback T dT).theta u v = S.theta (T u) (T v) * dT v := by
  simp only [theta, pullback]
  ring

/-- The incoming scalar amplitude scales in the incoming variable.
Paper `e1a0fd5`, `eq:continuation-null-gauge`, lines 1390–1394. -/
theorem pullback_zeta (S : SSFields) (T dT : ℝ → ℝ) (u v : ℝ) :
    (S.pullback T dT).zeta u v = S.zeta (T u) (T v) * dT u := by
  simp only [zeta, pullback]
  ring

/-- The radius transport coefficient has one factor from each variable.
Paper `e1a0fd5`, `eq:continuation-null-gauge`, lines 1390–1394. -/
theorem pullback_radiusCoeff (S : SSFields) (T dT : ℝ → ℝ) (u v : ℝ) :
    (S.pullback T dT).radiusCoeff u v =
      S.radiusCoeff (T u) (T v) * (dT u * dT v) := by
  simp only [radiusCoeff]
  rw [pullback_mu]
  simp only [pullback]
  ring

/-- The outgoing mass integrand has the outgoing Jacobian factor.
Paper `e1a0fd5`, `eq:continuation-null-gauge`, lines 1390–1394. -/
theorem pullback_massV (S : SSFields) (T dT : ℝ → ℝ) (u v : ℝ)
    (hv : dT v ≠ 0) :
    (S.pullback T dT).massV u v = S.massV (T u) (T v) * dT v := by
  simp only [massV]
  rw [pullback_mu, pullback_theta]
  simp only [pullback]
  rw [mul_pow, show 2 * (S.lam (T u) (T v) * dT v) =
    (2 * S.lam (T u) (T v)) * dT v by ring]
  calc
    _ = ((1 - S.mu (T u) (T v)) * S.theta (T u) (T v) ^ 2 * dT v) *
        dT v / ((2 * S.lam (T u) (T v)) * dT v) := by ring
    _ = _ := by rw [mul_div_mul_right _ _ hv]; ring

/-- The incoming mass integrand has the incoming Jacobian factor.
Paper `e1a0fd5`, `eq:continuation-null-gauge`, lines 1390–1394. -/
theorem pullback_massU (S : SSFields) (T dT : ℝ → ℝ) (u v : ℝ)
    (hu : dT u ≠ 0) :
    (S.pullback T dT).massU u v = S.massU (T u) (T v) * dT u := by
  simp only [massU]
  rw [pullback_mu, pullback_zeta]
  simp only [pullback]
  rw [mul_pow, show 2 * (S.nu (T u) (T v) * dT u) =
    (2 * S.nu (T u) (T v)) * dT u by ring]
  calc
    _ = ((1 - S.mu (T u) (T v)) * S.zeta (T u) (T v) ^ 2 * dT u) *
        dT u / ((2 * S.nu (T u) (T v)) * dT u) := by ring
    _ = _ := by rw [mul_div_mul_right _ _ hu]; ring

/-- The transformed expansion sum includes a derivative-mismatch term.
Paper `e1a0fd5`, `eq:continuation-null-gauge`, lines 1390–1394.
This term matters when passing to the regular axis. -/
theorem pullback_expansion_sum (S : SSFields) (T dT : ℝ → ℝ) (u v : ℝ) :
    (S.pullback T dT).nu u v + (S.pullback T dT).lam u v =
      (S.nu (T u) (T v) + S.lam (T u) (T v)) * dT u +
        S.lam (T u) (T v) * (dT v - dT u) := by
  simp only [pullback]
  ring

/-- Pointwise logarithmic incoming expansion law. Paper `e1a0fd5`,
`eq:terminal-expansion-gauge`, lines 1435–1438. -/
theorem pullback_log_neg_nu (S : SSFields) (T dT : ℝ → ℝ) (u v : ℝ)
    (hu : dT u ≠ 0) (hnu : S.nu (T u) (T v) ≠ 0) :
    Real.log (-(S.pullback T dT).nu u v) =
      Real.log (dT u) + Real.log (-S.nu (T u) (T v)) := by
  change Real.log (-(S.nu (T u) (T v) * dT u)) = _
  rw [← neg_mul, Real.log_mul (neg_ne_zero.mpr hnu) hu, add_comm]

end SSFields

/-- An injective common coordinate map preserves and reflects the diagonal.
Paper `e1a0fd5`, `eq:continuation-null-gauge`, line 1395. -/
theorem reparam_axis_iff {T : ℝ → ℝ} (hT : Function.Injective T) (u v : ℝ) :
    T u = T v ↔ u = v := hT.eq_iff

end AcExtensionPrinciple

end
