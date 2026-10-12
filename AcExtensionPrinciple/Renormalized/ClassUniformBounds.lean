module

public import AcExtensionPrinciple.ScalarBound.Uniform
public import AcExtensionPrinciple.GeometricBounds.IncomingFlux
public import AcExtensionPrinciple.Renormalized.ClassConeBounds
public import AcExtensionPrinciple.Renormalized.ClassRemainder

/-!
# Uniform Section 3 coefficients from the standing assumptions

Paper `e1a0fd5`, `equations.tex` lines 1071–1124.
The existing G0/G1/G2/G6 results discharge the geometric premises of
Lemma 2.1 before the Section 3 coefficients are bounded.
-/

public section

namespace AcExtensionPrinciple.StandingFull

open Set MeasureTheory
open scoped ENNReal

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Unconditional scalar bound obtained by discharging G0/G2/G6.
Paper `e1a0fd5`, `eq:uniform-scalar-bound`, lines 524–535 and 1071. -/
theorem section3_uniform_scalar_bound :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ pastTriangle ui,
      |S.r p.1 p.2 / S.lam p.1 p.2 * S.dvphi p.1 p.2| ≤ M ∧ |S.phi p.1 p.2| ≤ M := by
  obtain ⟨C, hC⟩ := h.uniform_scalar_bound
  have hC0 : 0 ≤ C := by
    have hm := hC (ui, ui) ⟨le_rfl, h.initial_negative, le_rfl, h.initial_negative.le⟩
    linarith [abs_nonneg (S.theta ui ui / S.lam ui ui), abs_nonneg (S.dvpsi ui ui / S.lam ui ui),
      abs_nonneg (S.phi ui ui)]
  refine ⟨C, hC0, fun p hp => ?_⟩
  have hm := hC p hp
  have hphi : |S.phi p.1 p.2| ≤ C := by
    linarith [abs_nonneg (S.theta p.1 p.2 / S.lam p.1 p.2),
      abs_nonneg (S.dvpsi p.1 p.2 / S.lam p.1 p.2)]
  refine ⟨?_, hphi⟩
  rcases hp.2.2.1.eq_or_lt with he | huv
  · have hr : S.r p.1 p.2 = 0 := by
      rw [← he]
      exact (h.regularCenter.localBV.axis_values p.1
        ⟨hp.1, hp.2.1, le_rfl, hp.2.1.le⟩).1
    simpa only [hr, zero_div, zero_mul, abs_zero] using hC0
  · have he : S.r p.1 p.2 / S.lam p.1 p.2 * S.dvphi p.1 p.2 =
        S.theta p.1 p.2 / S.lam p.1 p.2 := by
      unfold SSFields.dvphi
      field_simp [ne_of_gt (h.r_pos hp huv)]
    rw [he]
    linarith [abs_nonneg (S.dvpsi p.1 p.2 / S.lam p.1 p.2), abs_nonneg (S.phi p.1 p.2)]

/-- One uniform bound controls both normalized scalar amplitudes and the
interaction. Paper `e1a0fd5`, lines 1071–1073 and 1120. -/
theorem section3_uniform_coefficients :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ pastTriangle ui,
      |S.r p.1 p.2 / S.lam p.1 p.2 * S.dvphi p.1 p.2| ≤ M ∧
      |S.r p.1 p.2 / S.nu p.1 p.2 * S.duphi p.1 p.2| ≤ 2 * M ∧
      |S.renormalizedInteraction p.1 p.2| ≤ 1 + 2 * M ^ 2 := by
  obtain ⟨M, hM0, hM⟩ := h.section3_uniform_scalar_bound
  have hB := h.incoming_amplitude_bound_of_scalar_bound (fun p hp => (hM p hp).2)
  refine ⟨M, hM0, fun p hp => ⟨(hM p hp).1, hB p hp, ?_⟩⟩
  have he := interaction_abs_bound (h.mu_bounds hp).1 (h.mu_bounds hp).2.le
    (hM p hp).1 (hB p hp)
  change |S.mu p.1 p.2 + (1 - S.mu p.1 p.2) *
    (S.r p.1 p.2 / S.lam p.1 p.2 * S.dvphi p.1 p.2) *
    (S.r p.1 p.2 / S.nu p.1 p.2 * S.duphi p.1 p.2)| ≤ _
  convert he using 1
  ring

/-- Initial domination now has no geometric premises.
Paper `e1a0fd5`, `eq:renormalized-initial-domination`, lines 1092–1097. -/
theorem section3_initial_domination (q : ℝ → ℝ → ℝ) :
    ∀ p ∈ pastTriangle ui, |S.renormalizedInitial q ui p.1 p.2| ≤
      ((1 / initialGap ui S) / Real.exp (-Bstar ui S)) * |S.renormalizedDerivative q ui p.2| :=
  h.renormalizedInitial_domination_of_geometric q h.initialGap_pos (fun _ hp => h.kappa_bounds hp)

end AcExtensionPrinciple.StandingFull

end
