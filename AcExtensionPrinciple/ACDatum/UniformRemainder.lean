module

public import AcExtensionPrinciple.ACDatum.RadialTransport
public import AcExtensionPrinciple.GeometricBounds.Kappa

/-!
# Uniform bound for the identified derivative remainder

Paper `e1a0fd5`, `eq:rough-derivative-decomposition` and
`eq:derivative-remainder-bound`, lines 572–581 and 603.
The geometric gap is discharged here. The only remaining helper premise
is the uniform scalar bound of Lemma 2.1.
The scalar premise is supplied by `StandingFull.uniform_scalar_bound` in
`ScalarBound/Uniform.lean`, as consumed in `Integration/DatumRepresentative.lean`.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Uniform control of the source remainder using the proved mass gap and
the explicit Lemma 2.1 scalar bound. This helper takes the scalar bound as an explicit premise.
Paper `e1a0fd5`, `eq:derivative-remainder-bound`, lines 578–581. -/
theorem radialDatumRemainderIntegral_bound_of_scalar {M : ℝ}
    (hscalar : ∀ p ∈ pastTriangle ui,
      |S.theta p.1 p.2 / S.lam p.1 p.2| +
        |S.dvpsi p.1 p.2 / S.lam p.1 p.2| + |S.phi p.1 p.2| ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ u v, ui ≤ u → u < 0 → u < v → v ≤ 0 →
      |radialDatumRemainderIntegral ui S u v| ≤
        C * (∫ s in ui..u, -S.nu s v / S.r s v ^ 2) ∧
      C * (∫ s in ui..u, -S.nu s v / S.r s v ^ 2) ≤ C / S.r u v := by
  have hM : 0 ≤ M := by
    have hp : (ui, ui) ∈ pastTriangle ui :=
      ⟨le_rfl, h.initial_negative, le_rfl, h.initial_negative.le⟩
    have hb := hscalar (ui, ui) hp
    exact (add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)).trans hb
  exact h.radialDatumRemainderIntegral_bound_of_geometric
    (mul_pos h.initialGap_pos (Real.exp_pos _)) hM
    (fun _p hp => h.mass_gap_lower hp) hscalar

/-- Derivative identification holds for almost every incoming label on all proper segments
simultaneously. Paper `e1a0fd5`, `eq:rough-derivative-decomposition`, lines 572–574. -/
theorem radialDatumDerivative_ae_decomposition :
    ∀ᵐ v, v ∈ Ioo ui 0 → ∀ u, ui ≤ u → u < 0 → u < v →
      radialDatumDerivative S u v = deriv (S.dvpsi ui) v / S.lam u v ^ 2 +
        radialDatumRemainderIntegral ui S u v := by
  filter_upwards [h.radialDatumDerivative_ae_incoming_transport] with v hv
  intro hvI u hu hu0 huv
  exact (hv hvI u hu hu0 huv).2.2.2

end StandingFull

end AcExtensionPrinciple

end
