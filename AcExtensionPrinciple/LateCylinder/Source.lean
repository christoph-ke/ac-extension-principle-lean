module

public import AcExtensionPrinciple.Interpolation.Uniform

/-!
# Small source in a low-mass exterior

Paper `e1a0fd5`, `eq:small-exterior-source`, equations.tex lines 800–807.
The interpolation and scalar constants are uniform in the small parameter.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory

/-- Cubic interpolation and a bounded amplitude control the nonlinear
source. Paper `e1a0fd5`, `eq:small-exterior-source`, lines 800–807. -/
theorem small_cubic_source {A mu omega eps C M : ℝ}
    (heps : 0 < eps) (heps1 : eps ≤ 1) (hmu0 : 0 ≤ mu) (hmu : mu ≤ eps)
    (hw0 : 0 ≤ omega) (hw : omega ≤ eps) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hA : |A| ≤ M) (hinterp : |A| ^ 3 ≤ C * (mu + omega ^ 3)) :
    |A * (A ^ 2 - 3 * mu)| ≤ (2 * C + 3 * M) * eps := by
  have hw1 : omega ≤ 1 := hw.trans heps1
  have hw3 : omega ^ 3 ≤ eps := by
    have hs : omega ^ 2 ≤ 1 := by nlinarith
    have hc := mul_le_mul_of_nonneg_left hs hw0
    nlinarith
  have hcube : |A| ^ 3 ≤ 2 * C * eps := by
    have hh := mul_le_mul_of_nonneg_left (add_le_add hmu hw3) hC
    nlinarith only [hinterp, hh]
  calc
    _ = |A| * |A ^ 2 - 3 * mu| := abs_mul _ _
    _ ≤ |A| * (A ^ 2 + 3 * mu) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      have hh := abs_sub (A ^ 2) (3 * mu)
      rw [abs_pow, sq_abs, abs_of_nonneg
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hmu0)] at hh
      exact hh
    _ = |A| ^ 3 + 3 * |A| * mu := by rw [← sq_abs A]; ring
    _ ≤ (2 * C + 3 * M) * eps := by
      have hh := mul_le_mul hA hmu hmu0 hM
      nlinarith only [hh, hcube]

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The initial AC tail decreases with the outgoing label. Paper `e1a0fd5`,
`eq:initial-ac-tail`, lines 537–543, used at lines 800–807. -/
theorem initialACTail_antitone {u0 u : ℝ} (hu0 : ui ≤ u0) (hu : u0 ≤ u) (hu1 : u ≤ 0) :
    initialACTail ui S u ≤ initialACTail ui S u0 := by
  apply intervalIntegral.integral_mono_interval hu hu1 le_rfl
    (Eventually.of_forall (fun _ => abs_nonneg _))
  exact h.initial_second_derivative_integrable.abs.mono_set
    (by rw [uIcc_of_le (hu.trans hu1), uIcc_of_le h.initial_negative.le]
        exact Icc_subset_Icc hu0 le_rfl)

/-- Uniform smallness of the cubic source whenever μ and the earlier AC
tail are at most ε. Paper `e1a0fd5`,
`eq:small-exterior-source`, lines 800–807. -/
theorem exists_small_exterior_source :
    ∃ B : ℝ, 0 < B ∧ ∀ eps u0 u v, 0 < eps → eps ≤ 1 → ui ≤ u0 → u0 ≤ u →
      (u, v) ∈ pastTriangle ui → 0 < S.r u v → S.mu u v ≤ eps →
      initialACTail ui S u0 ≤ eps →
      |outgoingAmplitude S u v * (outgoingAmplitude S u v ^ 2 - 3 * S.mu u v)| ≤ B * eps := by
  obtain ⟨C, hC, hinterp⟩ := h.ac_interpolation
  obtain ⟨M, hscalar⟩ := h.uniform_scalar_bound
  have hM : 0 ≤ M := by
    have hh := hscalar (ui, ui) ⟨le_rfl, h.initial_negative, le_rfl, h.initial_negative.le⟩
    exact (add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)).trans hh
  refine ⟨2 * C + 3 * M, by positivity, ?_⟩
  intro eps u0 u v heps heps1 hu0 hu hp hr hmu hw
  apply small_cubic_source heps heps1 (h.mu_bounds hp).1 hmu
    (initialACTail_nonneg hp.2.1.le)
    ((h.initialACTail_antitone hu0 hu hp.2.1.le).trans hw) hC.le hM
  · have hh := hscalar (u, v) hp
    dsimp [outgoingAmplitude]
    linarith [abs_nonneg (S.dvpsi u v / S.lam u v), abs_nonneg (S.phi u v)]
  · exact hinterp (u, v) hp hr

end StandingFull

end AcExtensionPrinciple

end
