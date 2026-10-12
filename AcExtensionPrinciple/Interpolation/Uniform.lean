module

public import AcExtensionPrinciple.Interpolation.Oscillation
public import AcExtensionPrinciple.Interpolation.RadialMass

/-!
# Lemma 2.3 at the solution-class level

Paper `e1a0fd5`, `lem:ac-interpolation`, `eq:ac-interpolation`,
`equations.tex` lines 606–659. All analytic and geometric inputs to the
abstract radial interpolation theorem are discharged from StandingFull.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Lemma 2.3, uniform over the whole past triangle wherever r > 0.
Paper `e1a0fd5`, `lem:ac-interpolation`, lines 606–659. -/
theorem ac_interpolation :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ pastTriangle ui, 0 < S.r p.1 p.2 →
      |outgoingAmplitude S p.1 p.2| ^ 3 ≤
        C * (S.mu p.1 p.2 + initialACTail ui S p.1 ^ 3) := by
  obtain ⟨M, hscalar⟩ := h.uniform_scalar_bound
  have hM : 0 ≤ M := by
    have hb := hscalar (ui, ui) ⟨le_rfl, h.initial_negative, le_rfl, h.initial_negative.le⟩
    exact (add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)).trans hb
  have hA : ∀ p ∈ pastTriangle ui, |outgoingAmplitude S p.1 p.2| ≤ M := by
    intro p hp
    have hb := hscalar p hp
    dsimp [outgoingAmplitude]
    linarith [abs_nonneg (S.dvpsi p.1 p.2 / S.lam p.1 p.2), abs_nonneg (S.phi p.1 p.2)]
  obtain ⟨D, hD, hrem⟩ := h.exists_radial_remainder_bound
  let E := Real.exp (Bstar ui S)
  let C1 := max E (D + M)
  let g := initialGap ui S * Real.exp (-Bstar ui S)
  have hg : 0 < g := mul_pos h.initialGap_pos (Real.exp_pos _)
  have hC1 : 0 ≤ C1 := (Real.exp_pos _).le.trans (le_max_left _ _)
  let C := radialInterpolationConstant C1 M (g / 2)
  have hC : 0 < C := by
    apply lt_of_lt_of_le _ (le_max_right _ _)
    exact div_pos (by norm_num) (mul_pos (by linarith)
      (interpolationWidthCoefficient_bounds hC1 hM).1)
  refine ⟨C, hC, ?_⟩
  intro p hp hr
  let u := p.1
  let v := p.2
  have huv : u < v := by
    apply lt_of_le_of_ne hp.2.2.1
    intro he
    change u = v at he
    have hz := (h.regularCenter.localBV.axis_values u
      ⟨hp.1, hp.2.1, le_rfl, hp.2.1.le⟩).1
    have heq : S.r p.1 p.2 = 0 := by change S.r u v = 0; rw [← he, hz]
    linarith
  let r := S.r u v
  let label := coneRadiusLabel S u
  let A := fun t => outgoingAmplitude S u (label t)
  let m := fun t => S.m u (label t)
  have hv : v ∈ Icc u 0 := ⟨hp.2.2.1, hp.2.2.2⟩
  have hrR : r ≤ S.r u 0 := (h.radius_strictMono hp.1 hp.2.1).monotoneOn
    hv ⟨hp.2.1.le, le_rfl⟩ hp.2.2.2
  have hrI : r ∈ Icc 0 (S.r u 0) := ⟨hr.le, hrR⟩
  have hrad (t : ℝ) (ht : t ∈ Icc (r / 2) r) : t ∈ Icc 0 (S.r u 0) :=
    ⟨(by linarith [ht.1]), ht.2.trans hrR⟩
  have hlabelr : label r = v := h.coneRadiusLabel_radius hp.1 hp.2.1 hv
  have hAc : ContinuousOn A (Icc (r / 2) r) :=
    ((h.outgoingAmplitude_continuous_out hp.1 hp.2.1).comp
      (h.coneRadiusLabel_lipschitz hp.1 hp.2.1).continuousOn
      (fun t ht => (h.coneRadiusLabel_spec hp.1 hp.2.1 ht).1)).mono hrad
  have hAi := (hAc.pow 2).intervalIntegrable_of_Icc (μ := volume)
    (show r / 2 ≤ r by linarith)
  have hAr : ∀ t ∈ Icc (r / 2) r, |A t| ≤ M := by
    intro t ht
    have hs := h.coneRadiusLabel_spec hp.1 hp.2.1 (hrad t ht)
    exact hA (u, label t) ⟨hp.1, hp.2.1, hs.1⟩
  have hosc : ∀ t ∈ Icc (r / 2) r,
      |A t - A r| ≤ C1 * (initialACTail ui S u + Real.log (r / t)) := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hs := h.coneRadiusLabel_spec hp.1 hp.2.1 (hrad t ht)
    have hlt := h.coneRadiusLabel_offAxis hp.1 hp.2.1 (hrad t ht) ht0
    have hle : label t ≤ v := by
      rw [← hlabelr]
      exact h.coneRadiusLabel_monotone hp.1 hp.2.1 (hrad t ht) hrI ht.2
    have ho := h.outgoingAmplitude_oscillation_of_bounds hM hD.le hA hrem
      hp.1 hp.2.1 hlt hle hp.2.2.2
    change |A t - outgoingAmplitude S u v| ≤ _ at ho
    rw [hs.2] at ho
    have hlog : 0 ≤ Real.log (r / t) :=
      Real.log_nonneg ((le_div_iff₀ ht0).mpr (by simpa only [one_mul] using ht.2))
    have hw : 0 ≤ initialACTail ui S u := initialACTail_nonneg hp.2.1.le
    have he := mul_le_mul_of_nonneg_right (le_max_left E (D + M)) hw
    have hd := mul_le_mul_of_nonneg_right (le_max_right E (D + M)) hlog
    dsimp only [A]
    rw [hlabelr]
    exact ho.trans (by dsimp only [C1, E] at he hd ⊢; nlinarith only [he, hd])
  have hm0 : ∀ t ∈ Icc (r / 2) r, 0 ≤ m t := by
    intro t ht
    have hs := h.coneRadiusLabel_spec hp.1 hp.2.1 (hrad t ht)
    exact h.interpolation_mass_nonneg ⟨hp.1, hp.2.1, hs.1⟩
  have hmass : ∀ t ∈ Icc (r / 2) r,
      (g / 2) * (∫ s in t..r, A s ^ 2) ≤ m r - m t := by
    intro t ht
    exact h.radial_mass_lower_bound hp.1 hp.2.1 (hrad t ht) hrI
      (by linarith [ht.1]) ht.2 (fun _ hp' => h.mass_gap_lower hp')
  have hi := radial_amplitude_interpolation hr (initialACTail_nonneg hp.2.1.le)
    hC1 hM (by linarith : 0 < g / 2) hAr hosc hAi hm0 hmass
  change |A r| ^ 3 ≤ C * (massRatio r (m r) + initialACTail ui S u ^ 3) at hi
  dsimp only [A, m] at hi
  rw [hlabelr] at hi
  exact hi

/-- Lemma 2.3 in the paper's original scalar-derivative notation.
Paper `e1a0fd5`, `lem:ac-interpolation`, `eq:ac-interpolation`, lines 606–659. -/
theorem ac_interpolation_scalar_derivative :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ pastTriangle ui, 0 < S.r p.1 p.2 →
      |S.r p.1 p.2 / S.lam p.1 p.2 * S.dvphi p.1 p.2| ^ 3 ≤
        C * (S.mu p.1 p.2 + initialACTail ui S p.1 ^ 3) := by
  obtain ⟨C, hC, hbound⟩ := h.ac_interpolation
  refine ⟨C, hC, ?_⟩
  intro p hp hr
  have hl := h.lam_pos hp
  have he : S.r p.1 p.2 / S.lam p.1 p.2 * S.dvphi p.1 p.2 =
      outgoingAmplitude S p.1 p.2 := by
    dsimp [SSFields.dvphi, outgoingAmplitude]
    field_simp [hr.ne', hl.ne']
  rw [he]
  exact hbound p hp hr

end StandingFull

end AcExtensionPrinciple

end
