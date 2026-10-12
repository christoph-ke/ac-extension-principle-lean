module

public import AcExtensionPrinciple.Reduced.Quantities
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Tactic

/-!
# Radial AC interpolation with explicit constants

Helpers for paper `e1a0fd5`, `equations.tex` lines 618–659
(`eq:ac-interpolation`). The premises include positive c₃, nonnegative C₁,C₂,
and integrability of A², all provided by the paper's cone regularity and geometry.
-/

public section

namespace AcExtensionPrinciple

open Set MeasureTheory

/-- Explicit coefficient in `d=c r |A(r)|`; paper `e1a0fd5`,
`equations.tex` line 637 (`eq:interpolation-interval-width`). -/
@[expose] noncomputable def interpolationWidthCoefficient (C1 C2 : ℝ) : ℝ :=
  min (1 / (2 * (C2 + 1))) (1 / (8 * (C1 + 1)))

/-- Explicit interpolation constant; paper `e1a0fd5`, `equations.tex`
lines 618–659 (`eq:ac-interpolation`). -/
@[expose] noncomputable def radialInterpolationConstant (C1 C2 c3 : ℝ) : ℝ :=
  max (64 * C1 ^ 3) (2 / (c3 * interpolationWidthCoefficient C1 C2))

/-- The width coefficient is positive and small enough for both the half-radius
and amplitude-persistence bounds; paper `e1a0fd5`, `equations.tex` lines 637–645. -/
theorem interpolationWidthCoefficient_bounds {C1 C2 : ℝ} (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) :
    0 < interpolationWidthCoefficient C1 C2 ∧
    2 * interpolationWidthCoefficient C1 C2 * C2 ≤ 1 ∧
    8 * C1 * interpolationWidthCoefficient C1 C2 ≤ 1 := by
  let c := interpolationWidthCoefficient C1 C2
  have hc : 0 < c := by dsimp [c, interpolationWidthCoefficient]; positivity
  have h2 : c * (2 * (C2 + 1)) ≤ 1 := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * (C2 + 1))).mp
    exact min_le_left _ _
  have h8 : c * (8 * (C1 + 1)) ≤ 1 := by
    apply (le_div_iff₀ (by positivity : 0 < 8 * (C1 + 1))).mp
    exact min_le_right _ _
  exact ⟨hc, by nlinarith, by nlinarith⟩

/-- The logarithmic oscillation is linear on the last half-radius interval;
paper `e1a0fd5`, `equations.tex` lines 628–645 (`eq:radial-amplitude-oscillation`). -/
theorem log_radius_gap_le {r d t : ℝ} (hr : 0 < r) (hd : 0 ≤ d)
    (ht : r / 2 ≤ t) (hgap : r - t ≤ d) : Real.log (r / t) ≤ 2 * d / r := by
  have ht0 : 0 < t := by linarith
  have hlog := Real.log_le_sub_one_of_pos (div_pos hr ht0)
  have heq : r / t - 1 = (r - t) / t := by field_simp
  rw [heq] at hlog
  apply hlog.trans
  apply (div_le_div_iff₀ ht0 hr).mpr
  have hgapmul := mul_le_mul_of_nonneg_right hgap hr.le
  have htmul := mul_le_mul_of_nonneg_left ht hd
  nlinarith

/-- Large amplitudes persist on the interval of width `c r |A(r)|`;
paper `e1a0fd5`, `equations.tex` lines 635–645 (`eq:amplitude-persistence`). -/
theorem amplitude_persistence_of_log_oscillation {A : ℝ → ℝ} {r omega C1 c : ℝ}
    (hr : 0 < r) (hC1 : 0 ≤ C1) (hc : 0 ≤ c) (hsmall : 8 * C1 * c ≤ 1)
    (hwidth : c * r * |A r| ≤ r / 2) (hbig : 4 * C1 * omega < |A r|)
    (hosc : ∀ t ∈ Icc (r / 2) r,
      |A t - A r| ≤ C1 * (omega + Real.log (r / t))) :
    ∀ t ∈ Icc (r - c * r * |A r|) r, |A r| / 2 ≤ |A t| := by
  intro t ht
  have hthalf : r / 2 ≤ t := by linarith [ht.1]
  have hd : 0 ≤ c * r * |A r| := by positivity
  have hlog := log_radius_gap_le hr hd hthalf
    (by linarith [ht.1] : r - t ≤ c * r * |A r|)
  have heq : 2 * (c * r * |A r|) / r = 2 * c * |A r| := by field_simp
  rw [heq] at hlog
  have hv := (hosc t ⟨hthalf, ht.2⟩).trans
    (mul_le_mul_of_nonneg_left (by linarith :
      omega + Real.log (r / t) ≤ omega + 2 * c * |A r|) hC1)
  have hscale := mul_le_mul_of_nonneg_right hsmall (abs_nonneg (A r))
  have hrev : |A r| ≤ |A t| + |A t - A r| := by
    calc
      |A r| = |A t - (A t - A r)| := by congr 1; ring
      _ ≤ _ := abs_sub _ _
  nlinarith only [hv, hscale, hbig, hrev]

/-- Integrating persistence produces the cubic mass lower bound;
paper `e1a0fd5`, `equations.tex` lines 647–657 (`eq:interpolation-mass-lower-bound`). -/
theorem mass_lower_bound_of_amplitude_persistence {A m : ℝ → ℝ} {r c c3 : ℝ}
    (hr : 0 < r) (hc : 0 ≤ c) (hc3 : 0 ≤ c3)
    (hwidth : c * r * |A r| ≤ r / 2)
    (hAi : IntervalIntegrable (fun s ↦ A s ^ 2) volume (r / 2) r)
    (hm0 : ∀ t ∈ Icc (r / 2) r, 0 ≤ m t)
    (hmass : ∀ t ∈ Icc (r / 2) r,
      c3 * (∫ s in t..r, A s ^ 2) ≤ m r - m t)
    (hpersist : ∀ t ∈ Icc (r - c * r * |A r|) r, |A r| / 2 ≤ |A t|) :
    c3 * c * r * |A r| ^ 3 ≤ 4 * m r := by
  let d := c * r * |A r|
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hlow : r / 2 ≤ r - d := by dsimp [d]; linarith
  have hle : r - d ≤ r := by linarith
  have hsub : uIcc (r - d) r ⊆ uIcc (r / 2) r := by
    rw [uIcc_of_le hle, uIcc_of_le (by linarith : r / 2 ≤ r)]
    exact Icc_subset_Icc hlow le_rfl
  have hi := hAi.mono_set hsub
  have hI : d * (|A r| ^ 2 / 4) ≤ ∫ s in (r - d)..r, A s ^ 2 := by
    have hh : (∫ _s in (r - d)..r, |A r| ^ 2 / 4) ≤
        ∫ s in (r - d)..r, A s ^ 2 := by
      apply intervalIntegral.integral_mono_on hle intervalIntegrable_const hi
      intro t ht
      have hp := hpersist t ht
      nlinarith [sq_abs (A t), abs_nonneg (A t), abs_nonneg (A r)]
    simpa [intervalIntegral.integral_const, smul_eq_mul, mul_div_assoc] using hh
  have hmass0 := hmass (r - d) ⟨hlow, hle⟩
  have hmnonneg := hm0 (r - d) ⟨hlow, hle⟩
  have hscale := mul_le_mul_of_nonneg_left hI hc3
  dsimp [d] at hscale
  nlinarith only [hmass0, hmnonneg, hscale]

/-- Explicit radial interpolation, with constants depending only on C₁,C₂,c₃;
paper `e1a0fd5`, `equations.tex` lines 618–659 (`eq:ac-interpolation`). The
integrability premise follows from continuity of A on the compact cone annulus;
c₃>0 is supplied by the uniform mass gap in `eq:mass-gap-and-nu-bound`. -/
theorem radial_amplitude_interpolation {A m : ℝ → ℝ} {r omega C1 C2 c3 : ℝ}
    (hr : 0 < r) (homega : 0 ≤ omega) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hc3 : 0 < c3)
    (hA : ∀ t ∈ Icc (r / 2) r, |A t| ≤ C2)
    (hosc : ∀ t ∈ Icc (r / 2) r,
      |A t - A r| ≤ C1 * (omega + Real.log (r / t)))
    (hAi : IntervalIntegrable (fun s ↦ A s ^ 2) volume (r / 2) r)
    (hm0 : ∀ t ∈ Icc (r / 2) r, 0 ≤ m t)
    (hmass : ∀ t ∈ Icc (r / 2) r,
      c3 * (∫ s in t..r, A s ^ 2) ≤ m r - m t) :
    |A r| ^ 3 ≤ radialInterpolationConstant C1 C2 c3 * (massRatio r (m r) + omega ^ 3) := by
  let c := interpolationWidthCoefficient C1 C2
  let C := radialInterpolationConstant C1 C2 c3
  have hcb := interpolationWidthCoefficient_bounds hC1 hC2
  have hc : 0 < c := hcb.1
  have hrmem : r ∈ Icc (r / 2) r := ⟨by linarith, le_rfl⟩
  have hmu : 0 ≤ massRatio r (m r) := by
    unfold massRatio
    exact div_nonneg (by linarith [hm0 r hrmem]) hr.le
  have hCsmall : 64 * C1 ^ 3 ≤ C := le_max_left _ _
  have hClarge : 2 / (c3 * c) ≤ C := le_max_right _ _
  have hC : 0 ≤ C := (div_nonneg (by norm_num) (mul_pos hc3 hc).le).trans hClarge
  by_cases hsmall : |A r| ≤ 4 * C1 * omega
  · have hcube : |A r| ^ 3 ≤ (4 * C1 * omega) ^ 3 := by gcongr
    calc
      |A r| ^ 3 ≤ 64 * C1 ^ 3 * omega ^ 3 := by nlinarith only [hcube]
      _ ≤ C * omega ^ 3 := mul_le_mul_of_nonneg_right hCsmall (by positivity)
      _ ≤ C * (massRatio r (m r) + omega ^ 3) := by nlinarith [mul_nonneg hC hmu]
  · have hwidth : c * r * |A r| ≤ r / 2 := by
      have hAr := hA r hrmem
      have hmul := mul_le_mul_of_nonneg_left hAr (show 0 ≤ c * r by positivity)
      have hmul2 := mul_le_mul_of_nonneg_right hcb.2.1 hr.le
      nlinarith only [hmul, hmul2]
    have hpersist := amplitude_persistence_of_log_oscillation hr hC1 hc.le hcb.2.2
      hwidth (not_le.mp hsmall) hosc
    have hlower := mass_lower_bound_of_amplitude_persistence hr hc.le hc3.le
      hwidth hAi hm0 hmass hpersist
    have hden : 0 < c3 * c * r := by positivity
    have hquot : |A r| ^ 3 ≤ 4 * m r / (c3 * c * r) :=
      (le_div_iff₀ hden).mpr (by nlinarith only [hlower])
    have heq : 4 * m r / (c3 * c * r) = 2 / (c3 * c) * massRatio r (m r) := by
      unfold massRatio
      field_simp
      ring
    rw [heq] at hquot
    exact hquot.trans ((mul_le_mul_of_nonneg_right hClarge hmu).trans
      (by nlinarith [mul_nonneg hC (show 0 ≤ omega ^ 3 by positivity)]))

end AcExtensionPrinciple

end
