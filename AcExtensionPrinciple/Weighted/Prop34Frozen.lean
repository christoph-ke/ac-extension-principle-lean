module

public import AcExtensionPrinciple.Renormalized.ClassSplitting
public import AcExtensionPrinciple.GeometricBounds.Kappa

/-!
# The incoming integral formula for the frozen equation

Helpers, paper `e1a0fd5`, `eq:frozen-linear-transport`,
`equations.tex` lines 1257–1276. This construction uses the actual κ
integrating factor. Ray integrability is explicit; passing from finite
source energy to almost-everywhere ray integrability is a separate step.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory

/-- The literal incoming solution formula with initial datum `J₀`.
Paper `e1a0fd5`, `eq:frozen-linear-transport`, lines 1257–1276.
No completion of a normed space is used in this definition. -/
@[expose] noncomputable def weightedFrozenSolution
    (S : SSFields) (u₀ : ℝ) (J₀ : ℝ → ℝ) (F : ℝ × ℝ → ℝ)
    (p : ℝ × ℝ) : ℝ :=
  (S.kappa u₀ p.2 * J₀ p.2 + ∫ s in u₀..p.1,
    3 * S.kappa s p.2 * S.nu s p.2 * S.dvphi s p.2 * F (s, p.2)) /
      S.kappa p.1 p.2

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- The frozen solution takes its prescribed initial value off the axis.
Paper `e1a0fd5`, `eq:frozen-linear-transport`, lines 1260–1263. -/
theorem weightedFrozenSolution_initial {u₀ v : ℝ}
    (hi : ui ≤ u₀) (hu₀ : u₀ < 0) (huv : u₀ < v) (hv : v ≤ 0)
    (J₀ : ℝ → ℝ) (F : ℝ × ℝ → ℝ) :
    weightedFrozenSolution S u₀ J₀ F (u₀, v) = J₀ v := by
  simp only [weightedFrozenSolution, intervalIntegral.integral_same, add_zero]
  exact mul_div_cancel_left₀ _ (h.kappa_pos (p := (u₀, v)) ⟨hi, hu₀, huv.le, hv⟩).ne'

/-- A locally integrable source gives the frozen solution's incoming AC and equation. Paper
`e1a0fd5`, `eq:frozen-linear-transport`, lines 1260–1276. For finite source energy, the ray premise
is supplied almost everywhere by `weightedFrozenSolution_ac_ae_of_finite_source` in
`Weighted/Prop34Source.lean`, using Tonelli and positive geometric weights away from the axis. -/
theorem weightedFrozenSolution_ac_and_transport {u₀ b v : ℝ}
    (hi : ui ≤ u₀) (hab : u₀ ≤ b) (hb : b < 0) (hbv : b < v) (hv : v ≤ 0)
    (J₀ : ℝ → ℝ) (F : ℝ × ℝ → ℝ)
    (hF : IntervalIntegrable (fun s => F (s, v)) volume u₀ b) :
    AbsolutelyContinuousOnInterval (fun s => weightedFrozenSolution S u₀ J₀ F (s, v))
      u₀ b ∧
    (∀ᵐ x, x ∈ Ioo u₀ b → HasDerivAt
      (fun s => weightedFrozenSolution S u₀ J₀ F (s, v))
      (S.incomingFlux x v * weightedFrozenSolution S u₀ J₀ F (x, v) +
        3 * S.nu x v * S.dvphi x v * F (x, v)) x) := by
  let G := fun s => 3 * S.kappa s v * S.nu s v * S.dvphi s v * F (s, v)
  have hk := h.kappa_ac_in hab hi hb hbv hv
  have hn : ContinuousOn (fun s => S.nu s v) (uIcc u₀ b) := by
    rw [uIcc_of_le hab]
    exact continuous_in h.regularCenter.continuous_nu (inSeg_subset_triangle hi hb hbv.le hv)
  have hp := (h.incoming_components_ac hab hi hb hbv hv).2.2.2
  have hG : IntervalIntegrable G volume u₀ b :=
    hF.continuousOn_mul (((hk.continuousOn.const_mul 3).mul hn).mul
      hp.continuousOn)
  have hI : AbsolutelyContinuousOnInterval (fun t => ∫ s in u₀..t, G s) u₀ b :=
    hG.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hconst : AbsolutelyContinuousOnInterval
      (fun _ : ℝ => S.kappa u₀ v * J₀ v) u₀ b :=
    (LipschitzWith.const _).lipschitzOnWith.absolutelyContinuousOnInterval
  have hnum := hconst.add hI
  have hkpos (x : ℝ) (hx : x ∈ uIcc u₀ b) : 0 < S.kappa x v := by
    rw [uIcc_of_le hab] at hx
    exact h.kappa_pos (p := (x, v))
      ⟨hi.trans hx.1, hx.2.trans_lt hb, (hx.2.trans_lt hbv).le, hv⟩
  refine ⟨?_, ?_⟩
  · simpa only [weightedFrozenSolution, div_eq_mul_inv, G, Pi.add_apply] using
      hnum.fun_mul (positive_ac_inv hk hkpos)
  · filter_upwards [h.kappa_derivative_ae hab hi hb hbv hv,
      hG.ae_hasDerivAt_integral] with x hkx hIx hx
    have hx' : x ∈ uIcc u₀ b := by rw [uIcc_of_le hab]; exact ⟨hx.1.le, hx.2.le⟩
    have hdI := hIx hx' u₀ (by simp)
    have hd := ((hasDerivAt_const x (S.kappa u₀ v * J₀ v)).add hdI).div
      (hkx hx) (hkpos x hx').ne'
    convert hd using 1
    · rfl
    · dsimp [weightedFrozenSolution, G]
      field_simp [(hkpos x hx').ne']
      ring

end StandingFull

end AcExtensionPrinciple

end
