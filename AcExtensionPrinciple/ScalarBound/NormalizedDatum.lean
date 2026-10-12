module

public import AcExtensionPrinciple.ScalarBound.Calculus

/-!
# Bounds for the normalized datum after the amplitude bound

Paper commit `e1a0fd5`, `equations.tex`
lines 524–534, `eq:scalar-bound-normalized-datum`. These component
helpers take the θ bound explicitly; the strip argument must discharge it.
-/

public section

namespace AcExtensionPrinciple.StandingFull

open Set MeasureTheory
open scoped ENNReal

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Any proper partial blueshift integral, including v = 0, has the same
uniform bound. Paper `e1a0fd5`, lines 524–532, `eq:terminal-blueshift-bound`. -/
theorem partial_blueshift_le_terminal {u v : ℝ}
    (hp : (u, v) ∈ pastTriangle ui) (huv : u < v) :
    (∫ s in ui..u, -(S.gamma s v * S.varkappa s v)) ≤ Bstar ui S := by
  have hl := h.log_lam_primitive hp.1 le_rfl hp.2.1 huv hp.2.2.2
  have hi := hl.1.neg
  change IntervalIntegrable (fun s => -(S.gamma s v * S.varkappa s v)) volume ui u at hi
  rcases hp.2.2.2.eq_or_lt with hv | hv
  · change v = 0 at hv
    subst v
    have hn : ∀ s ∈ Ioo ui u, 0 ≤ -(S.gamma s 0 * S.varkappa s 0) := by
      intro s hs
      exact h.blueshift_nonneg ⟨hs.1.le, hs.2.trans hp.2.1,
        (hs.2.trans hp.2.1).le, le_rfl⟩ (hs.2.trans hp.2.1)
    have hb : ENNReal.ofReal (∫ s in ui..u, -(S.gamma s 0 * S.varkappa s 0)) ≤
        blueshiftSup ui S := by
      rw [ofReal_intervalIntegral hp.1 hi hn]
      exact (lintegral_mono_set (Ioo_subset_Ioo_right hp.2.1.le)).trans h.terminal_blueshift_le
    exact (ENNReal.ofReal_le_iff_le_toReal h.blueshift_finite.ne).mp hb
  · exact h.partial_blueshift_le hp.1 huv ⟨hp.1.trans_lt huv, hv⟩ hi

/-- The amplitude bound and the lower λ bound control θ/λ.
The amplitude premise is discharged by the mass contradiction.
Paper `e1a0fd5`, lines 524–526. -/
theorem normalized_theta_le_of_theta_bound {T u v : ℝ}
    (hT : ∀ p ∈ pastTriangle ui, p.1 < p.2 → |S.theta p.1 p.2| ≤ T)
    (hp : (u, v) ∈ pastTriangle ui) (huv : u < v) :
    |S.theta u v / S.lam u v| ≤ T / Real.exp (-Bstar ui S) := by
  rw [abs_div, abs_of_pos (h.lam_pos hp)]
  exact div_le_div₀ ((abs_nonneg _).trans (hT (u, v) hp huv)) (hT (u, v) hp huv)
    (Real.exp_pos _) (h.lam_bounds hp).1

/-- The incoming linear-transport integral is bounded by the complete
blueshift times the normalized amplitude bound. Paper `e1a0fd5`,
`eq:scalar-bound-normalized-datum`, lines 526–532. -/
theorem normalized_transport_integral_le_of_theta_bound {T u v : ℝ}
    (hT : ∀ p ∈ pastTriangle ui, p.1 < p.2 → |S.theta p.1 p.2| ≤ T)
    (hp : (u, v) ∈ pastTriangle ui) (huv : u < v) :
    |∫ s in ui..u, -(S.gamma s v * S.varkappa s v) *
      (S.theta s v / S.lam s v)| ≤ Bstar ui S * (T / Real.exp (-Bstar ui S)) := by
  let N := T / Real.exp (-Bstar ui S)
  have hN : 0 ≤ N := by
    have hp' : (ui, 0) ∈ pastTriangle ui :=
      ⟨le_rfl, h.initial_negative, h.initial_negative.le, le_rfl⟩
    exact div_nonneg ((abs_nonneg _).trans (hT (ui, 0) hp' h.initial_negative))
      (Real.exp_pos _).le
  have hs : ∀ s ∈ Icc ui u, (s, v) ∈ pastTriangle ui ∧ s < v := by
    intro s hs
    exact ⟨⟨hs.1, hs.2.trans_lt hp.2.1, (hs.2.trans_lt huv).le, hp.2.2.2⟩,
      hs.2.trans_lt huv⟩
  have hq := h.normalized_datum_primitive_in hp.1 le_rfl hp.2.1 huv hp.2.2.2
  have hb := (h.log_lam_primitive hp.1 le_rfl hp.2.1 huv hp.2.2.2).1.neg
  calc
    _ ≤ ∫ s in ui..u, |-(S.gamma s v * S.varkappa s v) *
        (S.theta s v / S.lam s v)| := intervalIntegral.abs_integral_le_integral_abs hp.1
    _ ≤ ∫ s in ui..u, N * -(S.gamma s v * S.varkappa s v) :=
      intervalIntegral.integral_mono_on hp.1 hq.1.abs (hb.const_mul N) (by
        intro s hsu
        rw [abs_mul, abs_of_nonneg (h.blueshift_nonneg (hs s hsu).1 (hs s hsu).2)]
        exact (mul_le_mul_of_nonneg_left
          (h.normalized_theta_le_of_theta_bound hT (hs s hsu).1 (hs s hsu).2)
          (h.blueshift_nonneg (hs s hsu).1 (hs s hsu).2)).trans_eq (mul_comm _ _))
    _ = N * (∫ s in ui..u, -(S.gamma s v * S.varkappa s v)) :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ N * Bstar ui S := mul_le_mul_of_nonneg_left
      (h.partial_blueshift_le_terminal hp huv) hN
    _ = _ := mul_comm _ _

/-- The paper's normalized-datum estimate, once θ is bounded.
The amplitude premise is discharged by the strip/mass argument.
Paper `e1a0fd5`, `eq:scalar-bound-normalized-datum`, lines 526–532. -/
theorem normalized_datum_le_of_theta_bound {A T u v : ℝ}
    (hA : ∀ s ∈ Icc ui 0, |S.dvpsi ui s| ≤ A)
    (hT : ∀ p ∈ pastTriangle ui, p.1 < p.2 → |S.theta p.1 p.2| ≤ T)
    (hp : (u, v) ∈ pastTriangle ui) (huv : u < v) :
    |S.dvpsi u v / S.lam u v| ≤ A + Bstar ui S * (T / Real.exp (-Bstar ui S)) := by
  have he := (h.normalized_datum_primitive_in hp.1 le_rfl hp.2.1 huv hp.2.2.2).2
  dsimp only at he
  rw [(h.initial_gauge v ⟨hp.1.trans huv.le, hp.2.2.2⟩).2, div_one] at he
  have he' : S.dvpsi u v / S.lam u v = S.dvpsi ui v +
      ∫ s in ui..u, -(S.gamma s v * S.varkappa s v) * (S.theta s v / S.lam s v) := by
    linarith
  rw [he']
  exact (abs_add_le _ _).trans (add_le_add
    (hA v ⟨hp.1.trans huv.le, hp.2.2.2⟩)
    (h.normalized_transport_integral_le_of_theta_bound hT hp huv))

/-- The identity φ = dvψ/λ − θ/λ gives the scalar bound.
Paper `e1a0fd5`, line 534, `eq:normalized-scalar-derivatives`. -/
theorem scalar_le_of_theta_bound {A T u v : ℝ}
    (hA : ∀ s ∈ Icc ui 0, |S.dvpsi ui s| ≤ A)
    (hT : ∀ p ∈ pastTriangle ui, p.1 < p.2 → |S.theta p.1 p.2| ≤ T)
    (hp : (u, v) ∈ pastTriangle ui) (huv : u < v) :
    |S.phi u v| ≤ A + (Bstar ui S + 1) * (T / Real.exp (-Bstar ui S)) := by
  have he : S.phi u v = S.dvpsi u v / S.lam u v - S.theta u v / S.lam u v := by
    unfold SSFields.theta
    field_simp [(h.lam_pos hp).ne']
    ring
  rw [he]
  exact (abs_sub _ _).trans (by linarith
    [h.normalized_datum_le_of_theta_bound hA hT hp huv,
      h.normalized_theta_le_of_theta_bound hT hp huv])

end AcExtensionPrinciple.StandingFull

end
