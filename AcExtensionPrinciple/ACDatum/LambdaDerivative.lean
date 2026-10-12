module

public import AcExtensionPrinciple.ACDatum.OutgoingCalculus

/-!
# Outgoing differentiation of the incoming expansion factor

Paper `e1a0fd5`, `equations.tex` lines 422–426 and 594–601.
The initial gauge and the logarithmic incoming equation express λ as an
exponential of an integral whose outgoing derivative is continuous.
-/

public section

namespace AcExtensionPrinciple

open Set Filter MeasureTheory
open scoped Topology

/-- The outgoing derivative of λ obtained from its incoming integrating
factor. Paper `e1a0fd5`, lines 422–426 and 596–601. -/
@[expose] noncomputable def lambdaOutgoingDerivative
    (ui : ℝ) (S : SSFields) (u v : ℝ) : ℝ :=
  S.lam u v * ∫ s in ui..u, outgoingDatumCoeffDerivative S s v

namespace StandingFull

variable {ui : ℝ} {S : SSFields} (h : StandingFull ui S)
include h

/-- Exact exponential incoming representation of λ.
Paper `e1a0fd5`, `eq:lambda-integrating-factor`, lines 311–316. -/
theorem lam_eq_exp_integral {u v : ℝ} (hu : ui ≤ u) (hu0 : u < 0)
    (huv : u < v) (hv0 : v ≤ 0) :
    S.lam u v = Real.exp (∫ s in ui..u, incomingDatumCoeff S s v) := by
  have he := (h.log_lam_primitive hu le_rfl hu0 huv hv0).2
  dsimp only at he
  rw [(h.initial_gauge v ⟨(hu.trans_lt huv).le, hv0⟩).2, Real.log_one, sub_zero] at he
  dsimp only [incomingDatumCoeff]
  rw [← he]
  exact (Real.exp_log (h.lam_pos (p := (u, v)) ⟨hu, hu0, huv.le, hv0⟩)).symm

/-- Pointwise outgoing derivative of λ away from coordinate endpoints.
Paper `e1a0fd5`, lines 422–426 and 596–601. -/
theorem lam_hasDerivAt_out {u v : ℝ} (hu : ui ≤ u) (hu0 : u < 0)
    (huv : u < v) (hv : v < 0) :
    HasDerivAt (S.lam u) (lambdaOutgoingDerivative ui S u v) v := by
  obtain ⟨a, b, hua, hav, hvb, hb⟩ := exists_proper_outgoing_neighborhood huv hv
  have hi := rectangle_integral_hasDerivAt ⟨hu, le_rfl⟩ ⟨hav, hvb⟩
    (h.incomingDatumCoeff_continuous_rectangle hu0 hua hb.le)
    (h.outgoingDatumCoeffDerivative_continuous_rectangle hu (hav.le.trans hvb.le) hu0 hua hb.le)
    (fun s hs x hx => h.incomingDatumCoeff_hasDerivAt_out hs.1 (hs.2.trans_lt hu0)
      (hs.2.trans_lt (hua.trans hx.1)) (hx.2.trans hb))
  have he : (fun x => Real.exp (∫ s in ui..u, incomingDatumCoeff S s x)) =ᶠ[𝓝 v] S.lam u := by
    filter_upwards [Ioo_mem_nhds hav hvb] with x hx
    exact (h.lam_eq_exp_integral hu hu0 (hua.trans hx.1) (hx.2.trans hb).le).symm
  convert hi.exp.congr_of_eventuallyEq he.symm using 1
  rw [← h.lam_eq_exp_integral hu hu0 huv hv.le]
  rfl

/-- Joint continuity of the outgoing λ derivative on proper rectangles.
Paper `e1a0fd5`, lines 596–601. -/
theorem lambdaOutgoingDerivative_continuous_rectangle {U a b : ℝ}
    (hui : ui ≤ U) (hab : a ≤ b) (hU : U < 0) (hUa : U < a) (hb : b ≤ 0) :
    ContinuousOn (fun p : ℝ × ℝ => lambdaOutgoingDerivative ui S p.1 p.2)
      (Icc ui U ×ˢ Icc a b) :=
  (h.regularCenter.continuous_lam.mono (properRectangle_subset_triangle (ui := ui) hU hUa hb)).mul
    (rectangle_integral_continuous hui hab
      (h.outgoingDatumCoeffDerivative_continuous_rectangle hui hab hU hUa hb))

end StandingFull

end AcExtensionPrinciple

end
