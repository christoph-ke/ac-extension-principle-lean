module

public import AcExtensionPrinciple.Minimal.LambdaAC

/-!
# Complete simultaneous restoration of the additional fields of the full working class
Paper `e1a0fd5`, `equations.tex` lines 114–132 and 220–261.
The input omits every requested field simultaneously. All restorations
follow the order r, m, φ continuity, joint normalized scalar traces, scalar AC,
λ continuity, conventions, λ AC. The source scalar traces are one-sided.
-/

public section

namespace AcExtensionPrinciple

/-- Restore the full standing class from the simultaneous minimal class.
No deleted field or joint normalized trace is an input. Paper `e1a0fd5`,
`thm:main`, lines 114–132 and 220–261. -/
theorem StandingAssumptions.toFull {ui : ℝ} {S : SSFields}
    (h : StandingAssumptions ui S) : StandingFull ui S := by
  let e := h.toExpansionDraft
  let rest : StandingWithout_ac_lam_out ui S := {
    toQ1StandingCore := e.toQ1StandingCore
    continuous_r := e.continuous_r
    continuous_m := e.continuous_m
    continuous_lam := e.continuous_lam
    continuous_nu := e.continuous_nu
    continuous_phi := e.continuous_phi
    lam_right_cont := e.lam_right_cont
    nu_right_cont := e.nu_right_cont
    dvpsi_right_cont := e.dvpsi_right_cont
    dupsi_right_cont := e.dupsi_right_cont
  }
  exact rest.restore e.ac_lam_out

end AcExtensionPrinciple

end
