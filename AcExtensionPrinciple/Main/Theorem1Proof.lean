module

public import AcExtensionPrinciple.Integration.MainFromEnergy
public import AcExtensionPrinciple.Weighted.Prop34

/-!
# Proof of Theorem 1 (provider for the frozen anchor `mainTheorem_v1`)

Paper `e1a0fd5`, `thm:main` (lines 112–146), proof in Section 4 (lines 1390–1445).
-/

public section

namespace AcExtensionPrinciple

/-- Theorem 1 of the paper (`thm:main`), in the form `MainTheoremStatement`: under E1 and E2, every solution satisfying
the standing assumptions admits a continuation in Christodoulou's BV class across (0,0) in the original chart and has
finite terminal variation of ∂ᵤψ/ν, φ, log(−ν), ν and ∂ᵤψ on [u_i, 0). Assembled from the energy finiteness of
Prop 3.4 (`StandingFull.proposition34`) and `main_statement_of_energy`. -/
theorem mainTheoremProof : MainTheoremStatement :=
  main_statement_of_energy fun _ _ h => h.proposition34

end AcExtensionPrinciple

end
