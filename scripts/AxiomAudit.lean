import AcExtensionPrinciple

/-!
# Axiom audit

Run with `lake env lean scripts/AxiomAudit.lean` after `lake build`. Expected output for both declarations:
`[propext, Classical.choice, Quot.sound]` (the three standard axioms of Lean and Mathlib). The external inputs E1 and
E2 are hypotheses of `MainTheoremStatement`, not axioms, so they do not appear here.
-/

#print axioms AcExtensionPrinciple.mainTheorem
#print axioms AcExtensionPrinciple.mainTheoremProof
#check @AcExtensionPrinciple.mainTheorem
