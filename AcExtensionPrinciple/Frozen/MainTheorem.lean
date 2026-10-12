-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import AcExtensionPrinciple.Frozen.MainTheoremStatement
public import AcExtensionPrinciple.Main.Theorem1Proof

/-!
# Frozen anchor `mainTheorem_v1`

Theorem 1 of the paper (`thm:main`), approval package v1.4 (paper `203e554`, lines 112–146), with
the author's rulings Q1–Q3, Q5–Q8 and Q10. Certified claim: Theorem 1 assuming the external inputs
E1 (`SmallBVExistence`) and E2 (`BVUniqueness`), which are hypotheses of `MainTheoremStatement`, not
axioms. Manifest entry `mainTheorem_v1` in `planning/frozen-anchors.json`. Only the proof body
between the proof markers may change: the draft `by sorry` is replaced by the seal
`by exact AcExtensionPrinciple.mainTheoremProof`.
-/

public section

namespace AcExtensionPrinciple

/-- Theorem 1 of the paper (`thm:main`), in the form `MainTheoremStatement`: under E1 and E2, every
solution satisfying the standing assumptions admits a continuation in Christodoulou's BV class
across (0,0) in the original chart and has finite terminal variation of ∂ᵤψ/ν, φ, log(−ν), ν and ∂ᵤψ
on [u_i, 0). Proof: `mainTheoremProof` (`Main/Theorem1Proof.lean`; paper Section 4, lines
1384–1439). -/
theorem mainTheorem : MainTheoremStatement :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact AcExtensionPrinciple.mainTheoremProof
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end AcExtensionPrinciple

end
-- FROZEN_ANCHOR_SUFFIX_END
