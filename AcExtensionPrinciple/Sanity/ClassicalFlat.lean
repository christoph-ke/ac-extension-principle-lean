module

public import AcExtensionPrinciple.Sanity.Classical
public import AcExtensionPrinciple.Sanity.FlatStanding
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Flat-space consistency of the classical structure
Paper `e1a0fd5`, lines 49–106, `eq:regular-axis`, `eq:initial-radius-gauge`;
Christodoulou CPAM p. 1157. The scalar constant is arbitrary.
-/

public section

namespace AcExtensionPrinciple

open Set

/-- Flat space in the initial gauge is a classical solution with a regular apex. Paper `e1a0fd5`,
lines 49–106, 112–132, 220–275; Christodoulou CPAM p. 1157. -/
theorem flat_classical (ui c : ℝ) (hui : ui < 0) :
    ClassicalTriangleSolution ui (flat c) := by
  have hsrc := fun u v => scaledFlat_sources 1 c u v
  constructor
  · exact hui
  · simpa [flat, scaledFlat] using
      (contDiff_snd.sub contDiff_fst : ContDiff ℝ 1 (fun p : ℝ × ℝ => p.2 - p.1)).contDiffOn
  · exact contDiff_const.contDiffOn
  · exact contDiff_const.contDiffOn
  · exact contDiff_const.contDiffOn
  · exact contDiff_const.contDiffOn
  · exact contDiff_const.contDiffOn
  · exact contDiff_const.contDiffOn
  · intro u v _ _ _
    simpa [flat, scaledFlat] using (hasDerivAt_id v).sub_const u
  · intro u v _ _ _
    simpa [flat, scaledFlat] using (hasDerivAt_const u v).fun_sub (hasDerivAt_id u)
  · intro u v _ _ _
    simpa [flat, scaledFlat] using ((hasDerivAt_id v).sub_const u).mul_const c
  · intro u v _ _ _
    simpa [flat, scaledFlat] using
      ((hasDerivAt_const u v).sub (hasDerivAt_id u)).mul_const c
  · intro u v _ _ _
    rw [show (flat c).massV u v = 0 from (hsrc u v).2.2.2.2.1]
    exact hasDerivAt_const v 0
  · intro u v _ _ _
    rw [show (flat c).massU u v = 0 from (hsrc u v).2.2.2.2.2]
    exact hasDerivAt_const u 0
  · intro u v _ _ _
    rw [show (flat c).radiusCoeff u v = 0 from (hsrc u v).2.2.2.1]
    exact hasDerivAt_const u 1
  · intro u v _ _ _
    rw [show (flat c).radiusCoeff u v = 0 from (hsrc u v).2.2.2.1]
    exact hasDerivAt_const v (-1)
  · intro u v _ _ _
    rw [show (flat c).radiusCoeff u v = 0 from (hsrc u v).2.2.2.1, zero_mul]
    exact hasDerivAt_const u (1 * c)
  · intro u v _ _ _
    rw [show (flat c).radiusCoeff u v = 0 from (hsrc u v).2.2.2.1, zero_mul]
    exact hasDerivAt_const v (-1 * c)
  · intro a _ _
    simp [flat, scaledFlat]
  · intro p _
    norm_num [flat, scaledFlat]
  · intro p _ _
    norm_num [flat, scaledFlat, SSFields.mu, massRatio]
  · intro v _
    simp [flat, scaledFlat]

end AcExtensionPrinciple

end
